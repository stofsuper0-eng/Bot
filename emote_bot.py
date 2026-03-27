import asyncio
import random
import re
import time
import json
import os
import traceback
import datetime

from highrise import BaseBot, Position
from highrise.models import SessionMetadata, User
from emotes import EMOTE_DICT


# ── PERSISTENCE ──────────────────────────────────────────────────────
_BASE_DIR      = os.path.dirname(os.path.abspath(__file__))
DATA_FILE      = os.path.join(_BASE_DIR, "emotebot_data.json")
CRASH_LOG_FILE = os.path.join(_BASE_DIR, "emotebot_crash_log.json")


def load_data() -> dict:
    if os.path.exists(DATA_FILE):
        try:
            with open(DATA_FILE, "r", encoding="utf-8") as f:
                return json.load(f)
        except Exception as e:
            print(f"[Persistence] Could not load {DATA_FILE}: {e}")
    return {}


def save_data(data: dict):
    try:
        tmp = DATA_FILE + ".tmp"
        with open(tmp, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2, ensure_ascii=False)
        os.replace(tmp, DATA_FILE)
    except Exception as e:
        print(f"[Persistence] Could not save {DATA_FILE}: {e}")


def log_crash(location: str, error: Exception, extra: str = ""):
    """Append crash info to crash_log.json for debugging."""
    try:
        entry = {
            "time":     datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S"),
            "location": location,
            "error":    str(error),
            "type":     type(error).__name__,
            "trace":    traceback.format_exc(),
            "extra":    extra,
        }
        existing = []
        if os.path.exists(CRASH_LOG_FILE):
            try:
                with open(CRASH_LOG_FILE, "r") as f:
                    existing = json.load(f)
            except Exception:
                existing = []
        existing.append(entry)
        existing = existing[-50:]  # keep last 50 only
        with open(CRASH_LOG_FILE, "w") as f:
            json.dump(existing, f, indent=2)
    except OSError as le:
        print(f"[CrashLog] Skipping log (disk/OS error): {le}")
    except Exception as le:
        print(f"[CrashLog] Failed to write crash log: {le}")


# ─────────────────────────────────────────────────────────────────────
#  BOT
# ─────────────────────────────────────────────────────────────────────
class EmoteBot(BaseBot):

    def __init__(self):
        super().__init__()

        # ── Owners ───────────────────────────────────────────────────
        self.owner_username        = "Highrisemaroc"
        self.second_owner_username = "st0f"

        # ── Connection state ─────────────────────────────────────────
        self.is_connected      = False
        self._room_cache: list = []
        self._room_cache_time  = 0.0
        self._api_semaphore    = None   # set in on_start

        # ── Rate-limited queues ───────────────────────────────────────
        self._chat_queue    = asyncio.Queue(maxsize=300)
        self._whisper_queue = asyncio.Queue(maxsize=500)

        # ── Emote data ───────────────────────────────────────────────
        self.emote_dict       = EMOTE_DICT
        self.emote_keys       = list(self.emote_dict.keys())
        self._emote_lower_map = {k.lower(): k for k in self.emote_dict}
        self._emote_nospace_map = {k.lower().replace(" ", ""): k for k in self.emote_dict}

        # ── Per-user emote loops ──────────────────────────────────────
        self.looping_users          = {}  # user_id -> bool
        self._loop_tasks            = {}  # user_id -> asyncio.Task
        self.user_loop_emotes       = {}  # user_id -> (emote_id, duration) — persisted
        self._loop_notinroom_count  = {}  # user_id -> consecutive "not in room" count
        self._loop_error_count      = {}  # user_id -> consecutive error count

        # ── Bot's own emote loop ──────────────────────────────────────
        self.bot_emote_id   = None  # no emote by default; use !botemote N to set
        self.bot_emote_task = None

        # ── Dance floor ───────────────────────────────────────────────
        self.dance_floor            = None   # {'x','y','z','rx','ry','rz'}
        self.users_dancing_on_floor = {}     # user_id -> bool (False=pending, True=active)
        self.dance_beat_start       = 0.0
        self.dance_beat_cycle       = 12.0
        self.dance_floor_emote      = None
        self._floor_beat_errors     = {}     # user_id -> last error timestamp
        self._floor_setup_step      = 0      # 0=idle 1=waiting point1 2=waiting point2
        self._floor_setup_p1        = None

        # ── Cooldowns ─────────────────────────────────────────────────
        self.user_cooldowns = {}
        self.cooldown_seconds = 2

        # ── Follow system ─────────────────────────────────────────────
        self.follow_target_id   = None   # user_id the bot is following
        self.follow_target_name = None
        self._follow_task       = None
        self._emote_react_times = {}

        # ── Bot saved position (for !setpos / keep_alive) ─────────────
        self.bot_pos = None   # {'x','y','z','facing'} — persisted

        # ── Task handles ─────────────────────────────────────────────
        self._task_chat_worker    = None
        self._task_whisper_worker = None
        self._task_room_cache     = None
        self._task_dance_beat     = None
        self._task_floor_monitor  = None
        self._task_auto_save      = None
        self._task_keep_alive     = None
        self._task_health_check   = None  # NEW: health monitoring
        self._last_save           = 0.0   # debounce: max once per 90s

        # ── Load persisted data ───────────────────────────────────────
        saved = load_data()
        self.dance_floor    = saved.get("dance_floor", None)
        self.bot_emote_id   = saved.get("bot_emote_id") or None
        self.bot_pos        = saved.get("bot_pos", {'x': 7.5, 'y': 0.0, 'z': 0.5, 'facing': 'FrontRight'})
        _saved_loops        = saved.get("user_loop_emotes", {})
        self.user_loop_emotes = {uid: tuple(v) for uid, v in _saved_loops.items()}
        print("[Persistence] Data loaded from disk")

    # ─────────────────────────────────────────────────────────────────
    #  HEALTH CHECK — Monitor for cascading failures
    # ─────────────────────────────────────────────────────────────────
    async def health_check_loop(self):
        """Monitor bot health and detect cascading failures."""
        try:
            while self.is_connected:
                await asyncio.sleep(30)  # Check every 30 seconds
                
                active_loops = len(self.looping_users)
                queue_size = self._chat_queue.qsize()
                error_count = sum(self._loop_error_count.values())
                
                # Log diagnostics
                if active_loops > 0 or queue_size > 50 or error_count > 0:
                    print(f"[Health] Loops: {active_loops}, ChatQ: {queue_size}, Errors: {error_count}")
                
                # Warn on potential issues
                if active_loops > 30:
                    print(f"[Health] ⚠️  WARNING: {active_loops} active loops (potential leak)")
                
                if queue_size > 250:
                    print(f"[Health] ⚠️  WARNING: Chat queue at {queue_size}/300")
                
        except asyncio.CancelledError:
            pass
        except Exception as e:
            print(f"[Health] Monitor error: {e}")

    # ─────────────────────────────────────────────────────────────────
    #  PROTECTED LOOP WRAPPER — Prevent task crashes
    # ─────────────────────────────────────────────────────────────────
    async def _protected_loop_wrapper(self, user_id: str, loop_coro):
        """
        Wraps a loop coroutine to catch all exceptions and prevent task crash.
        Always cleans up even if the loop fails.
        """
        try:
            await loop_coro
        except asyncio.CancelledError:
            print(f"[Loop] Task cancelled for user {user_id}")
        except Exception as e:
            print(f"[Loop] ⚠️ Task crashed for user {user_id}: {e}")
            log_crash("loop_wrapper", e, f"user_id={user_id}")
        finally:
            # Always clean up
            self.looping_users.pop(user_id, None)
            self._loop_tasks.pop(user_id, None)
            self._loop_error_count.pop(user_id, None)
            self._loop_notinroom_count.pop(user_id, None)
            print(f"[Loop] Cleaned up task for user {user_id}")

    # ─────────────────────────────────────────────────────────────────
    #  HELPERS — owner check, chat/whisper queues, room cache
    # ─────────────────────────────────────────────────────────────────
    def is_owner(self, user: User) -> bool:
        return (user.username.lower() == self.owner_username.lower() or
                user.username.lower() == self.second_owner_username.lower())

    _MAX_CHAT_LEN = 250

    def _split_msg(self, msg: str) -> list:
        """Split long messages into ≤250-char chunks on newlines or spaces."""
        if len(msg) <= self._MAX_CHAT_LEN:
            return [msg]
        parts, current = [], ""
        for line in msg.split("\n"):
            if len(current) + len(line) + 1 <= self._MAX_CHAT_LEN:
                current = (current + "\n" + line).lstrip("\n")
            else:
                if current:
                    parts.append(current)
                current = line
        if current:
            parts.append(current)
        return parts or [msg[:self._MAX_CHAT_LEN]]

    def _chat(self, msg: str):
        for part in self._split_msg(msg):
            if not part.strip():
                continue
            try:
                self._chat_queue.put_nowait(part)
            except asyncio.QueueFull:
                print(f"[Chat] Queue full — dropping: {part[:60]}")

    def _whisper(self, user_id: str, text: str):
        try:
            self._whisper_queue.put_nowait((user_id, text))
        except asyncio.QueueFull:
            print(f"[Whisper] Queue full — dropping to {user_id}")

    async def safe_get_room_users(self):
        return list(self._room_cache)

    # ─────────────────────────────────────────────────────────────────
    #  PERSISTENCE
    # ─────────────────────────────────────────────────────────────────
    def _persist(self):
        now = time.time()
        if now - self._last_save < 90:
            return
        self._last_save = now
        print("[Persistence] Auto-saving...")
        save_data({
            "dance_floor":      self.dance_floor,
            "bot_emote_id":     self.bot_emote_id,
            "bot_pos":          self.bot_pos,
            "user_loop_emotes": self.user_loop_emotes,
        })

    # ─────────────────────────────────────────────────────────────────
    #  LOOP MANAGEMENT
    # ─────────────────────────────────────────────────────────────────
    def _start_loop(self, user_id: str, loop_coro):
        """Start a protected emote loop for a user."""
        if user_id in self._loop_tasks:
            return
        
        # Initialize error tracking
        self._loop_error_count[user_id] = 0
        self._loop_notinroom_count[user_id] = 0
        
        # Wrap the loop in protection
        task = asyncio.create_task(
            self._protected_loop_wrapper(user_id, loop_coro)
        )
        self._loop_tasks[user_id] = task
        self.looping_users[user_id] = True
        print(f"[Loop] Started loop for user {user_id}")

    def _stop_loop(self, user_id: str):
        """Stop an emote loop for a user."""
        if user_id in self._loop_tasks:
            task = self._loop_tasks[user_id]
            if not task.done():
                task.cancel()
        self.looping_users.pop(user_id, None)
        print(f"[Loop] Stopped loop for user {user_id}")

    # ─────────────────────────────────────────────────────────────────
    #  EMOTE LOOPS WITH PROTECTION
    # ─────────────────────────────────────────────────────────────────
    async def loop_emote(self, user_id: str, emote_id: str, duration: float):
        """
        Loop an emote for a user.
        - Checks connection status
        - Handles permission errors gracefully
        - Stops after 3 consecutive errors
        - Resets error count on success
        """
        MAX_ERRORS = 3
        
        while user_id in self.looping_users and self.is_connected:
            try:
                # Double-check connection before sending
                if not self.is_connected:
                    print(f"[Loop] {user_id} stopping: bot disconnected")
                    break
                
                # Send emote with timeout
                await asyncio.wait_for(
                    self.highrise.send_emote(emote_id, user_id),
                    timeout=5.0
                )
                
                # Reset error count on success
                self._loop_error_count[user_id] = 0
                
            except asyncio.CancelledError:
                break
            except asyncio.TimeoutError:
                self._loop_error_count[user_id] = self._loop_error_count.get(user_id, 0) + 1
                if self._loop_error_count[user_id] >= MAX_ERRORS:
                    print(f"[Loop] {user_id} stopping: timeout after {MAX_ERRORS} attempts")
                    break
                print(f"[Loop] {user_id} timeout (attempt {self._loop_error_count[user_id]})")
            except Exception as e:
                error_str = str(e).lower()
                
                # Permanent errors — stop immediately
                if "not free" in error_str or "not owned" in error_str:
                    print(f"[Loop] {user_id} stopping: emote permission denied")
                    break
                
                # Connection errors — count and potentially stop
                if "not connected" in error_str or "closing" in error_str or "websocket" in error_str:
                    print(f"[Loop] {user_id} connection issue: {e}")
                    break
                
                # Other errors — count them
                self._loop_error_count[user_id] = self._loop_error_count.get(user_id, 0) + 1
                if self._loop_error_count[user_id] >= MAX_ERRORS:
                    print(f"[Loop] {user_id} stopping: {MAX_ERRORS} errors ({type(e).__name__})")
                    break
                
                print(f"[Loop] {user_id} error (attempt {self._loop_error_count[user_id]}): {e}")
            
            try:
                await asyncio.sleep(duration)
            except asyncio.CancelledError:
                break

    async def loop_random_emote(self, user_id: str):
        """Loop random emotes continuously."""
        while user_id in self.looping_users and self.is_connected:
            try:
                if not self.is_connected:
                    break
                
                emote_name = random.choice(self.emote_keys)
                emote_data = self.emote_dict[emote_name]
                emote_id = emote_data[0]
                duration = float(emote_data[1])
                
                await asyncio.wait_for(
                    self.highrise.send_emote(emote_id, user_id),
                    timeout=5.0
                )
                
                # Reset error count on success
                self._loop_error_count[user_id] = 0
                
            except asyncio.CancelledError:
                break
            except asyncio.TimeoutError:
                self._loop_error_count[user_id] = self._loop_error_count.get(user_id, 0) + 1
                if self._loop_error_count[user_id] >= 3:
                    break
            except Exception as e:
                error_str = str(e).lower()
                if "not free" in error_str or "not owned" in error_str:
                    break
                self._loop_error_count[user_id] = self._loop_error_count.get(user_id, 0) + 1
                if self._loop_error_count[user_id] >= 3:
                    break
            
            try:
                await asyncio.sleep(1)
            except asyncio.CancelledError:
                break

    # ─────────────────────────────────────────────────────────────────
    #  EVENT HANDLERS
    # ─────────────────────────────────────────────────────────────────
    async def on_start(self, session_metadata: SessionMetadata) -> None:
        """Called when bot connects."""
        self.is_connected = True
        print("[Start] Bot online!")
        
        # Create semaphore for rate limiting
        self._api_semaphore = asyncio.Semaphore(5)
        
        # Start background tasks
        self._task_chat_worker = self.create_task(self._chat_worker())
        self._task_whisper_worker = self.create_task(self._whisper_worker())
        self._task_room_cache = self.create_task(self._room_cache_updater())
        self._task_auto_save = self.create_task(self._auto_save_loop())
        self._task_health_check = self.create_task(self.health_check_loop())  # NEW
        
        # Restore user loops from disk
        for user_id, (emote_id, duration) in self.user_loop_emotes.items():
            self._start_loop(user_id, self.loop_emote(user_id, emote_id, duration))
            print(f"[Start] Restored loop for user {user_id}")

    async def on_chat(self, user: User, message: str):
        """Handle chat messages — CRITICAL: wrapped for crash protection."""
        try:
            if user.id == self.highrise.my_id:
                return

            msg = message.strip()
            low = msg.lower()

            # ── Owner commands in public chat ─────────────────────────
            if self.is_owner(user):
                # (Owner command handling code would go here)
                pass

            # ── Cooldown check (2s between commands) ──────────────────
            now  = time.time()
            last = self.user_cooldowns.get(user.id, 0)
            if now - last < self.cooldown_seconds:
                return
            self.user_cooldowns[user.id] = now

            # ── Help ──────────────────────────────────────────────────
            if low == '!help':
                self._chat(
                    f"🎭 EMOTE BOT COMMANDS\n"
                    f"1-{len(self.emote_keys)} — play emote by number\n"
                    "loop N — loop emote by number\n"
                    "[name] — play emote by name\n"
                    "loop [name] — loop emote by name\n"
                    "random — loop random emotes\n"
                    "stop / 0 — stop your loop\n"
                    "!dancefloor — teleport to dance floor"
                )
                return

            # ── Teleport to dance floor ────────────────────────────────
            if low == '!dancefloor':
                if self.dance_floor:
                    await self.highrise.teleport(
                        user.id,
                        Position(self.dance_floor['x'], self.dance_floor['y'], self.dance_floor['z'])
                    )
                    self._chat(f"🕺 @{user.username} → dance floor!")
                else:
                    self._chat("Dance floor not set yet!")
                return

            # ── Stop loop ──────────────────────────────────────────────
            if low in ('stop', '0'):
                self._stop_loop(user.id)
                self.user_loop_emotes.pop(user.id, None)
                self._chat(f"🛑 @{user.username} stopped.")
                return

            # ── Random emote loop ──────────────────────────────────────
            if low == 'random':
                if user.id in self.looping_users:
                    self._chat(f"⚠️ @{user.username} already looping! Type 'stop' first.")
                    return
                self._chat(f"🎲 @{user.username} random loop! Type 'stop' to stop 🛑")
                self._start_loop(user.id, self.loop_random_emote(user.id))
                return

            # ── Emote by number (loop N or just N) ────────────────────
            loop_match   = re.fullmatch(r"loop\s+(\d+)", low)
            number_match = re.fullmatch(r"(\d+)", low)

            if loop_match or number_match:
                is_loop = bool(loop_match)
                index   = int(loop_match.group(1) if loop_match else number_match.group(1)) - 1
                if 0 <= index < len(self.emote_keys):
                    emote_name = self.emote_keys[index]
                    emote_data = self.emote_dict[emote_name]
                    emote_id   = emote_data[0]
                    duration   = float(emote_data[1])
                    if is_loop:
                        if user.id in self.looping_users:
                            self._chat(f"⚠️ @{user.username} already looping! Type 'stop' first.")
                            return
                        self._chat(f"🔄 @{user.username} looping #{index+1}: {emote_name}")
                        self.user_loop_emotes[user.id] = (emote_id, duration)
                        self._start_loop(user.id, self.loop_emote(user.id, emote_id, duration))
                        self._persist()
                    else:
                        # ✅ FIXED: Protected emote send
                        try:
                            await asyncio.wait_for(
                                self.highrise.send_emote(emote_id, user.id),
                                timeout=5.0
                            )
                        except asyncio.TimeoutError:
                            print(f"[Emote] Timeout sending emote {emote_id} to {user.id}")
                        except Exception as e:
                            error_str = str(e).lower()
                            
                            # Handle different error types
                            if "not free" in error_str or "not owned" in error_str:
                                self._chat(f"❌ @{user.username} this emote is locked or not yours!")
                                print(f"[Emote] Permission denied: {e}")
                            elif "not connected" in error_str or "closing" in error_str:
                                print(f"[Emote] Connection issue: {e}")
                            else:
                                print(f"[Emote] Error: {e}")
                                log_crash("send_emote", e, f"emote_id={emote_id}")
                else:
                    self._chat(f"❌ Pick 1-{len(self.emote_keys)}")
                return

            # ── Emote by name (loop [name] or just [name]) ─────────────
            name_loop_match = re.fullmatch(r"loop\s+(.+)", low)
            is_name_loop    = bool(name_loop_match)
            emote_query     = name_loop_match.group(1).strip() if is_name_loop else low.strip()

            matched_key = self._emote_lower_map.get(emote_query)
            if not matched_key:
                matched_key = self._emote_nospace_map.get(emote_query.replace(" ", ""))

            if matched_key:
                emote_data = self.emote_dict[matched_key]
                emote_id   = emote_data[0]
                duration   = float(emote_data[1])
                if is_name_loop:
                    if user.id in self.looping_users:
                        self._chat(f"⚠️ @{user.username} already looping! Type 'stop' first.")
                        return
                    self._chat(f"🔄 @{user.username} looping: {matched_key}")
                    self.user_loop_emotes[user.id] = (emote_id, duration)
                    self._start_loop(user.id, self.loop_emote(user.id, emote_id, duration))
                    self._persist()
                else:
                    # ✅ FIXED: Protected emote send
                    try:
                        await asyncio.wait_for(
                            self.highrise.send_emote(emote_id, user.id),
                            timeout=5.0
                        )
                    except asyncio.TimeoutError:
                        print(f"[Emote] Timeout sending emote {emote_id} to {user.id}")
                    except Exception as e:
                        error_str = str(e).lower()
                        if "not free" in error_str or "not owned" in error_str:
                            self._chat(f"❌ @{user.username} this emote is locked!")
                            print(f"[Emote] Permission denied: {e}")
                        elif "not connected" in error_str or "closing" in error_str:
                            print(f"[Emote] Connection issue: {e}")
                        else:
                            print(f"[Emote] Error: {e}")
                            log_crash("send_emote", e, f"emote_id={emote_id}")

        except Exception as e:
            log_crash("on_chat", e, f"msg={message[:80]}")
            print(f"[Chat] Error: {e}")

    async def _chat_worker(self):
        """Worker to send queued chat messages with rate limiting."""
        try:
            while self.is_connected:
                try:
                    msg = await asyncio.wait_for(self._chat_queue.get(), timeout=5.0)
                except asyncio.TimeoutError:
                    continue
                
                if not self.is_connected:
                    self._chat_queue.task_done()
                    continue
                
                try:
                    await self.highrise.chat(msg)
                    await asyncio.sleep(0.3)  # Rate limit
                except Exception as e:
                    error_str = str(e).lower()
                    if "closing" not in error_str and "not connected" not in error_str:
                        print(f"[Chat Worker] Error: {e}")
                finally:
                    self._chat_queue.task_done()
        except asyncio.CancelledError:
            pass

    async def _whisper_worker(self):
        """Worker to send queued whispers with rate limiting."""
        try:
            while self.is_connected:
                try:
                    user_id, text = await asyncio.wait_for(self._whisper_queue.get(), timeout=5.0)
                except asyncio.TimeoutError:
                    continue
                
                if not self.is_connected:
                    self._whisper_queue.task_done()
                    continue
                
                try:
                    await self.highrise.whisper(user_id, text)
                    await asyncio.sleep(0.3)  # Rate limit
                except Exception as e:
                    error_str = str(e).lower()
                    if "closing" not in error_str and "not connected" not in error_str:
                        print(f"[Whisper Worker] Error: {e}")
                finally:
                    self._whisper_queue.task_done()
        except asyncio.CancelledError:
            pass

    async def _room_cache_updater(self):
        """Update room cache periodically."""
        try:
            while self.is_connected:
                try:
                    room = await self.highrise.get_room()
                    self._room_cache = list(room.users.items()) if hasattr(room, 'users') else []
                    self._room_cache_time = time.time()
                except Exception as e:
                    print(f"[RoomCache] Update error: {e}")
                
                await asyncio.sleep(5)
        except asyncio.CancelledError:
            pass

    async def _auto_save_loop(self):
        """Auto-save every 90 seconds if data changed."""
        try:
            while self.is_connected:
                await asyncio.sleep(90)
                self._persist()
        except asyncio.CancelledError:
            pass

    async def on_disconnect(self) -> None:
        """Called when bot disconnects."""
        self.is_connected = False
        self._room_cache = []
        print("[DISCONNECT] Bot disconnected")


# ── ENTRY POINT ──────────────────────────────────────────────────────
import subprocess
import sys
import signal as _signal

if __name__ == "__main__":
    import time as _time

    _HR_ROOM_ID   = os.environ.get("HR_ROOM_ID",   "673a9012dcd373b903936bad")
    _HR_API_TOKEN = os.environ.get("HR_API_TOKEN", "")

    if not _HR_API_TOKEN:
        print(
            "[Main] WARNING: HR_API_TOKEN not set!\n"
            "[Main] Set it via: export HR_API_TOKEN='your_token_here'"
        )

    _child_proc = None

    def _forward_signal(signum, frame):
        if _child_proc and _child_proc.poll() is None:
            try:
                _child_proc.send_signal(signum)
            except Exception:
                pass

    _signal.signal(_signal.SIGTERM, _forward_signal)
    _signal.signal(_signal.SIGINT,  _forward_signal)

    _retry = 0
    while True:
        _start      = _time.time()
        _child_proc = subprocess.Popen([
            sys.executable, "-m", "highrise",
            "emote_bot:EmoteBot",
            _HR_ROOM_ID,
            _HR_API_TOKEN,
        ])
        returncode  = _child_proc.wait()
        _child_proc = None
        _uptime     = _time.time() - _start
        if _uptime > 60:
            _retry = 0
        _retry += 1
        if returncode in (-_signal.SIGTERM, -_signal.SIGINT):
            print("[Main] Shutdown signal — exiting.")
            break
        wait = 3 if returncode == 0 else (5 if _uptime > 10 else min(10 * _retry, 30))
        print(f"[Main] Exited (code {returncode}, uptime {_uptime:.0f}s) retry #{_retry} in {wait}s...")
        _time.sleep(wait)
