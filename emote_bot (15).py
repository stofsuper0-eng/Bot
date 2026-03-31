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
        existing = existing[-50:]
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
        self._api_semaphore    = None   # set in on_start — CRITICAL: controls concurrency
        self._tasks            = set()

        # ── Rate-limited queues ───────────────────────────────────────
        self._chat_queue    = asyncio.Queue(maxsize=300)
        self._whisper_queue = asyncio.Queue(maxsize=500)

        # ── Emote data ───────────────────────────────────────────────
        self.emote_dict       = EMOTE_DICT
        self.emote_keys       = list(self.emote_dict.keys())
        self._emote_lower_map = {k.lower(): k for k in self.emote_dict}
        self._emote_nospace_map = {k.lower().replace(" ", ""): k for k in self.emote_dict}

        # ── Per-user emote loops ──────────────────────────────────────
        self.looping_users          = {}
        self._loop_tasks            = {}
        self.user_loop_emotes       = {}
        self._loop_notinroom_count  = {}
        self._loop_error_count      = {}

        # ── Bot's own emote loop ──────────────────────────────────────
        self.bot_emote_id   = None
        self.bot_emote_task = None

        # ── Dance floor ───────────────────────────────────────────────
        self.dance_floor            = None
        self.users_dancing_on_floor = {}
        self.dance_beat_start       = 0.0
        self.dance_beat_cycle       = 12.0
        self.dance_floor_emote      = None
        self._floor_beat_errors     = {}
        self._floor_setup_step      = 0
        self._floor_setup_p1        = None

        # ── Cooldowns ─────────────────────────────────────────────────
        self.user_cooldowns = {}
        self.cooldown_seconds = 2

        # ── Follow system ─────────────────────────────────────────────
        self.follow_target_id   = None
        self.follow_target_name = None
        self._follow_task       = None
        self._emote_react_times = {}
        self._last_follow_move  = 0.0

        # ── Bot saved position ────────────────────────────────────────
        self.bot_pos = None
        self.startup_pos = None  # Position to walk to on reconnect (!setpos)

        # ── Dawya emote loop ──────────────────────────────────────────
        self._dawya_loop_task = None
        self._dawya_target_id = None  # Store dawya's user ID

        # ── Task handles ─────────────────────────────────────────────
        self._task_chat_worker    = None
        self._task_whisper_worker = None
        self._task_room_cache     = None
        self._task_heartbeat      = None  # ✅ NEW: heartbeat to keep connection alive
        self._task_auto_save      = None
        self._task_health_check   = None
        self._last_save           = 0.0

        # ── Load persisted data ───────────────────────────────────────
        saved = load_data()
        self.dance_floor    = saved.get("dance_floor", None)
        self.bot_emote_id   = saved.get("bot_emote_id") or None
        self.bot_pos        = saved.get("bot_pos", {'x': 7.5, 'y': 0.0, 'z': 0.5, 'facing': 'FrontRight'})
        self.startup_pos    = saved.get("startup_pos", None)  # Load startup position
        _saved_loops        = saved.get("user_loop_emotes", {})
        self.user_loop_emotes = {uid: tuple(v) for uid, v in _saved_loops.items()}
        print("[Persistence] Data loaded from disk")

    def create_task(self, coro):
        """Create and track asyncio task for clean shutdown."""
        task = asyncio.create_task(coro)
        self._tasks.add(task)
        task.add_done_callback(self._tasks.discard)
        return task

    # ✅ NEW: Safe API call wrappers with semaphore
    async def _safe_send_emote(self, emote_id: str, user_id: str):
        """Send emote with semaphore protection."""
        async with self._api_semaphore:
            return await self.highrise.send_emote(emote_id, user_id)

    async def _safe_chat(self, msg: str):
        """Send chat with semaphore protection."""
        async with self._api_semaphore:
            return await self.highrise.chat(msg)

    async def _safe_whisper(self, user_id: str, msg: str):
        """Send whisper with semaphore protection."""
        async with self._api_semaphore:
            return await self.highrise.whisper(user_id, msg)

    async def _safe_walk_to(self, pos: Position):
        """Walk with semaphore protection."""
        async with self._api_semaphore:
            return await self.highrise.walk_to(pos)

    async def _safe_teleport(self, user_id: str, pos: Position):
        """Teleport with semaphore protection."""
        async with self._api_semaphore:
            return await self.highrise.teleport(user_id, pos)

    async def _safe_get_room_users(self):
        """Get room users with semaphore protection."""
        async with self._api_semaphore:
            return await self.highrise.get_room_users()

    # ─────────────────────────────────────────────────────────────────
    #  HEALTH CHECK
    # ─────────────────────────────────────────────────────────────────
    async def health_check_loop(self):
        """Monitor bot health."""
        try:
            while self.is_connected:
                await asyncio.sleep(30)
                
                active_loops = len(self.looping_users)
                queue_size = self._chat_queue.qsize()
                error_count = sum(self._loop_error_count.values())
                
                if active_loops > 0 or queue_size > 50 or error_count > 0:
                    print(f"[Health] Loops: {active_loops}, ChatQ: {queue_size}, Errors: {error_count}")
                
                if active_loops > 30:
                    print(f"[Health] ⚠️ WARNING: {active_loops} active loops (potential leak)")
                
                if queue_size > 250:
                    print(f"[Health] ⚠️ WARNING: Chat queue at {queue_size}/300")
                
        except asyncio.CancelledError:
            pass
        except Exception as e:
            print(f"[Health] Monitor error: {e}")

    # ✅ NEW: Heartbeat to keep connection alive
    async def _dawya_emote_loop(self):
        """Send random emotes to @_Dawya_ non-stop."""
        print("[Dawya] Loop started, waiting for room to load...")
        await asyncio.sleep(5)  # Wait for room cache to populate
        print("[Dawya] Room loaded, looking for @_Dawya_...")
        
        try:
            while self.is_connected:
                await asyncio.sleep(2)  # Send every 2 seconds
                
                if not self._dawya_target_id:
                    # Try to find _Dawya_ in the room
                    try:
                        # Use the API to get fresh room users with position data
                        room_users = await self._safe_get_room_users()
                        print(f"[Dawya] Searching in room ({len(room_users)} users)")
                        
                        for item in room_users:
                            # Handle both (user, position) tuples and plain user objects
                            if isinstance(item, tuple):
                                u, pos = item
                            else:
                                u = item
                            
                            username = getattr(u, 'username', str(u))
                            print(f"[Dawya] Checking user: '{username}' vs '_Dawya_'")
                            
                            if username == "_Dawya_":
                                self._dawya_target_id = u.id
                                print(f"[Dawya] ✅ FOUND @_Dawya_ with ID {u.id}")
                                break
                    except Exception as e:
                        print(f"[Dawya] ❌ Error finding user: {e}")
                        import traceback
                        traceback.print_exc()
                    continue
                
                # Try to send emote to dawya
                try:
                    # Pick a random emote
                    random_emote_key = random.choice(self.emote_keys)
                    random_emote_id = self.emote_dict[random_emote_key][0]
                    
                    # Send it
                    await asyncio.wait_for(
                        self._safe_send_emote(random_emote_id, self._dawya_target_id),
                        timeout=5.0
                    )
                    print(f"[Dawya] ✅ Sent '{random_emote_key}' to @_Dawya_")
                    
                except asyncio.TimeoutError:
                    print(f"[Dawya] ⚠️ Timeout sending emote to {self._dawya_target_id}")
                except Exception as e:
                    error_str = str(e).lower()
                    print(f"[Dawya] Exception: {type(e).__name__}: {e}")
                    
                    if "not in room" in error_str or "not found" in error_str or "does not exist" in error_str:
                        print(f"[Dawya] ⚠️ User not in room, resetting search")
                        self._dawya_target_id = None
                    elif "closing" not in error_str and "not connected" not in error_str:
                        print(f"[Dawya] ❌ Error sending emote: {e}")
                        
        except asyncio.CancelledError:
            print("[Dawya] Loop cancelled")
        except Exception as e:
            print(f"[Dawya] ❌ Fatal loop error: {e}")
            import traceback
            traceback.print_exc()

    # ─────────────────────────────────────────────────────────────────
    #  PROTECTED LOOP WRAPPER
    # ─────────────────────────────────────────────────────────────────
    async def _protected_loop_wrapper(self, user_id: str, loop_coro):
        """Wrap loop to catch exceptions and clean up."""
        try:
            await loop_coro
        except asyncio.CancelledError:
            print(f"[Loop] Task cancelled for user {user_id}")
        except Exception as e:
            print(f"[Loop] ⚠️ Task crashed for user {user_id}: {e}")
            log_crash("loop_wrapper", e, f"user_id={user_id}")
        finally:
            self.looping_users.pop(user_id, None)
            self._loop_tasks.pop(user_id, None)
            self._loop_error_count.pop(user_id, None)
            self._loop_notinroom_count.pop(user_id, None)
            print(f"[Loop] Cleaned up task for user {user_id}")

    # ─────────────────────────────────────────────────────────────────
    #  HELPERS
    # ─────────────────────────────────────────────────────────────────
    def is_owner(self, user: User) -> bool:
        return (user.username.lower() == self.owner_username.lower() or
                user.username.lower() == self.second_owner_username.lower())

    _MAX_CHAT_LEN = 250

    def _split_msg(self, msg: str) -> list:
        """Split long messages into ≤250-char chunks."""
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
            "startup_pos":      self.startup_pos,  # Save startup position
            "user_loop_emotes": self.user_loop_emotes,
        })

    # ─────────────────────────────────────────────────────────────────
    #  LOOP MANAGEMENT
    # ─────────────────────────────────────────────────────────────────
    def _start_loop(self, user_id: str, loop_coro):
        """Start a protected emote loop."""
        if user_id in self._loop_tasks:
            return
        
        self._loop_error_count[user_id] = 0
        self._loop_notinroom_count[user_id] = 0
        
        task = asyncio.create_task(
            self._protected_loop_wrapper(user_id, loop_coro)
        )
        self._loop_tasks[user_id] = task
        self.looping_users[user_id] = True
        print(f"[Loop] Started loop for user {user_id}")

    def _stop_loop(self, user_id: str):
        """Stop an emote loop."""
        if user_id in self._loop_tasks:
            task = self._loop_tasks[user_id]
            if not task.done():
                task.cancel()
        self.looping_users.pop(user_id, None)
        self._emote_react_times.pop(user_id, None)
        print(f"[Loop] Stopped loop for user {user_id}")

    async def on_user_leave(self, user: User):
        """Clean up user data on leave."""
        self.users_dancing_on_floor.pop(user.id, None)
        self._loop_notinroom_count.pop(user.id, None)
        self._loop_error_count.pop(user.id, None)
        self._emote_react_times.pop(user.id, None)
        
        if self.follow_target_id == user.id:
            self.follow_target_id = None
            self.follow_target_name = None
            if self._follow_task:
                self._follow_task.cancel()
        
        self._stop_loop(user.id)

    async def on_user_move(self, user: User, pos: Position):
        """Follow target when they move."""
        if user.id == self.follow_target_id and self.is_connected:
            now = time.time()
            if now - self._last_follow_move >= 1.5:
                self._last_follow_move = now
                try:
                    await self._safe_walk_to(Position(pos.x + 1.0, pos.y, pos.z, pos.facing))
                except Exception as e:
                    print(f"[Follow] Move error: {e}")

    # ─────────────────────────────────────────────────────────────────
    #  EMOTE LOOPS WITH PROTECTION
    # ─────────────────────────────────────────────────────────────────
    async def loop_emote(self, user_id: str, emote_id: str, duration: float):
        """Loop an emote with proper error handling."""
        MAX_ERRORS = 3
        
        while user_id in self.looping_users and self.is_connected:
            try:
                if not self.is_connected:
                    print(f"[Loop] {user_id} stopping: bot disconnected")
                    break
                
                await asyncio.wait_for(
                    self._safe_send_emote(emote_id, user_id),
                    timeout=5.0
                )
                
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
                
                if "not free" in error_str or "not owned" in error_str:
                    print(f"[Loop] {user_id} stopping: emote permission denied")
                    break
                
                if "not connected" in error_str or "closing" in error_str or "websocket" in error_str:
                    print(f"[Loop] {user_id} connection issue: {e}")
                    break
                
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
        """Loop random emotes."""
        while user_id in self.looping_users and self.is_connected:
            try:
                if not self.is_connected:
                    break
                
                emote_name = random.choice(self.emote_keys)
                emote_data = self.emote_dict[emote_name]
                emote_id = emote_data[0]
                duration = float(emote_data[1])
                
                await asyncio.wait_for(
                    self._safe_send_emote(emote_id, user_id),
                    timeout=5.0
                )
                
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
        
        # ✅ CRITICAL: Initialize semaphore NOW
        self._api_semaphore = asyncio.Semaphore(5)
        
        # Start background tasks
        self._task_chat_worker = self.create_task(self._chat_worker())
        self._task_whisper_worker = self.create_task(self._whisper_worker())
        self._task_room_cache = self.create_task(self._room_cache_updater())
        self._task_heartbeat = self.create_task(self._heartbeat_loop())  # ✅ NEW: heartbeat
        self._task_auto_save = self.create_task(self._auto_save_loop())
        self._task_health_check = self.create_task(self.health_check_loop())
        
        # ✅ NEW: Start Dawya emote loop
        self._dawya_loop_task = self.create_task(self._dawya_emote_loop())
        print("[Start] ✅ Dawya emote loop started!")
        
        # Restore user loops
        for user_id, (emote_id, duration) in list(self.user_loop_emotes.items()):
            self._start_loop(user_id, self.loop_emote(user_id, emote_id, duration))
        
        # ✅ NEW: Walk to startup position if set
        if self.startup_pos:
            try:
                await asyncio.sleep(2)  # Wait for room to load
                pos = Position(
                    self.startup_pos['x'],
                    self.startup_pos['y'],
                    self.startup_pos['z'],
                    self.startup_pos.get('facing', 'FrontRight')
                )
                await self._safe_walk_to(pos)
                print(f"[Start] Walked to startup position: {self.startup_pos}")
            except Exception as e:
                print(f"[Start] Error walking to startup pos: {e}")
        
        self._chat("✨ Emote Bot is online! Type !help for commands ✨")

    async def on_chat(self, user: User, message: str):
        """Handle chat messages."""
        try:
            if user.id == self.highrise.my_id:
                return

            msg = message.strip()
            low = msg.lower()

            # Cooldown check
            now = time.time()
            last = self.user_cooldowns.get(user.id, 0)
            if now - last < self.cooldown_seconds:
                return
            self.user_cooldowns[user.id] = now

            # Help
            if low == '!help':
                self._chat(
                    f"🎭 EMOTE BOT COMMANDS\n"
                    f"1-{len(self.emote_keys)} — play emote by number\n"
                    "loop N — loop emote by number\n"
                    "[name] — play emote by name\n"
                    "loop [name] — loop emote by name\n"
                    "random — loop random emotes\n"
                    "stop / 0 — stop your loop\n"
                    "!dancefloor — teleport to dance floor\n"
                    "!setpos — save current position for reconnect\n"
                    "!party — send 4 emotes to whole room"
                )
                return
            
            # ✅ NEW: !setpos command — save current position
            if low == '!setpos':
                if not self.is_owner(user):
                    self._chat("❌ Owner only!")
                    return
                try:
                    room_users = await self._safe_get_room_users()
                    for u, pos in room_users:
                        if u.id == self.highrise.my_id:
                            self.startup_pos = {
                                'x': pos.x,
                                'y': pos.y,
                                'z': pos.z,
                                'facing': pos.facing
                            }
                            self._persist()
                            self._chat(f"✅ Position saved! Will teleport here on reconnect.")
                            print(f"[SetPos] Saved position: {self.startup_pos}")
                            break
                except Exception as e:
                    self._chat(f"❌ Error: {e}")
                    print(f"[SetPos] Error: {e}")
                return
            
            # ✅ NEW: !testroom command — debug room users
            if low == '!testroom':
                if not self.is_owner(user):
                    return
                try:
                    room_users = await self._safe_get_room_users()
                    print(f"\n[Test] Room users API result type: {type(room_users)}")
                    print(f"[Test] Room users: {room_users}")
                    
                    if room_users:
                        first_user = room_users[0]
                        print(f"[Test] First user type: {type(first_user)}")
                        print(f"[Test] First user: {first_user}")
                        if hasattr(first_user, 'username'):
                            print(f"[Test] First user.username: {first_user.username}")
                        if hasattr(first_user, '__dict__'):
                            print(f"[Test] First user.__dict__: {first_user.__dict__}")
                    
                    # Also check cache
                    print(f"[Test] Cache type: {type(self._room_cache)}")
                    print(f"[Test] Cache content: {self._room_cache}")
                    
                    self._chat(f"Room debug info logged to console")
                except Exception as e:
                    print(f"[Test] Error: {e}")
                    import traceback
                    traceback.print_exc()
                return
            
            # ✅ NEW: !party command — send 4 similar emotes to room
            if low == '!party':
                if not self.is_owner(user):
                    self._chat("❌ Owner only!")
                    return
                try:
                    room_users = await self._safe_get_room_users()
                    # Pick 4 random emotes
                    party_emotes = random.sample(self.emote_keys, min(4, len(self.emote_keys)))
                    
                    for emote_key in party_emotes:
                        emote_data = self.emote_dict[emote_key]
                        emote_id = emote_data[0]
                        
                        # Send to all users in room
                        for u, _ in room_users:
                            if u.id != self.highrise.my_id:
                                try:
                                    await asyncio.wait_for(
                                        self._safe_send_emote(emote_id, u.id),
                                        timeout=5.0
                                    )
                                except:
                                    pass
                        
                        await asyncio.sleep(0.5)  # Stagger emotes
                    
                    self._chat(f"🎉 PARTY! Sent 4 emotes to everyone!")
                except Exception as e:
                    self._chat(f"❌ Party error: {e}")
                    print(f"[Party] Error: {e}")
                return

            # Teleport to dance floor
            if low == '!dancefloor':
                if self.dance_floor:
                    try:
                        await self._safe_teleport(
                            user.id,
                            Position(self.dance_floor['x'], self.dance_floor['y'], self.dance_floor['z'])
                        )
                        self._chat(f"🕺 @{user.username} → dance floor!")
                    except Exception as e:
                        print(f"[Teleport] Error: {e}")
                else:
                    self._chat("Dance floor not set yet!")
                return

            # Stop loop
            if low in ('stop', '0'):
                self._stop_loop(user.id)
                self._chat(f"🛑 @{user.username} stopped.")
                return

            # Random emote loop
            if low == 'random':
                if user.id in self.looping_users:
                    self._chat(f"⚠️ @{user.username} already looping! Type 'stop' first.")
                    return
                self._chat(f"🎲 @{user.username} random loop! Type 'stop' to stop 🛑")
                self._start_loop(user.id, self.loop_random_emote(user.id))
                return

            # Emote by number
            loop_match = re.fullmatch(r"loop\s+(\d+)", low)
            number_match = re.fullmatch(r"(\d+)", low)

            if loop_match or number_match:
                is_loop = bool(loop_match)
                index = int(loop_match.group(1) if loop_match else number_match.group(1)) - 1
                if 0 <= index < len(self.emote_keys):
                    emote_name = self.emote_keys[index]
                    emote_data = self.emote_dict[emote_name]
                    emote_id = emote_data[0]
                    duration = float(emote_data[1])
                    
                    if is_loop:
                        if user.id in self.looping_users:
                            self._chat(f"⚠️ @{user.username} already looping! Type 'stop' first.")
                            return
                        self._chat(f"🔄 @{user.username} looping #{index+1}: {emote_name}")
                        self.user_loop_emotes[user.id] = (emote_id, duration)
                        self._start_loop(user.id, self.loop_emote(user.id, emote_id, duration))
                        self._persist()
                    else:
                        try:
                            await asyncio.wait_for(
                                self._safe_send_emote(emote_id, user.id),
                                timeout=5.0
                            )
                        except asyncio.TimeoutError:
                            print(f"[Emote] Timeout sending to {user.id}")
                        except Exception as e:
                            error_str = str(e).lower()
                            if "not free" in error_str or "not owned" in error_str:
                                self._chat(f"❌ @{user.username} this emote is locked!")
                            else:
                                print(f"[Emote] Error: {e}")
                else:
                    self._chat(f"❌ Pick 1-{len(self.emote_keys)}")
                return

            # Emote by name
            name_loop_match = re.fullmatch(r"loop\s+(.+)", low)
            is_name_loop = bool(name_loop_match)
            emote_query = name_loop_match.group(1).strip() if is_name_loop else low.strip()

            matched_key = self._emote_lower_map.get(emote_query)
            if not matched_key:
                matched_key = self._emote_nospace_map.get(emote_query.replace(" ", ""))

            if matched_key:
                emote_data = self.emote_dict[matched_key]
                emote_id = emote_data[0]
                duration = float(emote_data[1])
                
                if is_name_loop:
                    if user.id in self.looping_users:
                        self._chat(f"⚠️ @{user.username} already looping! Type 'stop' first.")
                        return
                    self._chat(f"🔄 @{user.username} looping: {matched_key}")
                    self.user_loop_emotes[user.id] = (emote_id, duration)
                    self._start_loop(user.id, self.loop_emote(user.id, emote_id, duration))
                    self._persist()
                else:
                    try:
                        await asyncio.wait_for(
                            self._safe_send_emote(emote_id, user.id),
                            timeout=5.0
                        )
                    except asyncio.TimeoutError:
                        print(f"[Emote] Timeout sending to {user.id}")
                    except Exception as e:
                        error_str = str(e).lower()
                        if "not free" in error_str or "not owned" in error_str:
                            self._chat(f"❌ @{user.username} this emote is locked!")
                        else:
                            print(f"[Emote] Error: {e}")

        except Exception as e:
            log_crash("on_chat", e, f"msg={message[:80]}")
            print(f"[Chat] Error: {e}")

    async def _chat_worker(self):
        """Worker to send queued chat messages with semaphore."""
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
                    # ✅ FIXED: Use semaphore
                    await self._safe_chat(msg)
                    await asyncio.sleep(0.3)  # Rate limit
                except Exception as e:
                    error_str = str(e).lower()
                    if "closing" not in error_str and "not connected" not in error_str:
                        print(f"[Chat Worker] Error: {e}")
                finally:
                    self._chat_queue.task_done()
        except asyncio.CancelledError:
            pass
        except Exception as e:
            print(f"[Chat Worker] Fatal error: {e}")

    async def _whisper_worker(self):
        """Worker to send queued whispers with semaphore."""
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
                    # ✅ FIXED: Use semaphore
                    await self._safe_whisper(user_id, text)
                    await asyncio.sleep(0.3)  # Rate limit
                except Exception as e:
                    error_str = str(e).lower()
                    if "closing" not in error_str and "not connected" not in error_str:
                        print(f"[Whisper Worker] Error: {e}")
                finally:
                    self._whisper_queue.task_done()
        except asyncio.CancelledError:
            pass
        except Exception as e:
            print(f"[Whisper Worker] Fatal error: {e}")

    async def _room_cache_updater(self):
        """✅ FIXED: Update room cache with reduced frequency + semaphore."""
        try:
            while self.is_connected:
                try:
                    result = await self._safe_get_room_users()
                    if hasattr(result, "content"):
                        self._room_cache = result.content
                    else:
                        self._room_cache = list(result) if result else []
                    
                    self._room_cache_time = time.time()
                except Exception as e:
                    print(f"[RoomCache] Update error: {e}")
                
                # ✅ FIXED: Reduced frequency from 5s to 20s to reduce API calls
                await asyncio.sleep(20)
        except asyncio.CancelledError:
            pass
        except Exception as e:
            print(f"[RoomCache] Fatal error: {e}")

    async def _auto_save_loop(self):
        """Auto-save every 90 seconds."""
        try:
            while self.is_connected:
                await asyncio.sleep(90)
                self._persist()
        except asyncio.CancelledError:
            pass
        except Exception as e:
            print(f"[AutoSave] Fatal error: {e}")

    async def on_disconnect(self) -> None:
        """Called when bot disconnects."""
        self.is_connected = False
        self._room_cache = []
        
        # Cancel all tracked tasks
        for task in list(self._tasks):
            if not task.done():
                task.cancel()
        
        # Clear all user data
        self.users_dancing_on_floor.clear()
        self.looping_users.clear()
        self._loop_tasks.clear()
        self.user_loop_emotes.clear()
        self._emote_react_times.clear()
        
        # Clear queues
        while not self._chat_queue.empty():
            try:
                self._chat_queue.get_nowait()
                self._chat_queue.task_done()
            except:
                break
        
        while not self._whisper_queue.empty():
            try:
                self._whisper_queue.get_nowait()
                self._whisper_queue.task_done()
            except:
                break
        
        self._persist()
        print("[DISCONNECT] Bot disconnected and cleaned up")


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
