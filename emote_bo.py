import asyncio
import random
import re
import time
import json
import os
import sys
import traceback
import datetime
import aiohttp
from urllib.parse import quote as _urlquote

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
        self.owner_username        = "R13XD"
        self.second_owner_username = "st0f"
        self.target_user_name      = "_Dawya_"  # ✅ Target user for continuous emotes

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

        # ── Bot saved position (for !setpos / keep_alive) ───────────��─
        self.bot_pos = None   # {'x','y','z','facing'} — persisted

        # ── Task handles ─────────────────────────────────────────────
        self._task_chat_worker    = None
        self._task_whisper_worker = None
        self._task_room_cache     = None
        self._task_dance_beat     = None
        self._task_floor_monitor  = None
        self._task_auto_save      = None
        self._task_keep_alive     = None
        self._disconnect_exit_task = None  # Watchdog to force exit if disconnected 30s+
        self._task_target_emotes  = None   # Task for sending emotes to target

        # ✅ FIXED: Target emote rate-limit tracking
        self._last_target_emote_time = 0.0
        self._target_emote_backoff   = 8.0

        self._last_save           = 0.0   # debounce: max once per 90s
        self.http_session         = None   # aiohttp session for API calls

        # ── Load persisted data ───────────────────────────────────────
        saved = load_data()
        self.dance_floor    = saved.get("dance_floor", None)
        self.bot_emote_id   = saved.get("bot_emote_id") or None
        self.bot_pos        = saved.get("bot_pos", {'x': 7.5, 'y': 0.0, 'z': 0.5, 'facing': 'FrontRight'})
        _saved_loops        = saved.get("user_loop_emotes", {})
        self.user_loop_emotes = {uid: tuple(v) for uid, v in _saved_loops.items()}
        # Welcome messages: persisted list of up to 3 strings (can be empty)
        _welcomes = saved.get("welcomes", ["", "", ""])
        welcomes = list(_welcomes) if isinstance(_welcomes, list) else []
        while len(welcomes) < 3:
            welcomes.append("")
        self.welcomes = welcomes[:3]

        print("[Persistence] Data loaded from disk")

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
    def _snapshot(self) -> dict:
        return {
            "dance_floor":      self.dance_floor,
            "bot_emote_id":     self.bot_emote_id,
            "bot_pos":          self.bot_pos,
            "user_loop_emotes": {uid: list(v) for uid, v in self.user_loop_emotes.items()},
            "welcomes":         self.welcomes,
        }

    def _force_save(self):
        """Synchronous, immediate save — bypasses debounce. Use for critical changes."""
        try:
            snapshot = self._snapshot()
            tmp = DATA_FILE + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(snapshot, f, indent=2, ensure_ascii=False)
            os.replace(tmp, DATA_FILE)
            self._last_save = time.time()
            print(f"[Persistence] Force-saved to {DATA_FILE}")
        except Exception as e:
            print(f"[Persistence] FORCE SAVE FAILED: {e}")

    def _persist(self):
        now = time.time()
        if now - self._last_save < 90:
            return
        self._last_save = now
        asyncio.create_task(self._persist_async(self._snapshot()))

    async def _persist_async(self, snapshot: dict):
        try:
            tmp = DATA_FILE + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(snapshot, f, indent=2, ensure_ascii=False)
            os.replace(tmp, DATA_FILE)
        except Exception as e:
            print(f"[Persistence] Async save error: {e}")
            try:
                if os.path.exists(DATA_FILE + ".tmp"):
                    os.remove(DATA_FILE + ".tmp")
            except Exception:
                pass

    # ─────────────────────────────────────────────────────────────────
    #  BACKGROUND TASKS
    # ─────────────────────────────────────────────────────────────────
    async def _chat_worker(self):
        while True:
            try:
                msg = await self._chat_queue.get()
                if not self.is_connected:
                    self._chat_queue.task_done()
                    continue
                try:
                    if len(msg) > 255:
                        msg = msg[:252] + "..."
                    await self.highrise.chat(msg)
                except Exception as e:
                    err = str(e).lower()
                    if "closing transport" in err or "not connected" in err:
                        self.is_connected = False
                    else:
                        print(f"[Chat] Send error: {e}")
                finally:
                    self._chat_queue.task_done()
                await asyncio.sleep(1.1)
            except asyncio.CancelledError:
                return
            except Exception as e:
                log_crash("_chat_worker", e)
                await asyncio.sleep(1.0)

    async def _whisper_worker(self):
        while True:
            try:
                user_id, text = await self._whisper_queue.get()
                if not self.is_connected:
                    self._whisper_queue.task_done()
                    continue
                try:
                    if len(text) > 255:
                        text = text[:252] + "..."
                    await self.highrise.send_whisper(user_id, text)
                except Exception as e:
                    err = str(e).lower()
                    if "closing transport" in err or "not connected" in err:
                        self.is_connected = False
                    elif "rate" in err or "429" in err:
                        await asyncio.sleep(2.0)
                        try:
                            self._whisper_queue.put_nowait((user_id, text))
                        except asyncio.QueueFull:
                            pass
                    else:
                        print(f"[Whisper] Error for {user_id}: {e}")
                finally:
                    self._whisper_queue.task_done()
                await asyncio.sleep(0.8)
            except asyncio.CancelledError:
                return
            except Exception as e:
                log_crash("_whisper_worker", e)
                await asyncio.sleep(1.0)

    async def _room_cache_loop(self):
        """Refresh room user list every 10s."""
        while True:
            try:
                if not self.is_connected:
                    await asyncio.sleep(2)
                    continue
                resp = await self.highrise.get_room_users()
                if hasattr(resp, "content"):
                    self._room_cache      = list(resp.content)
                    self._room_cache_time = time.time()
                await asyncio.sleep(10)
            except asyncio.CancelledError:
                return
            except Exception as e:
                err = str(e).lower()
                
                # 🔥 CRITICAL: Detect fatal transport/connection errors
                if "closed" in err or "connection with id" in err or "transport" in err:
                    print(f"[Cache] 🚨 FATAL ERROR DETECTED: {err}")
                    print("[Cache] Scheduling quick restart in 8 seconds...")
                    
                    async def quick_exit():
                        await asyncio.sleep(8)
                        if not self.is_connected:
                            print("[Cache] Quick-exit: forcing restart (os._exit(1))")
                            os._exit(1)
                    
                    # Cancel old watchdog and schedule new quick one
                    try:
                        if self._disconnect_exit_task and not self._disconnect_exit_task.done():
                            self._disconnect_exit_task.cancel()
                    except:
                        pass
                    self._disconnect_exit_task = asyncio.create_task(quick_exit())
                
                elif "closing transport" in err or "not connected" in err:
                    self.is_connected = False
                
                await asyncio.sleep(5)

    async def _auto_save_loop(self):
        """Force-save every 5 minutes regardless of debounce."""
        while True:
            await asyncio.sleep(300)
            self._last_save = 0.0
            self._persist()

    async def keep_alive(self):
        """Walk to saved bot position every 60s to prevent idle-kick."""
        while True:
            try:
                await asyncio.sleep(60)
                if self.is_connected and self.bot_pos and not self.follow_target_id:
                    try:
                        bp = self.bot_pos
                        await self.highrise.walk_to(
                            Position(bp['x'], bp['y'], bp['z'], bp.get('facing', 'FrontRight'))
                        )
                    except Exception:
                        pass
            except asyncio.CancelledError:
                return
            except Exception as e:
                log_crash("keep_alive", e)
                await asyncio.sleep(10)

    # ─────────────────────────────────────────────────────────────────
    #  FOLLOW SYSTEM
    # ─────────────────────────────────────────────���───────────────────
    async def follow_loop(self):
        """Continuously walk towards the follow target every 2 seconds."""
        while True:
            try:
                await asyncio.sleep(2)
                if not self.is_connected or not self.follow_target_id:
                    break
                room_users = await self.safe_get_room_users()
                target_pos = next(
                    (p for u, p in room_users if u.id == self.follow_target_id),
                    None
                )
                if target_pos is None or not hasattr(target_pos, 'x'):
                    print(f"[Follow] Target {self.follow_target_name} left room — stopping")
                    self.follow_target_id   = None
                    self.follow_target_name = None
                    break
                try:
                    await self.highrise.walk_to(
                        Position(target_pos.x, target_pos.y, target_pos.z, "FrontRight")
                    )
                except Exception as e:
                    if "closing transport" in str(e).lower():
                        self.is_connected = False
                        break
            except asyncio.CancelledError:
                return
            except Exception as e:
                log_crash("follow_loop", e)
                await asyncio.sleep(3)

    def _start_follow(self, user_id: str, username: str):
        """Start following a user, cancelling any previous follow."""
        self._stop_follow()
        self.follow_target_id   = user_id
        self.follow_target_name = username
        self._follow_task = asyncio.create_task(self.follow_loop())

    def _stop_follow(self):
        """Stop following."""
        self.follow_target_id   = None
        self.follow_target_name = None
        if self._follow_task and not self._follow_task.done():
            self._follow_task.cancel()
        self._follow_task = None

    # ─────────────────────────────────────────────────────────────────
    #  SAFE REACT
    # ─────────────────────────────────────────────────────────────────
    async def _safe_react(self, reaction: str, user_id: str):
        if self._api_semaphore is None:
            self._api_semaphore = asyncio.Semaphore(3)
        async with self._api_semaphore:
            try:
                await self.highrise.react(reaction, user_id)
            except Exception as e:
                print(f"[React] {reaction} failed for {user_id}: {e}")
            await asyncio.sleep(0.25)

    # ─────────────────────────────────────────────────────────────────
    #  DANCE FLOOR SYSTEM
    # ─────────────────────────────────────────────────────────────────
    def is_on_floor(self, user_pos, floor_coords: dict) -> bool:
        """Check if a position is inside the dance floor bounding box."""
        try:
            x, y, z = user_pos.x, user_pos.y, user_pos.z
        except AttributeError:
            return False  # seated/anchored user
        return (abs(x - floor_coords['x']) <= floor_coords.get('rx', 2) and
                abs(y - floor_coords['y']) <= floor_coords.get('ry', 0.6) and
                abs(z - floor_coords['z']) <= floor_coords.get('rz', 2))

    async def floor_monitor(self):
        """Poll room every 10s — add/remove users from dance floor tracking."""
        await asyncio.sleep(5)
        while True:
            try:
                await asyncio.sleep(10)
                if not self.is_connected or not self.dance_floor:
                    continue
                room_users = await self.safe_get_room_users()
                for user, position in room_users:
                    if user.id == self.highrise.my_id:
                        continue
                    if not hasattr(position, 'x'):
                        continue
                    if self.is_on_floor(position, self.dance_floor):
                        if user.id not in self.users_dancing_on_floor:
                            last_err = self._floor_beat_errors.get(user.id, 0)
                            if time.time() - last_err < 60:
                                continue  # still in error cooldown
                            self.users_dancing_on_floor[user.id] = False
                            asyncio.create_task(self.auto_dance_on_floor(user.id, user.username))
                    else:
                        self.users_dancing_on_floor.pop(user.id, None)
            except Exception as e:
                log_crash("floor_monitor", e)
                print(f"[FloorMonitor] Error: {e}")

    async def auto_dance_on_floor(self, user_id, username):
        try:
            self.users_dancing_on_floor[user_id] = False
            if self.dance_floor_emote and self.dance_floor_emote in self.emote_dict:
                cycle   = self.dance_beat_cycle
                elapsed = time.time() - self.dance_beat_start
                wait    = max(0.0, cycle - (elapsed % max(cycle, 0.001)))
                if wait > 0.1:
                    await asyncio.sleep(wait)
            if user_id not in self.users_dancing_on_floor:
                return
            self.users_dancing_on_floor[user_id] = True
        except Exception as e:
            log_crash("auto_dance_on_floor", e)
            if user_id in self.users_dancing_on_floor:
                self.users_dancing_on_floor[user_id] = True

    async def dance_beat_loop(self):
        all_emotes = self.emote_keys[:]
        while True:
            try:
                if not self.is_connected:
                    await asyncio.sleep(2)
                    continue
                if self.dance_floor and self.users_dancing_on_floor:
                    emote_name = random.choice(all_emotes)
                    emote_data = self.emote_dict[emote_name]
                    emote_id   = emote_data[0]
                    duration   = float(emote_data[1])

                    self.dance_beat_start  = time.time()
                    self.dance_floor_emote = emote_name
                    beat_call_time         = time.monotonic()

                    room_users     = list(self._room_cache)
                    cached_ids     = {u.id for u, _ in room_users}
                    position_map   = {u.id: pos for u, pos in room_users}

                    stale, task_uids = [], []
                    for uid, active in list(self.users_dancing_on_floor.items()):
                        if not active:
                            continue
                        if uid not in cached_ids:
                            stale.append(uid)
                            continue
                        user_pos = position_map.get(uid)
                        if not user_pos or not self.is_on_floor(user_pos, self.dance_floor):
                            stale.append(uid)
                            continue
                        task_uids.append(uid)

                    BEAT_BATCH        = 5
                    BEAT_PAUSE        = 0.5
                    transport_closing = False

                    async def _send_beat_one(uid):
                        nonlocal transport_closing
                        if transport_closing:
                            return
                        try:
                            await self.highrise.send_emote(emote_id, uid)
                        except Exception as result:
                            err_str = str(result).lower()
                            if "closing transport" in err_str or "not connected" in err_str:
                                self.is_connected = False
                                transport_closing = True
                                print("[Beat] Transport closing — aborting beat tick")
                            elif "not in room" in err_str or "target user" in err_str or "not free" in err_str:
                                self.users_dancing_on_floor.pop(uid, None)
                                return
                            else:
                                self._floor_beat_errors[uid] = time.time()
                            stale.append(uid)

                    for bi in range(0, len(task_uids), BEAT_BATCH):
                        if transport_closing:
                            break
                        batch = task_uids[bi:bi + BEAT_BATCH]
                        await asyncio.gather(*[_send_beat_one(u) for u in batch])
                        if not transport_closing and bi + BEAT_BATCH < len(task_uids):
                            await asyncio.sleep(BEAT_PAUSE)

                    for uid in stale:
                        self.users_dancing_on_floor.pop(uid, None)

                    beat_elapsed        = time.monotonic() - beat_call_time
                    raw_sleep           = self._emote_sleep(emote_id, duration)
                    self.dance_beat_cycle = max(raw_sleep, 12.0)
                    await asyncio.sleep(max(self.dance_beat_cycle - beat_elapsed, 0.5))
                else:
                    await asyncio.sleep(1.0)
            except asyncio.CancelledError:
                return
            except Exception as e:
                log_crash("dance_beat_loop", e)
                print(f"[Beat] Error: {e}")
                await asyncio.sleep(2.0)

    # ─────────────────────────────────────────────────────────────────
    #  EMOTE LOOP SYSTEM
    # ─────────────────────────────────────────────────────────────────

    TRUE_LOOP_EMOTES = {
        "idle-loop-sitfloor", "idle-loop-tired", "idle-loop-tapdance",
        "idle-loop-shy",      "idle-loop-sad",   "idle-loop-happy",
        "idle-loop-annoyed",  "idle-loop-aerobics",
        "idle-dance-casual",  "idle-dance-tiktok4",  "idle-dance-tiktok7",
        "idle-dance-headbobbing", "idle-dance-swinging",
    }

    LOOP_INTERVAL_OVERRIDE = {
        "idle-floating": 13.5,
    }

    EMOTE_EXIT_TAIL = {
        "emote-ghost-idle":   6.5,   "emote-float":        2.0,
        "emote-gravity":      2.0,   "emote-telekinesis":  2.0,
        "emote-astronaut":    2.5,   "emote-jetpack":      2.5,
        "emote-wings":        2.0,   "hcc-jetpack":        2.0,
        "sit-relaxed":        1.5,   "sit-open":           1.5,
        "sit-idle-cute":      1.5,   "sit-idle-phone-text":1.5,
        "idle-floorsleeping": 2.8,   "idle-floorsleeping2":2.8,
        "idle_layingdown":    2.8,   "idle_layingdown2":   2.8,
        "idle-laying-phone-texting": 2.5,
        "idle-laying-phone-talking":  2.5,
        "idle-crouched":      1.8,   "idle-phone-camera":  1.5,
        "idle-phone-talking": 1.5,   "emote-fainting":     2.8,
        "idle_zombie":        0.5,   "idle-sad":           0.5,
        "idle-posh":          0.5,   "idle-angry":         0.5,
        "idle-enthusiastic":  0.5,   "idle-hero":          0.5,
        "idle-lookup":        0.5,   "idle-fighter":       0.5,
        "idle-sleep":         0.5,   "idle-wild":          0.5,
        "idle-nervous":       0.5,   "idle-toilet":        0.5,
        "idle-uwu":           0.5,   "idle-guitar":        0.5,
        "idle_singing":       0.5,   "emote-frog":         1.5,
        "emote-bunnyhop":     0.8,   "emote-harlemshake":  0.5,
        "emote-tapdance":     0.4,   "emote-headball":     0.5,
        "emote-sumo":         0.5,
    }

    EMOTE_LATENCY_COMP = 0.15

    def _emote_sleep(self, emote_id: str, duration: float) -> float:
        if emote_id in self.TRUE_LOOP_EMOTES:
            return duration + 0.05
        if emote_id.startswith("dance-"):
            return duration
        tail = self.EMOTE_EXIT_TAIL.get(emote_id, 0.2)
        return max(duration - tail - self.EMOTE_LATENCY_COMP, 0.5)

    def _start_loop(self, user_id, coro):
        old = self._loop_tasks.get(user_id)
        if old and not old.done():
            old.cancel()
        self.looping_users[user_id] = True
        task = asyncio.create_task(coro)
        self._loop_tasks[user_id] = task
        return task

    def _stop_loop(self, user_id):
        self.looping_users.pop(user_id, None)
        task = self._loop_tasks.pop(user_id, None)
        if task and not task.done():
            task.cancel()

    async def _delayed_loop_restore(self):
        await asyncio.sleep(30)
        if not self.is_connected:
            return
        room_ids = {u.id for u, _ in self._room_cache}
        restored = 0
        for uid, (eid, dur) in list(self.user_loop_emotes.items()):
            if uid in room_ids and uid not in self.looping_users:
                self._start_loop(uid, self.loop_emote(uid, eid, dur))
                restored += 1
            else:
                self.user_loop_emotes.pop(uid, None)
        if restored:
            print(f"[Reconnect] Restored {restored} emote loop(s) from fresh cache")

    async def loop_emote(self, user_id, emote_id, duration):
        current_task = asyncio.current_task()
        try:
            while True:
                if not self.looping_users.get(user_id, False):
                    break
                if self._loop_tasks.get(user_id) is not current_task:
                    break
                if not self.is_connected:
                    await asyncio.sleep(2)
                    continue

                call_time = time.monotonic()

                try:
                    await self.highrise.send_emote(emote_id, user_id)
                    self._loop_notinroom_count.pop(user_id, None)
                except Exception as e:
                    err_str = str(e).lower()
                    if "not in room" in err_str or "target user" in err_str:
                        count = self._loop_notinroom_count.get(user_id, 0) + 1
                        self._loop_notinroom_count[user_id] = count
                        if count >= 5:
                            print(f"[Loop] {user_id} not in room x5 — stopping")
                            self._loop_notinroom_count.pop(user_id, None)
                            self.user_loop_emotes.pop(user_id, None)
                            self._stop_loop(user_id)
                            break
                        await asyncio.sleep(3)
                        continue
                    elif "not free" in err_str:
                        await asyncio.sleep(4)   # user is already emoting
                        continue
                    elif "closing transport" in err_str or "not connected" in err_str:
                        self.is_connected = False
                        break
                    else:
                        print(f"[Loop] Emote error for {user_id}: {e}")
                        self._stop_loop(user_id)
                        break

                if emote_id in self.TRUE_LOOP_EMOTES:
                    while self.looping_users.get(user_id, False) and self._loop_tasks.get(user_id) is current_task:
                        await asyncio.sleep(30)
                    if not self.looping_users.get(user_id, False):
                        break
                else:
                    if emote_id in self.LOOP_INTERVAL_OVERRIDE:
                        target_cycle = self.LOOP_INTERVAL_OVERRIDE[emote_id]
                    else:
                        target_cycle = self._emote_sleep(emote_id, duration)
                    elapsed    = time.monotonic() - call_time
                    sleep_time = max(max(target_cycle, 6.0) - elapsed, 0.05)
                    await asyncio.sleep(sleep_time)

        except asyncio.CancelledError:
            pass
        except Exception as e:
            log_crash("loop_emote", e)
            print(f"[Loop] Error: {e}")
        finally:
            if self._loop_tasks.get(user_id) is current_task:
                self.looping_users.pop(user_id, None)
                self._loop_tasks.pop(user_id, None)

    async def loop_random_emote(self, user_id):
        current_task = asyncio.current_task()
        try:
            while True:
                if not self.looping_users.get(user_id, False):
                    break
                if self._loop_tasks.get(user_id) is not current_task:
                    break
                if not self.is_connected:
                    await asyncio.sleep(2)
                    continue
                emote_name = random.choice(self.emote_keys)
                emote_data = self.emote_dict[emote_name]
                emote_id   = emote_data[0]
                duration   = float(emote_data[1])
                try:
                    call_time = time.monotonic()
                    await self.highrise.send_emote(emote_id, user_id)
                except Exception as e:
                    err_str = str(e).lower()
                    if "closing transport" in err_str or "not connected" in err_str:
                        self.is_connected = False
                        break
                    elif "not free" in err_str:
                        await asyncio.sleep(4)
                        continue
                    await asyncio.sleep(1.0)
                    continue
                target_cycle = self._emote_sleep(emote_id, duration)
                elapsed      = time.monotonic() - call_time
                sleep_time   = max(max(target_cycle, 6.0) - elapsed, 0.05)
                await asyncio.sleep(sleep_time)
        except asyncio.CancelledError:
            pass
        except Exception as e:
            log_crash("loop_random_emote", e)
            print(f"[RandomLoop] Error: {e}")
        finally:
            if self._loop_tasks.get(user_id) is current_task:
                self.looping_users.pop(user_id, None)
                self._loop_tasks.pop(user_id, None)

    async def bot_emote_loop(self, emote_id: str, duration: float):
        try:
            while True:
                if not self.is_connected:
                    await asyncio.sleep(2)
                    continue
                if self.bot_emote_id != emote_id:
                    break
                call_time = time.monotonic()
                try:
                    await self.highrise.send_emote(emote_id)
                except Exception as e:
                    err_str = str(e).lower()
                    if "not in room" in err_str:
                        await asyncio.sleep(5)
                        continue
                    elif "not free" in err_str:
                        await asyncio.sleep(4)
                        continue
                    elif "closing transport" in err_str or "not connected" in err_str:
                        self.is_connected = False
                        break
                    break
                if emote_id in self.TRUE_LOOP_EMOTES:
                    while self.bot_emote_id == emote_id:
                        await asyncio.sleep(30)
                    break
                else:
                    target_cycle = self._emote_sleep(emote_id, duration)
                    elapsed      = time.monotonic() - call_time
                    sleep_time   = max(max(target_cycle, 3.0) - elapsed, 0.05)
                    await asyncio.sleep(sleep_time)
        except asyncio.CancelledError:
            pass
        except Exception as e:
            log_crash("bot_emote_loop", e)
            print(f"[BotEmote] Error: {e}")

    # ✅ FIXED: Target emote system — no more spam / rate-limit crashes
    async def send_emotes_to_target(self):
        """Send random emotes to @_Dawya_ with intelligent backoff and error handling."""
        try:
            while self.is_connected:
                try:
                    # Find target
                    target_user = None
                    for user, pos in self._room_cache:
                        if user.username.lower() == self.target_user_name.lower():
                            target_user = user
                            break

                    if not target_user:
                        await asyncio.sleep(8)
                        continue

                    now = time.time()
                    if now - self._last_target_emote_time < self._target_emote_backoff:
                        await asyncio.sleep(2)
                        continue

                    # Pick random emote
                    emote_name = random.choice(self.emote_keys)
                    emote_data = self.emote_dict[emote_name]
                    emote_id = emote_data[0]

                    try:
                        await asyncio.wait_for(
                            self.highrise.send_emote(emote_id, target_user.id),
                            timeout=6.0
                        )
                        self._last_target_emote_time = time.time()
                        self._target_emote_backoff = random.uniform(8.0, 14.0)  # normal smooth pace

                    except asyncio.TimeoutError:
                        print(f"[TargetEmote] Timeout sending to @{self.target_user_name}")
                        self._target_emote_backoff = 15.0
                    except Exception as e:
                        err_str = str(e).lower()
                        if "not free" in err_str or "already" in err_str:
                            self._target_emote_backoff = random.uniform(20.0, 35.0)
                        elif "not in room" in err_str or "target user" in err_str:
                            self._target_emote_backoff = 12.0
                        elif "closing transport" in err_str or "not connected" in err_str:
                            self.is_connected = False
                            break
                        else:
                            print(f"[TargetEmote] Unexpected error: {e}")
                            self._target_emote_backoff = 18.0

                    await asyncio.sleep(self._target_emote_backoff)

                except asyncio.CancelledError:
                    break
                except Exception as e:
                    print(f"[TargetEmote] Loop error: {e}")
                    await asyncio.sleep(5)

        except asyncio.CancelledError:
            pass
        except Exception as e:
            print(f"[TargetEmote] Fatal error: {e}")

    # ───��─────────────────────────────────────────────────────────────
    #  HIGHRISE EVENTS
    # ─────────────────────────────────────────────────────────────────
    async def on_start(self, session_metadata: SessionMetadata):
        self.is_connected  = True
        
        if self._disconnect_exit_task and not self._disconnect_exit_task.done():
            self._disconnect_exit_task.cancel()
            self._disconnect_exit_task = None
            print("[Start] Cancelled disconnect exit watchdog — reconnected!")
        
        self._api_semaphore = asyncio.Semaphore(3)
        is_reconnect = hasattr(self, '_tasks_started')
        print(f"[Start] {'Reconnected' if is_reconnect else 'Bot online!'}")

        # ── Restart bot emote loop ────────────────────────────────────
        if self.bot_emote_id:
            if self.bot_emote_task and not self.bot_emote_task.done():
                self.bot_emote_task.cancel()
            _eid   = self.bot_emote_id
            _ename = next((k for k, v in self.emote_dict.items() if v[0] == _eid), None)
            _dur   = float(self.emote_dict[_ename][1]) if _ename else 10.0
            async def _delayed_bot_emote(eid=_eid, dur=_dur):
                await asyncio.sleep(5)
                if self.bot_emote_id == eid:
                    if self.bot_emote_task and not self.bot_emote_task.done():
                        self.bot_emote_task.cancel()
                    self.bot_emote_task = asyncio.create_task(self.bot_emote_loop(eid, dur))
            asyncio.create_task(_delayed_bot_emote())

        # ── Restore user loops ────────────────────────────────────────
        if self.user_loop_emotes:
            if is_reconnect:
                asyncio.create_task(self._delayed_loop_restore())
            else:
                room_ids = {u.id for u, _ in self._room_cache}
                restored = 0
                for uid, (eid, dur) in list(self.user_loop_emotes.items()):
                    if uid in room_ids and uid not in self.looping_users:
                        self._start_loop(uid, self.loop_emote(uid, eid, dur))
                        restored += 1
                    else:
                        self.user_loop_emotes.pop(uid, None)
                if restored:
                    print(f"[Start] Restored {restored} user emote loop(s)")

        # ── Move to saved position on every start (fresh deploy or reconnect) ──
        if self.bot_pos and not self.follow_target_id:
            async def _restore_position():
                await asyncio.sleep(3)   # give the session a moment to settle
                if self.is_connected and self.bot_pos and not self.follow_target_id:
                    try:
                        bp = self.bot_pos
                        await self.highrise.walk_to(
                            Position(bp['x'], bp['y'], bp['z'], bp.get('facing', 'FrontRight'))
                        )
                        print(f"[Start] ✅ Moved to saved pos ({bp['x']}, {bp['y']}, {bp['z']})")
                    except Exception as e:
                        print(f"[Start] ⚠️ Could not restore position: {e}")
            asyncio.create_task(_restore_position())

        # ── Start / restart background tasks ─────────────────────────
        task_registry = [
            ('_task_chat_worker',    self._chat_worker),
            ('_task_whisper_worker', self._whisper_worker),
            ('_task_room_cache',     self._room_cache_loop),
            ('_task_dance_beat',     self.dance_beat_loop),
            ('_task_floor_monitor',  self.floor_monitor),
            ('_task_auto_save',      self._auto_save_loop),
            ('_task_keep_alive',     self.keep_alive),
            ('_task_target_emotes',  self.send_emotes_to_target),
        ]
        _always_restart = {'_task_keep_alive'}
        for attr, factory in task_registry:
            existing = getattr(self, attr, None)
            if existing is None or existing.done() or attr in _always_restart:
                if existing and not existing.done():
                    existing.cancel()
                setattr(self, attr, asyncio.create_task(factory()))

        if not is_reconnect:
            self._tasks_started = True
            self._chat("Marhba bikom f room Maroc 2026")

    async def on_user_join(self, user: User, position: Position):
        try:
            if user.id == self.highrise.my_id:
                return
            # Greet with a random non-empty welcome message, if available
            available = [w for w in self.welcomes if isinstance(w, str) and w.strip()]
            if not available:
                return
            msg = random.choice(available)
            if "{user}" in msg:
                out = msg.replace("{user}", f"@{user.username}")
            else:
                out = f"@{user.username} {msg}"
            self._chat(out)
        except Exception as e:
            log_crash("on_user_join", e)

    async def on_user_leave(self, user: User):
        try:
            self._stop_loop(user.id)
            self._loop_notinroom_count.pop(user.id, None)
            self.user_loop_emotes.pop(user.id, None)
            self.users_dancing_on_floor.pop(user.id, None)
            self._floor_beat_errors.pop(user.id, None)
        except Exception as e:
            log_crash("on_user_leave", e)

    async def on_emote(self, user: User, emote_id: str, receiver: User | None):
        try:
            if 'dance' in emote_id.lower():
                now  = time.time()
                last = self._emote_react_times.get(user.id, 0)
                if now - last >= 60:
                    self._emote_react_times[user.id] = now
                    try:
                        await self.highrise.react("fire", user.id)
                    except Exception:
                        pass
        except Exception as e:
            log_crash("on_emote", e)

    async def on_user_move(self, user: User, pos: Position):
        try:
            if user.id == self.highrise.my_id:
                return
            self.user_loop_emotes.pop(user.id, None)
            if self.looping_users.pop(user.id, False):
                self._stop_loop(user.id)
            if user.id in self.users_dancing_on_floor:
                if self.dance_floor and hasattr(pos, 'x'):
                    if not self.is_on_floor(pos, self.dance_floor):
                        self.users_dancing_on_floor.pop(user.id, None)
        except Exception as e:
            log_crash("on_user_move", e)

    async def on_whisper(self, user: User, message: str):
        try:
            if not self.is_owner(user):
                self._whisper(user.id, "🤫 Whisper commands are for owners only!")
                return
            await self._handle_owner_command(user, message, whisper=True)
        except Exception as e:
            log_crash("on_whisper", e)

    # ─────────────────────────────────────────────────────────────────
    #  OWNER COMMANDS (whisper only)
    # ─────────────────────────────────────────────────────────────────
    async def _handle_owner_command(self, user: User, message: str, whisper: bool = False) -> bool:
        msg = message.strip()
        low = msg.lower()

        async def reply(text):
            if whisper:
                self._whisper(user.id, text)
            else:
                self._chat(text)

        if low in ('!help', '!ownercmds'):
            await reply(
                "👑 OWNER COMMANDS:\n"
                "!botemote N — bot loops emote #N\n"
                "!botemotestop — stop bot emote\n"
                "!setpos — save bot's current position\n"
                "!follow @user — bot follows a user\n"
                "!stopfollow — stop following\n"
                "!setdancefloor → !dancepoint ×2\n"
                "!cleardance — clear dance floor\n"
                "!floorstatus — show floor coords\n"
                "!party — everyone same emote\n"
                "!emotes — list all emotes\n"
                "!announce [text] — broadcast msg\n"
                "!addwelcome1/2/3 <text> — set welcome messages (use {user} to insert @username)\n"
                "!cw1/2/3 — clear specific welcome slot\n"
                "!cw — clear all welcomes\n"
                "!showwelcomes — list current welcome messages\n"
                "!copyoutfit @username — attempt to copy someone's outfit (owner only)"
            )
            return True

        # ---------------- Welcome management ----------------
        m = re.match(r"^!addwelcome\s*(\d)?\s*(.*)$", msg, re.IGNORECASE)
        m2 = re.match(r"^!addwelcome([123])\s*(.*)$", msg, re.IGNORECASE)
        if m2:
            idx = int(m2.group(1))
            text = m2.group(2).strip()
            if not text:
                await reply("Usage: !addwelcome{1,2,3} <text>  — use {user} to include @username in message.")
                return True
            self.welcomes[idx-1] = text
            self._force_save()
            await reply(f"✅ Welcome #{idx} saved.")
            return True
        elif m and m.group(1):
            idx = int(m.group(1))
            text = m.group(2).strip()
            if not text:
                await reply("Usage: !addwelcome <1|2|3> <text>  — use {user} to include @username in message.")
                return True
            if not (1 <= idx <= 3):
                await reply("Index must be 1, 2 or 3.")
                return True
            self.welcomes[idx-1] = text
            self._force_save()
            await reply(f"✅ Welcome #{idx} saved.")
            return True

        if low.startswith('!showwelcomes'):
            lines = []
            for i, w in enumerate(self.welcomes, start=1):
                lines.append(f"{i}: {w if w.strip() else '(empty)'}")
            await reply("\n".join(lines))
            return True

        if low == '!cw':
            self.welcomes = ["", "", ""]
            self._force_save()
            await reply("🗑️ All welcome messages cleared.")
            return True
        if low in ('!cw1', '!cw2', '!cw3'):
            idx = int(low[-1])
            self.welcomes[idx-1] = ""
            self._force_save()
            await reply(f"🗑️ Welcome #{idx} cleared.")
            return True

        # ---------------- Copy outfit (enhanced) ----------------
        if low.startswith('!copyoutfit'):
            parts = msg.split(None, 1)
            if len(parts) < 2:
                await reply("Usage: !copyoutfit @username  — owner only.")
                return True
            target_name = parts[1].lstrip("@").strip()
            target_user = await self._lookup_user_by_name(target_name)
            if target_user is None:
                await reply(f"❌ '{target_name}' not found (not in room and no lookup succeeded).")
                return True

            await reply(f"🔎 Attempting to copy outfit from @{target_user.username} ... (best-effort)")

            success, message = await self._attempt_copy_outfit(target_user)
            if success:
                await reply(f"✅ Outfit copied: {message}")
            else:
                await reply(f"❌ Could not copy outfit: {message}")
            return True

        # ---------------- existing commands ----------------
        if low.startswith('!botemote '):
            parts = low.split()
            if len(parts) < 2 or not parts[1].isdigit():
                await reply("Usage: !botemote <number>  e.g. !botemote 5")
                return True
            idx = int(parts[1]) - 1
            if not (0 <= idx < len(self.emote_keys)):
                await reply(f"❌ Pick 1-{len(self.emote_keys)}")
                return True
            emote_name = self.emote_keys[idx]
            emote_data = self.emote_dict[emote_name]
            emote_id   = emote_data[0]
            duration   = float(emote_data[1])
            if self.bot_emote_task and not self.bot_emote_task.done():
                self.bot_emote_task.cancel()
            self.bot_emote_id   = emote_id
            self.bot_emote_task = asyncio.create_task(self.bot_emote_loop(emote_id, duration))
            self._force_save()
            await reply(f"🤖 Bot now looping #{idx+1}: {emote_name}")
            return True

        if low == '!botemotestop':
            if self.bot_emote_task and not self.bot_emote_task.done():
                self.bot_emote_task.cancel()
            self.bot_emote_id   = None
            self.bot_emote_task = None
            self._force_save()
            await reply("🛑 Bot emote stopped.")
            return True

        if low == '!setpos':
            room_users = await self.safe_get_room_users()
            my_pos = next((p for u, p in room_users if u.id == self.highrise.my_id), None)
            if my_pos is None or not hasattr(my_pos, 'x'):
                await reply("❌ Can't read bot position right now. Try again.")
                return True
            self.bot_pos = {
                'x': my_pos.x, 'y': my_pos.y, 'z': my_pos.z,
                'facing': getattr(my_pos, 'facing', 'FrontRight'),
            }
            self._force_save()
            await reply(
                f"📍 Bot position saved: ({my_pos.x:.1f}, {my_pos.y:.1f}, {my_pos.z:.1f})\n"
                "Keep-alive will return here every 60s."
            )
            return True

        if low.startswith('!follow'):
            parts = msg.split(None, 1)
            if len(parts) < 2:
                await reply("Usage: !follow @username  or  !follow username")
                return True
            target_name = parts[1].lstrip('@').strip()
            room_users  = await self.safe_get_room_users()
            target_user = next(
                (u for u, _ in room_users if u.username.lower() == target_name.lower()),
                None
            )
            if target_user is None:
                await reply(f"❌ '{target_name}' not found in room.")
                return True
            self._start_follow(target_user.id, target_user.username)
            await reply(f"🏃 Now following @{target_user.username}! Type !stopfollow to stop.")
            return True

        if low == '!stopfollow':
            if self.follow_target_id:
                name = self.follow_target_name
                self._stop_follow()
                await reply(f"🛑 Stopped following @{name}.")
            else:
                await reply("⚠️ Not currently following anyone.")
            return True

        if low in ('!setdancefloor', '!setdance'):
            self._floor_setup_step = 1
            self._floor_setup_p1   = None
            await reply(
                "🕺 Dance Floor Setup — Step 1/2\n"
                "Walk to the FIRST corner of the dance area\n"
                "then type: !dancepoint"
            )
            return True

        if low == '!dancepoint':
            room_users = await self.safe_get_room_users()
            my_pos     = next((p for u, p in room_users if u.id == user.id), None)
            if my_pos is None or not hasattr(my_pos, 'x'):
                await reply("❌ Can't find your position. Try again.")
                return True
            if self._floor_setup_step == 1:
                self._floor_setup_p1   = {'x': my_pos.x, 'y': my_pos.y, 'z': my_pos.z}
                self._floor_setup_step = 2
                await reply(
                    f"✅ Point 1 saved: ({my_pos.x:.1f}, {my_pos.y:.1f}, {my_pos.z:.1f})\n"
                    "Step 2/2: Walk to the OPPOSITE corner\n"
                    "then type: !dancepoint"
                )
            elif self._floor_setup_step == 2:
                p1 = self._floor_setup_p1
                self.dance_floor = {
                    'x':  (p1['x'] + my_pos.x) / 2,
                    'y':  (p1['y'] + my_pos.y) / 2,
                    'z':  (p1['z'] + my_pos.z) / 2,
                    'rx': abs(p1['x'] - my_pos.x) / 2 + 0.5,
                    'ry': max(abs(p1['y'] - my_pos.y) / 2, 0.6),
                    'rz': abs(p1['z'] - my_pos.z) / 2 + 0.5,
                }
                self._floor_setup_step = 0
                self._force_save()
                await reply(
                    f"✅ Dance Floor set!\n"
                    f"Center: ({self.dance_floor['x']:.1f}, {self.dance_floor['y']:.1f}, {self.dance_floor['z']:.1f})\n"
                    "🕺 Step on it to auto-dance!"
                )
            else:
                await reply("⚠️ Start with !setdancefloor first.")
            return True

        if low == '!cleardance':
            self.dance_floor       = None
            self.dance_floor_emote = None
            self.users_dancing_on_floor.clear()
            self._force_save()
            await reply("🗑️ Dance floor cleared!")
            return True

        if low == '!floorstatus':
            dan_s = (f"({self.dance_floor['x']:.1f}, {self.dance_floor['y']:.1f}, {self.dance_floor['z']:.1f})"
                     if self.dance_floor else "Not set")
            await reply(f"🕺 Dance Floor: {dan_s}")
            return True

        if low == '!party':
            room_users = await self.safe_get_room_users()
            targets    = [u for u, _ in room_users if u.id != self.highrise.my_id]
            if not targets:
                await reply("❌ No users in room!")
                return True
            emote_key = random.choice(self.emote_keys)
            emote_id  = self.emote_dict[emote_key][0]
            duration  = float(self.emote_dict[emote_key][1])
            self._chat("🎉 PARTY TIME! Everyone does the same emote! 🥳")
            async def _do_party(tgts, eid, dur):
                for t in tgts:
                    try:
                        await self.highrise.send_emote(eid, t.id)
                    except Exception as e:
                        print(f"[Party] Failed for {t.username}: {e}")
                    await asyncio.sleep(0.15)
                await asyncio.sleep(max(dur, 2.0))
                for t in tgts:
                    await self._safe_react("clap", t.id)
                self._chat("🎉 Party over! 👏")
            asyncio.create_task(_do_party(targets, emote_id, duration))
            return True

        if low == '!emotes':
            lines   = [f"#{i+1} {k}" for i, k in enumerate(self.emote_keys)]
            chunk   = []
            batches = []
            for line in lines:
                if sum(len(l) for l in chunk) + len(line) > 220:
                    batches.append("\n".join(chunk))
                    chunk = [line]
                else:
                    chunk.append(line)
            if chunk:
                batches.append("\n".join(chunk))
            for batch in batches:
                self._whisper(user.id, batch)
                await asyncio.sleep(0.9)
            return True

        if low.startswith('!announce '):
            self._chat(f"📢 {msg[10:].strip()}")
            return True

        if low == '!dancefloor':
            if self.dance_floor:
                await self.highrise.teleport(
                    user.id,
                    Position(self.dance_floor['x'], self.dance_floor['y'], self.dance_floor['z'])
                )
            else:
                await reply("Dance floor not set yet!")
            return True

        return False

    # ─────────────────────────────────────────────────────────────────
    #  CHAT HANDLER — emote commands for all users
    # ─────────────────────────────────────────────────────────────────
    async def on_chat(self, user: User, message: str):
        try:
            if user.id == self.highrise.my_id:
                return

            msg = message.strip()
            low = msg.lower()

            if self.is_owner(user):
                matched = await self._handle_owner_command(user, message)
                if matched:
                    return

            now  = time.time()
            last = self.user_cooldowns.get(user.id, 0)
            if now - last < self.cooldown_seconds:
                return
            self.user_cooldowns[user.id] = now

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

            if low in ('stop', '0'):
                self._stop_loop(user.id)
                self.user_loop_emotes.pop(user.id, None)
                self._chat(f"🛑 @{user.username} stopped.")
                return

            if low == 'random':
                if user.id in self.looping_users:
                    self._chat(f"⚠️ @{user.username} already looping! Type 'stop' first.")
                    return
                self._chat(f"🎲 @{user.username} random loop! Type 'stop' to stop 🛑")
                self._start_loop(user.id, self.loop_random_emote(user.id))
                return

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
                        self._force_save()
                    else:
                        try:
                            await self.highrise.send_emote(emote_id, user.id)
                        except Exception as e:
                            print(f"[Emote] Error: {e}")
                else:
                    self._chat(f"❌ Pick 1-{len(self.emote_keys)}")
                return

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
                    self._force_save()
                else:
                    try:
                        await self.highrise.send_emote(emote_id, user.id)
                    except Exception as e:
                        print(f"[Emote] Error: {e}")

        except Exception as e:
            log_crash("on_chat", e, f"msg={message[:80]}")
            print(f"[Chat] Error: {e}")

    async def on_disconnect(self) -> None:
        self.is_connected = False
        self._room_cache = []
        
        print("[DISCONNECT] Bot disconnected — scheduling watchdog for quick restart...")
        
        async def _exit_if_still_disconnected():
            await asyncio.sleep(30)
            if not self.is_connected:
                print("[DISCONNECT] Still disconnected after 30s — forcing hard process exit (os._exit(1)).")
                os._exit(1)

        if self._disconnect_exit_task and not self._disconnect_exit_task.done():
            self._disconnect_exit_task.cancel()
        
        self._disconnect_exit_task = asyncio.create_task(_exit_if_still_disconnected())
        print("[DISCONNECT] Watchdog scheduled: will force restart in 30s if still disconnected.")


    # ---------------- Helpers for copy outfit ----------------
    async def _get_http_session(self):
        if self.http_session is None or self.http_session.closed:
            self.http_session = aiohttp.ClientSession()
        return self.http_session

    async def _lookup_user_by_name_api(self, username: str):
        """Resolve username -> User-like object using public Highrise Web API.
        Tries multiple query-param names and handles both flat and nested responses."""
        session = await self._get_http_session()
        headers = {"User-Agent": "Mozilla/5.0", "Accept": "application/json"}
        encoded = _urlquote(username)
        # Try different query param names the Highrise API may accept
        urls_to_try = [
            f"https://webapi.highrise.game/users?username={encoded}",
            f"https://webapi.highrise.game/users?handle={encoded}",
        ]
        for url in urls_to_try:
            print(f"[Lookup API] GET {url}")
            try:
                async with session.get(url, headers=headers,
                                       timeout=aiohttp.ClientTimeout(total=10)) as resp:
                    print(f"[Lookup API] HTTP {resp.status}")
                    raw = await resp.text()
                    print(f"[Lookup API] Raw response: {raw[:400]}")
                    if resp.status != 200:
                        continue
                    try:
                        data = json.loads(raw)
                    except Exception:
                        continue
                    # Normalise to a flat list of user dicts
                    candidates = []
                    if isinstance(data, list):
                        candidates = data
                    elif isinstance(data, dict):
                        for key in ("users", "results", "data", "items"):
                            if key in data and isinstance(data[key], list):
                                candidates = data[key]
                                break
                        if not candidates:
                            # Single-user response?
                            if "id" in data or "_id" in data:
                                candidates = [data]
                    if not candidates:
                        print(f"[Lookup API] Empty result for '{username}' from {url}")
                        continue
                    # Unwrap nested 'user' key if present
                    flat = []
                    for c in candidates:
                        if isinstance(c, dict) and "user" in c and isinstance(c["user"], dict):
                            flat.append(c["user"])
                        else:
                            flat.append(c)
                    # Exact match first, then first result
                    target = next(
                        (u for u in flat
                         if isinstance(u, dict) and
                         u.get("username", u.get("handle", u.get("name", ""))).lower() == username.lower()),
                        flat[0] if flat else None
                    )
                    if not target:
                        continue
                    uid   = target.get("id") or target.get("_id") or target.get("userId")
                    uname = (target.get("username") or target.get("handle")
                             or target.get("name") or username)
                    if uid:
                        print(f"[Lookup API] Resolved '{username}' -> id={uid}, name={uname}")
                        return type('User', (), {'id': uid, 'username': uname})()
                    print(f"[Lookup API] Found entry but no id field: {target}")
            except asyncio.TimeoutError:
                print(f"[Lookup API] Timeout: {url}")
            except Exception as e:
                print(f"[Lookup API] Exception ({url}): {e}")
        print(f"[Lookup API] All attempts failed for '{username}'")
        return None

    async def _fetch_user_outfit_api(self, user_id: str):
        """Fetch a user's equipped outfit item IDs from public Highrise Web API."""
        session = await self._get_http_session()
        headers = {"User-Agent": "Mozilla/5.0"}
        url = f"https://webapi.highrise.game/users/{user_id}"
        print(f"[Outfit API] GET {url}")
        try:
            async with session.get(url, headers=headers, timeout=aiohttp.ClientTimeout(total=8)) as resp:
                print(f"[Outfit API] HTTP {resp.status}")
                if resp.status == 200:
                    data = await resp.json(content_type=None)
                    print(f"[Outfit API] Response keys: {list(data.keys()) if isinstance(data, dict) else type(data)}")
                    # /users/{id} returns a single user object directly — NOT wrapped in a list
                    # Unwrap if the server wraps it anyway
                    user_data = data
                    if isinstance(data, dict) and "user" in data:
                        user_data = data["user"]
                    elif isinstance(data, dict) and "users" in data:
                        users_list = data["users"]
                        user_data = users_list[0] if users_list else {}
                    outfit = user_data.get("outfit", [])
                    if not outfit:
                        print(f"[Outfit API] No outfit data for user {user_id}")
                        return []
                    item_ids = []
                    for item in outfit:
                        if isinstance(item, dict):
                            iid = item.get("id") or item.get("itemId") or item.get("item_id")
                            if iid:
                                item_ids.append(iid)
                        elif item:
                            item_ids.append(item)
                    print(f"[Outfit API] Extracted {len(item_ids)} item IDs: {item_ids}")
                    return item_ids
                else:
                    text = await resp.text()
                    print(f"[Outfit API] Error {resp.status}: {text[:200]}")
        except asyncio.TimeoutError:
            print(f"[Outfit API] Timeout for user {user_id}")
        except Exception as e:
            print(f"[Outfit API] Exception for user {user_id}: {e}")
        return []

    async def _lookup_user_by_name(self, username: str):
        """Try room cache, then live fetch, then REST API for users not in room."""
        try:
            # 1) Room cache (fast path)
            for u, _ in self._room_cache:
                if u.username.lower() == username.lower():
                    return u
            # 2) Live room fetch — cache may be stale after reconnect
            try:
                resp = await self.highrise.get_room_users()
                if hasattr(resp, "content"):
                    self._room_cache = list(resp.content)
                    self._room_cache_time = time.time()
                    for u, _ in self._room_cache:
                        if u.username.lower() == username.lower():
                            return u
            except Exception:
                pass
            # 3) REST API fallback — works even if user is offline or in another room
            return await self._lookup_user_by_name_api(username)
        except Exception as e:
            log_crash("_lookup_user_by_name", e, f"name={username}")
            return None


    def _extract_items_from_response(self, resp):
        """
        Normalize many possible shapes to a list of item dicts or scalar ids.
        Returns list of items (dict or scalar).
        """
        if resp is None:
            return []
        # If it's already a list/tuple of items
        if isinstance(resp, (list, tuple)):
            return list(resp)
        # If it's a dict with common keys
        if isinstance(resp, dict):
            for key in ("items", "closet", "wardrobe", "ownedItems", "inventory", "items_owned"):
                if key in resp and isinstance(resp[key], (list, tuple)):
                    return list(resp[key])
            # sometimes response maps id -> info
            if all(isinstance(k, str) and isinstance(v, dict) for k, v in resp.items()):
                out = []
                for k, v in resp.items():
                    d = dict(v)
                    d.setdefault("id", k)
                    out.append(d)
                return out
        # If object with attributes
        if hasattr(resp, "items") and isinstance(getattr(resp, "items"), (list, tuple)):
            return list(getattr(resp, "items"))
        if hasattr(resp, "closet") and isinstance(getattr(resp, "closet"), (list, tuple)):
            return list(getattr(resp, "closet"))
        return []

    def _is_item_free(self, item):
        """
        Heuristics to determine if an item is free for anyone to wear.
        Checks many common keys: is_free, free, price, cost, currency, is_owned, owned.
        Returns True if likely free, False if definitely paid/owned.
        If unknown, returns False (conservative).
        """
        try:
            if item is None:
                return False
            # If scalar id, we can't be sure -> treat as unknown (conservative: False)
            if not isinstance(item, dict):
                return False
            # explicit flags
            for k in ("is_free", "free", "isPublic", "public"):
                v = item.get(k)
                if isinstance(v, bool) and v:
                    return True
            # owned flags - if it's marked owned it doesn't mean free to others; treat owned==True => not free
            for k in ("owned", "is_owned", "owner"):
                if k in item:
                    v = item.get(k)
                    if isinstance(v, bool) and v:
                        return False
            # price/cost heuristics (0 means free)
            for k in ("price", "cost", "amount", "coinCost"):
                if k in item:
                    v = item.get(k)
                    try:
                        if v in (None, "", 0, "0", 0.0):
                            return True
                        # numeric >0 -> not free
                        if isinstance(v, (int, float)) and v > 0:
                            return False
                        # string with number
                        if isinstance(v, str) and v.isdigit() and int(v) > 0:
                            return False
                    except Exception:
                        pass
            # if metadata contains tags indicating free
            tags = item.get("tags") or item.get("meta_tags") or item.get("labels")
            if isinstance(tags, (list, tuple)):
                for t in tags:
                    if isinstance(t, str) and t.lower() in ("free", "gift", "promo"):
                        return True
            # As a last resort, look for common 'rarity' or 'tier' fields - assume non-free if present and not zero
            if "rarity" in item or "tier" in item:
                return False
            return False
        except Exception:
            return False

    async def _try_get_item_details(self, item_id):
        """
        If SDK exposes a method to fetch item metadata, try it.
        Returns dict or None.
        """
        try:
            methods = ["get_item", "get_item_details", "fetch_item", "get_asset"]
            for m in methods:
                fn = getattr(self.highrise, m, None)
                if callable(fn):
                    try:
                        res = await fn(item_id)
                        if res:
                            if isinstance(res, dict):
                                return res
                            # convert object to dict where possible
                            if hasattr(res, "__dict__"):
                                return dict(vars(res))
                    except Exception:
                        continue
        except Exception as e:
            log_crash("_try_get_item_details", e, f"id={item_id}")
        return None

    async def _attempt_equip_items(self, item_ids):
        """
        Try many method names / parameter shapes to make the bot equip items (on itself).
        Returns (success: bool, message: str).
        """
        if not item_ids:
            return False, "No item IDs to equip."

        # candidate method names and parameter shapes we will try
        wear_candidates = [
            ("wear_items", lambda ids: (ids,)),
            ("wear_items", lambda ids: ({"items": ids},)),
            ("wear_items", lambda ids: ({"itemIds": ids},)),
            ("wear", lambda ids: (ids,)),
            ("wear", lambda ids: ({"items": ids},)),
            ("equip_items", lambda ids: (ids,)),
            ("equip_items", lambda ids: ({"items": ids},)),
            ("set_outfit", lambda ids: (ids,)),
            ("set_outfit", lambda ids: ({"items": ids},)),
            ("set_outfit_items", lambda ids: (ids,)),
            ("set_outfit_items", lambda ids: ({"itemIds": ids},)),
            ("apply_outfit", lambda ids: (ids,)),
        ]

        for method_name, param_factory in wear_candidates:
            fn = getattr(self.highrise, method_name, None)
            if not callable(fn):
                continue
            try:
                args = param_factory(item_ids)
                await fn(*args)
                return True, f"Equipped {len(item_ids)} items via {method_name}."
            except TypeError:
                # wrong signature - try next shape
                continue
            except Exception as e:
                # log and continue trying other methods
                print(f"[Equip] {method_name} failed: {e}")
                continue

        # Some SDKs provide single-item wear methods; try them one-by-one
        single_candidates = ["wear_item", "equip_item", "wearSingle", "wearById"]
        for sid in item_ids:
            for method_name in single_candidates:
                fn = getattr(self.highrise, method_name, None)
                if not callable(fn):
                    continue
                try:
                    await fn(sid)
                    # continue to next item - if multiple succeed, we count them
                    # we don't abort on single failure
                except Exception as e:
                    print(f"[Equip] {method_name}({sid}) failed: {e}")
                    continue

        # if some items were single-equipped, assume success (we didn't track successes above).
        # But be conservative and say we couldn't equip via batch methods.
        return False, "SDK does not expose a known batch equip/set_outfit API."

    async def _attempt_copy_outfit(self, target_user):
        """
        Copy outfit from ANY user (in room or not) using public Highrise Web API.
        Returns (success: bool, message: str).
        """
        try:
            target_id   = getattr(target_user, "id", None)
            target_name = getattr(target_user, "username", None)

            # If we only have a name, resolve via API
            if not target_id and target_name:
                print(f"[Copy] No user ID, resolving '{target_name}' via API...")
                resolved = await self._lookup_user_by_name_api(target_name)
                if resolved:
                    target_id   = resolved.id
                    target_name = resolved.username
                    print(f"[Copy] Resolved to ID {target_id}")
                else:
                    return False, f"Cannot find user '{target_name}' via API."

            if not target_id:
                return False, "No user ID available."

            outfit_items = await self._fetch_user_outfit_api(target_id)
            if not outfit_items:
                return False, "User has no visible outfit or API returned empty."

            # Try to equip each item — SDK will reject ones the bot doesn't own
            success_count = 0
            for item_id in outfit_items:
                try:
                    if hasattr(self.highrise, "wear_item"):
                        await self.highrise.wear_item(item_id)
                    elif hasattr(self.highrise, "equip_item"):
                        await self.highrise.equip_item(item_id)
                    elif hasattr(self.highrise, "wear"):
                        await self.highrise.wear(item_id)
                    else:
                        await self.highrise.wear_items([item_id])
                    success_count += 1
                    print(f"[Copy] Equipped {item_id}")
                except Exception as e:
                    print(f"[Copy] Could not equip {item_id}: {e}")

            if success_count:
                return True, f"Equipped {success_count}/{len(outfit_items)} items from @{target_name}."
            else:
                return False, "No items could be equipped (bot likely doesn't own them)."

        except Exception as e:
            log_crash("_attempt_copy_outfit", e, f"target={getattr(target_user, 'username', '')}")
            return False, f"Unexpected error: {e}"


# ── ENTRY POINT ──────────────────────────────────────────────────────
import subprocess
import sys
import signal as _signal

if __name__ == "__main__":
    import time as _time

    _HR_ROOM_ID   = os.environ.get("HR_ROOM_ID",   "69a3286149cca0f5f12bd44b")
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
