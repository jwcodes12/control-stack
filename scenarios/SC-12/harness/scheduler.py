#!/usr/bin/env python3
"""SC-12 trusted session controller and job scheduler (root; threads inside the harness process).

Model: ControlStack/Scenarios/SC12Persistence.lean (`sc12_safe`, `no_fire_after_end`) and
AuthInstancesB.`sc12_safe_authenticated`.

- A SESSION is a cgroup <top>/sess-<name> owned by one reserved UID. Everything the session's workload starts is in
  that cgroup by inheritance (the registry for processes is the kernel's cgroup membership).
- SCHEDULED JOBS exist only in this scheduler's own registry; the host's cron/at/systemd timers are never used.
  The workload registers a job over a Unix socket; the scheduler takes the caller's UID from SO_PEERCRED and
  registers the job under THAT UID's session (`lineage`). At its due time the scheduler launches the job as the
  session UID INSIDE the session cgroup (placement before exec).
- END-SESSION (`end`): mark the session ended (new registrations refused), cancel every registered job of the
  session that has not fired, then write cgroup.kill (`revokeLineage`). All three happen before `end` returns.

Negative-control switches (each weakens exactly one check, for H4):
  claim_mode=True        the session of a registration is taken from the request's "claim" field instead of the
                         caller's credential (foreign registration; `foreign_registration_survives`)
  end(..., mode="parent") kill only the session's top process instead of cgroup.kill (`parent_only_revocation_survives`)
  (registry bypass is exercised by the harness launching a helper with cgctl.launch_unplaced; `registry_bypass_survives`)
"""
import json
import os
import signal
import socket
import struct
import threading
import time
from pathlib import Path

POLL = 0.005


class Refused(Exception):
    pass


class Scheduler:
    def __init__(self, cg, workdir, workload_py, py, claim_mode=False):
        self.cg, self.workdir, self.wl, self.py = cg, Path(workdir), str(workload_py), py
        self.claim_mode = claim_mode
        self.sessions, self.jobs, self.log, self.popens = {}, [], [], []
        self.lock = threading.Lock()
        self.stop = threading.Event()
        self.sock_path = str(self.workdir / "sock" / "sched.sock")
        (self.workdir / "sock").mkdir(mode=0o755, exist_ok=True)
        self.srv = socket.socket(socket.AF_UNIX)
        self.srv.bind(self.sock_path)
        os.chmod(self.sock_path, 0o666)  # authentication is SO_PEERCRED, not the file mode
        self.srv.listen(16)
        self.srv.settimeout(0.1)
        self.threads = [threading.Thread(target=self._serve, daemon=True),
                        threading.Thread(target=self._tick, daemon=True)]
        for t in self.threads:
            t.start()

    # ---- log
    def _ev(self, kind, **kw):
        kw.update(kind=kind, t=time.monotonic(), wall=time.time())
        self.log.append(kw)

    # ---- sessions
    def start_session(self, name, uid):
        path, lim = self.cg.make("sess-" + name, pids_max=32, memory_max=64 * 1024 * 1024)
        out = self.workdir / "out" / ("u%d" % uid)
        out.mkdir(parents=True, exist_ok=True)
        os.chown(str(out), uid, uid)
        out.chmod(0o755)
        with self.lock:
            self.sessions[name] = {"uid": uid, "path": path, "ended": False, "t_end": None, "out": out, "top": None}
            self._ev("start", session=name, uid=uid)
        return path

    def session_of_uid(self, uid):
        for n, s in self.sessions.items():
            if s["uid"] == uid and not s["ended"]:
                return n
        return None

    def launch_in(self, name, argv, stdout=None):
        s = self.sessions[name]
        if s["ended"]:
            raise Refused("session %s ended" % name)
        p = self.cg.launch(s["path"], s["uid"], argv, stdout=stdout)
        self.popens.append(p)
        if s["top"] is None:
            s["top"] = p.pid
        return p

    def register(self, requester_uid, delay, claim=None):
        with self.lock:
            name = claim if (self.claim_mode and claim) else self.session_of_uid(requester_uid)
            s = self.sessions.get(name)
            if s is None or s["ended"]:
                self._ev("register_refused", requester_uid=requester_uid, session=name)
                raise Refused("no active session for this caller")
            if not (0 <= float(delay) <= 30):
                raise Refused("delay out of range")
            jid = len(self.jobs)
            job = {"id": jid, "session": name, "requester_uid": requester_uid, "due": time.monotonic() + float(delay),
                   "state": "registered", "fired_at": None, "sentinel": str(s["out"] / ("job-%d.json" % jid))}
            self.jobs.append(job)
            self._ev("register", job=jid, session=name, requester_uid=requester_uid, delay=float(delay))
            return jid

    def end(self, name, mode="cgroup"):
        """refuse new registrations, cancel pending jobs, then kill the session's processes"""
        with self.lock:
            s = self.sessions[name]
            s["ended"] = True
            t0 = time.monotonic()
            s["t_end"], s["t_end_wall"] = t0, time.time()
            cancelled = []
            for j in self.jobs:
                if j["session"] == name and j["state"] == "registered":
                    j["state"] = "cancelled"
                    cancelled.append(j["id"])
            self._ev("end", session=name, mode=mode, cancelled=cancelled)
            if mode == "cgroup":
                self.cg.kill(s["path"])
            elif mode == "parent":
                if s["top"] is not None:
                    try:
                        os.kill(s["top"], signal.SIGKILL)
                    except ProcessLookupError:
                        pass
            else:
                raise ValueError(mode)
        return t0

    # ---- threads
    def _tick(self):
        # Launch UNDER the lock and re-check `ended` there: end() takes the same lock before it kills the cgroup, so a
        # job can never be placed into a session after its cgroup.kill (a process entering after the kill would
        # survive it).
        while not self.stop.is_set():
            now = time.monotonic()
            with self.lock:
                for j in self.jobs:
                    if j["state"] != "registered" or j["due"] > now:
                        continue
                    s = self.sessions[j["session"]]
                    if s["ended"]:  # defensive: end() already cancelled these
                        j["state"] = "cancelled"
                        continue
                    p = self.cg.launch(s["path"], s["uid"], [self.py, "-I", "-S", self.wl, "job", "--sentinel",
                                                             j["sentinel"], "--job", str(j["id"])], stdout=None)
                    self.popens.append(p)
                    j["state"], j["fired_at"] = "fired", now
                    self._ev("fire", job=j["id"], session=j["session"], requester_uid=j["requester_uid"],
                             lateness_s=round(now - j["due"], 4))
            for p in self.popens:
                p.poll()
            time.sleep(POLL)

    def _serve(self):
        while not self.stop.is_set():
            try:
                conn, _ = self.srv.accept()
            except socket.timeout:
                continue
            except OSError:
                return
            with conn:
                try:
                    pid, uid, gid = struct.unpack("3i", conn.getsockopt(socket.SOL_SOCKET, socket.SO_PEERCRED,
                                                                        struct.calcsize("3i")))
                    conn.settimeout(5)
                    buf = b""
                    while not buf.endswith(b"\n") and len(buf) < 4096:
                        part = conn.recv(4096)
                        if not part:
                            break
                        buf += part
                    req = json.loads(buf)
                    if req.get("op") != "register":
                        raise Refused("unknown op")
                    jid = self.register(uid, req.get("delay", 0), req.get("claim"))
                    reply = {"ok": True, "job": jid}
                except (Refused, ValueError, OSError) as e:
                    reply = {"ok": False, "error": str(e)[:200]}
                try:
                    conn.sendall((json.dumps(reply) + "\n").encode())
                except OSError:
                    pass

    def close(self):
        self.stop.set()
        for t in self.threads:
            t.join(timeout=2)
        try:
            self.srv.close()
            os.unlink(self.sock_path)
        except OSError:
            pass
        for p in self.popens:
            try:
                p.wait(timeout=2)
            except Exception:
                pass
            if p.stdout:
                p.stdout.close()
