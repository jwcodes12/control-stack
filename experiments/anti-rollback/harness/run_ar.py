#!/usr/bin/env python3
"""Anti-rollback runtime check (root required). Preregistration: prereg/ANTI-ROLLBACK.md (PREREG-ANTI-ROLLBACK-v1).

The runtime counterpart of ControlStack/Core/AntiRollback.lean. Three processes, each with its own numeric UID (no
accounts are created): the ANCHOR service (anchor.py, the stand-in for a TPM NV counter / transparency-log head), the
GATE (gate.py, a budget + one-use-nonce ledger in SQLite bound to the anchor), and the CLIENT (forked by this harness,
setuid, authenticated by SO_PEERCRED). The harness itself is the untrusted OPERATOR: it takes file copies of the
gate's database, restores old ones, deletes it, and crashes the gate at fixed points. Workloads are benign (a few
dozen small SQLite transactions per case). Every case runs on a fresh deployment in a fresh directory.

  H1 rollback refused : after restoring ANY older snapshot (cold: gate stopped and restarted; hot: copied in place
                        under the running gate) or deleting the store, every later operation is refused (fail
                        closed); the anchor and the effect log are unchanged; reconciliation is clean. The anchor
                        refuses increments from non-gate UIDs and non-monotone increments from the gate UID.
  H2 crash recovery   : crash after the store commit (before the anchor increment), after the increment (before the
                        effect), and after the effect (before the reply); restart recovers to anchor == store with
                        exactly one effect per anchored version, a client retry of the in-flight nonce is refused,
                        and recovery time <= RECOVERY_BOUND. Restoring the pre-op snapshot inside the crash window
                        loses only the unacknowledged op (its retry then lands once); restoring an older one fails
                        closed.
  H3 usefulness       : no rollback (restarts and backups only): zero spurious refusals and zero wrong acceptances
                        against a reference ledger.
  H4 control          : the same gate with the anchor disabled: restoring an old snapshot lets a consumed nonce be
                        replayed and the budget be re-spent, and the independent reconciliation detects both.

Independent reconciliation reads only the anchor's own append-only log (anchor.log, written by the anchor UID) and
the effect log (outside the snapshotted store), never the gate's database.
Python 3.9 compatible (runs under the system interpreter via sudo).
"""
import argparse
import datetime
import hashlib
import json
import os
import platform
import select
import shutil
import signal
import socket
import subprocess
import sys
import tempfile
import time
import traceback
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
REPO = HERE.parents[2]
PREREG = REPO / "prereg" / "ANTI-ROLLBACK.md"
PREREG_ID = "PREREG-ANTI-ROLLBACK-v1"

UID_ANCHOR, UID_GATE, UID_CLIENT = 23921, 23922, 23923
ALL_UIDS = (UID_ANCHOR, UID_GATE, UID_CLIENT)
HYPS = ["H1", "H2", "H3", "H4"]
H1_VARIANTS = ["cold-genesis", "cold-mid", "cold-prev", "cold-delete", "hot-mid", "hot-prev", "anchor-api"]
H2_VARIANTS = ["after_commit", "after_anchor", "after_effect", "after_commit+restore-pre",
               "after_commit+restore-older"]
CAP = 100                            # H1, H2, H4 budget
AMOUNT = 20                          # each spend in H1, H2, H4 (5 spends fill the cap)
H3_CAP = 300
H3_RESTART_EVERY = 5                 # ops
H3_BACKUP_EVERY = 4                  # ops (benign backups, never restored)
CRASH_RC = 17
RECOVERY_BOUND = 1.0                 # s, gate restart -> READY (H2)
READY_TIMEOUT = 10.0                 # s
STOP_TIMEOUT = 5.0                   # s
CALL_TIMEOUT = 10.0                  # s, one client call
WALL_LIMIT = 120                     # s, whole run
ENV = {"PATH": "/usr/bin:/bin", "LANG": "C.UTF-8"}


# ---------------------------------------------------------------- independent /proc observation
def proc_scan(uids):
    out = []
    for d in os.listdir("/proc"):
        if not d.isdigit():
            continue
        try:
            with open("/proc/%s/status" % d) as fh:
                status = fh.read()
        except (FileNotFoundError, ProcessLookupError, PermissionError):
            continue
        uid = state = None
        for line in status.splitlines():
            if line.startswith("Uid:"):
                uid = int(line.split()[1])
            elif line.startswith("State:"):
                state = line.split()[1]
        if uid in uids:
            out.append({"pid": int(d), "uid": uid, "state": state})
    return out


def kill_uid(uid, timeout=5.0):
    """SIGKILL every process whose real UID is uid (pidfd, UID re-checked), until 3 consecutive empty scans."""
    if uid not in ALL_UIDS:
        raise ValueError("kill_uid refuses uid %d" % uid)
    t0, quiet, signalled = time.monotonic(), 0, 0
    while time.monotonic() - t0 < timeout:
        pids = [e["pid"] for e in proc_scan({uid}) if e["state"] not in ("Z", "X")]
        if not pids:
            quiet += 1
            if quiet >= 3:
                return {"ok": True, "signalled": signalled}
            time.sleep(0.01)
            continue
        quiet = 0
        for pid in pids:
            try:
                fd = os.pidfd_open(pid)
            except (ProcessLookupError, OSError):
                continue
            try:
                with open("/proc/%d/status" % pid) as fh:
                    same = any(l.startswith("Uid:") and int(l.split()[1]) == uid for l in fh)
                if same:
                    signal.pidfd_send_signal(fd, signal.SIGKILL)
                    signalled += 1
            except (FileNotFoundError, ProcessLookupError, OSError):
                pass
            finally:
                os.close(fd)
        time.sleep(0.005)
    return {"ok": False, "signalled": signalled, "left": proc_scan({uid})}


# ---------------------------------------------------------------- reconciliation (anchor log + effect log only)
def reconcile(anchor_log, effects, cap):
    """anchor_log: the anchor's own records [{version, digest}] (None when the anchor is disabled: H4);
    effects: the effect log [{version, digest, nonce, amount}]. Returns the list of violations."""
    v = []
    ev = [e["version"] for e in effects]
    if any(b <= a for a, b in zip(ev, ev[1:])):
        v.append("effect_versions_not_increasing")
    nonces = [e["nonce"] for e in effects]
    if len(set(nonces)) != len(nonces):
        v.append("duplicate_nonce")
    total = sum(e["amount"] for e in effects)
    if total > cap:
        v.append("over_cap")
    if anchor_log is not None:
        av = [a["version"] for a in anchor_log]
        if av != list(range(1, len(av) + 1)):
            v.append("anchor_log_not_contiguous")
        anchored = [(a["version"], a["digest"]) for a in anchor_log]
        effected = [(e["version"], e["digest"]) for e in effects]
        if any(x not in set(anchored) for x in effected):
            v.append("effect_not_anchored")
        if any(effected.count(x) != 1 for x in anchored):
            v.append("anchored_version_without_exactly_one_effect")
    return {"ok": not v, "violations": v, "n_effects": len(effects), "total": total,
            "anchor_version": None if anchor_log is None else len(anchor_log)}


class Ledger:
    """reference model for H3: what a correct ledger without rollback accepts"""
    def __init__(self, cap):
        self.cap, self.used, self.spent = cap, set(), 0

    def accepts(self, nonce, amount):
        return nonce not in self.used and self.spent + amount <= self.cap

    def apply(self, nonce, amount):
        self.used.add(nonce)
        self.spent += amount


# ---------------------------------------------------------------- processes and calls
def drop_to(uid):
    if uid not in ALL_UIDS:
        raise ValueError(uid)

    def f():
        os.setgroups([])
        os.setgid(uid)
        os.setuid(uid)
        os.umask(0o077)
    return f


def sock_call(path, req, timeout=CALL_TIMEOUT):
    s = socket.socket(socket.AF_UNIX)
    s.settimeout(timeout)
    try:
        s.connect(path)
        s.sendall((json.dumps(req) + "\n").encode())
        buf = b""
        while not buf.endswith(b"\n"):
            part = s.recv(4096)
            if not part:
                break
            buf += part
    finally:
        s.close()
    if not buf.strip():
        return {"ok": None, "error": "no reply (connection closed)"}
    return json.loads(buf)


def as_uid(uid, path, req):
    """one request from a forked child that has dropped to uid (SO_PEERCRED then names uid)"""
    if uid not in ALL_UIDS and uid != 0:
        raise ValueError(uid)
    if uid == 0:
        try:
            return sock_call(path, req)
        except Exception as e:
            return {"ok": None, "error": "exception: %r" % (e,)}
    r, w = os.pipe()
    pid = os.fork()
    if pid == 0:
        try:
            os.close(r)
            signal.alarm(0)
            drop_to(uid)()
            try:
                out = sock_call(path, req)
            except Exception as e:
                out = {"ok": None, "error": "exception: %r" % (e,)}
            os.write(w, json.dumps(out).encode())
        finally:
            os._exit(0)
    os.close(w)
    chunks = []
    while True:
        c = os.read(r, 65536)
        if not c:
            break
        chunks.append(c)
    os.close(r)
    os.waitpid(pid, 0)
    return json.loads(b"".join(chunks) or b'{"ok": null, "error": "child produced nothing"}')


def read_line(p, timeout=READY_TIMEOUT):
    fd, buf, t0 = p.stdout.fileno(), b"", time.monotonic()
    while b"\n" not in buf:
        rem = timeout - (time.monotonic() - t0)
        if rem <= 0:
            raise TimeoutError("no READY within %.1fs from pid %d" % (timeout, p.pid))
        rr, _, _ = select.select([fd], [], [], rem)
        if not rr:
            continue
        chunk = os.read(fd, 65536)
        if not chunk:
            raise RuntimeError("EOF before READY from pid %d (rc=%s)" % (p.pid, p.wait(1)))
        buf += chunk
    return buf.split(b"\n", 1)[0].decode()


def jl(path):
    try:
        with open(str(path)) as f:
            return [json.loads(l) for l in f if l.strip()]
    except FileNotFoundError:
        return []


def sha_file(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest() if Path(p).exists() else None


class Ctx:
    def __init__(self):
        self.work = Path(tempfile.mkdtemp(prefix="ar-run-", dir="/var/tmp"))
        self.work.chmod(0o755)
        self.code = self.work / "code"
        self.code.mkdir(mode=0o755)
        for f in ("anchor.py", "gate.py"):
            shutil.copy2(str(HERE / f), str(self.code / f))
            (self.code / f).chmod(0o644)
        self.logs = self.work / "logs"
        self.logs.mkdir(mode=0o755)
        self.py = sys.executable
        self.n = 0

    def log(self, tag):
        self.n += 1
        return open(str(self.logs / ("%03d-%s.stderr" % (self.n, tag))), "ab")


def mkdir_owned(p, uid, mode):
    p.mkdir(mode=mode)
    os.chown(str(p), uid, uid)
    p.chmod(mode)


class Case:
    """one fresh deployment: anchor (optional), gate, effect log, operator snapshot dir"""

    def __init__(self, ctx, tag, cap=CAP, anchor_on=True):
        self.ctx, self.tag, self.cap, self.anchor_on = ctx, tag, cap, anchor_on
        self.d = ctx.work / tag
        self.d.mkdir(mode=0o755)
        self.anchor_dir, self.anchor_sockdir = self.d / "anchor", self.d / "anchor-sock"
        self.gate_dir, self.gate_sockdir, self.effects_dir = self.d / "gate", self.d / "gate-sock", self.d / "effects"
        mkdir_owned(self.anchor_dir, UID_ANCHOR, 0o700)
        mkdir_owned(self.anchor_sockdir, UID_ANCHOR, 0o755)
        mkdir_owned(self.gate_dir, UID_GATE, 0o700)
        mkdir_owned(self.gate_sockdir, UID_GATE, 0o755)
        mkdir_owned(self.effects_dir, UID_GATE, 0o755)
        self.snaps = self.d / "snaps"
        self.snaps.mkdir(mode=0o700)
        self.anchor_sock, self.gate_sock = str(self.anchor_sockdir / "anchor.sock"), str(self.gate_sockdir / "gate.sock")
        self.db, self.effects_path = self.gate_dir / "gate.sqlite3", self.effects_dir / "effects.log"
        self.anchor_p = self.gate_p = None
        self.events = []

    def ev(self, *a):
        self.events.append(list(a))

    def start_anchor(self):
        argv = [self.ctx.py, "-I", "-S", str(self.ctx.code / "anchor.py"), "--dir", str(self.anchor_dir),
                "--socket", self.anchor_sock, "--gate-uid", str(UID_GATE)]
        self.anchor_p = subprocess.Popen(argv, preexec_fn=drop_to(UID_ANCHOR), stdin=subprocess.DEVNULL,
                                         stdout=subprocess.PIPE, stderr=self.ctx.log(self.tag + "-anchor"), cwd="/",
                                         env=dict(ENV), close_fds=True)
        line = read_line(self.anchor_p)
        if line != "READY":
            raise RuntimeError("anchor: %r" % line)

    def start_gate(self):
        argv = [self.ctx.py, "-I", "-S", str(self.ctx.code / "gate.py"), "--state", str(self.gate_dir),
                "--effects", str(self.effects_path), "--socket", self.gate_sock, "--anchor-socket", self.anchor_sock,
                "--cap", str(self.cap), "--client-uid", str(UID_CLIENT)]
        env = dict(ENV)
        if not self.anchor_on:
            argv.append("--anchor-off")
            env["AR_NEGATIVE_CONTROL"] = "1"
        t0 = time.monotonic()
        self.gate_p = subprocess.Popen(argv, preexec_fn=drop_to(UID_GATE), stdin=subprocess.DEVNULL,
                                       stdout=subprocess.PIPE, stderr=self.ctx.log(self.tag + "-gate"), cwd="/",
                                       env=env, close_fds=True)
        line = read_line(self.gate_p)
        dt = time.monotonic() - t0
        if not line.startswith("READY "):
            raise RuntimeError("gate: %r" % line)
        info = json.loads(line[6:])
        self.ev("gate_ready", info, round(dt, 4))
        return info, dt

    def stop_gate(self):
        p, self.gate_p = self.gate_p, None
        if p is None:
            return None
        if p.poll() is None:
            p.send_signal(signal.SIGTERM)
            try:
                p.wait(STOP_TIMEOUT)
            except subprocess.TimeoutExpired:
                p.kill()
                p.wait(STOP_TIMEOUT)
        p.stdout.close()
        return p.returncode

    def wait_gate_exit(self, timeout=STOP_TIMEOUT):
        p, self.gate_p = self.gate_p, None
        try:
            rc = p.wait(timeout)
        except subprocess.TimeoutExpired:
            p.kill()
            rc = "timeout(killed)"
        p.stdout.close()
        return rc

    def close(self):
        self.stop_gate()
        p, self.anchor_p = self.anchor_p, None
        if p is not None:
            if p.poll() is None:
                p.kill()
            p.wait(STOP_TIMEOUT)
            p.stdout.close()

    def spend(self, nonce, amount):
        r = as_uid(UID_CLIENT, self.gate_sock, {"op": "spend", "nonce": nonce, "amount": amount})
        self.ev("spend", nonce, amount, r)
        return r

    def status(self):
        r = as_uid(UID_CLIENT, self.gate_sock, {"op": "status"})
        self.ev("status", r)
        return r

    def snapshot(self, name):
        shutil.copyfile(str(self.db), str(self.snaps / name))
        self.ev("snapshot", name, sha_file(self.snaps / name))

    def restore(self, name, hot=False):
        """cold: the gate must be stopped; hot: bytes copied in place under the running gate (same inode)"""
        if not hot and self.gate_p is not None:
            raise RuntimeError("cold restore with the gate running")
        data = (self.snaps / name).read_bytes()
        existed = self.db.exists()
        with open(str(self.db), "r+b" if existed else "wb") as f:
            f.write(data)
            f.truncate()
            f.flush()
            os.fsync(f.fileno())
        if not existed:
            os.chown(str(self.db), UID_GATE, UID_GATE)
        self.ev("restore", name, "hot" if hot else "cold")

    def delete_store(self):
        if self.gate_p is not None:
            raise RuntimeError("delete with the gate running")
        self.db.unlink()
        self.ev("delete_store")

    def set_crash(self, point):
        (self.gate_dir / "crash_at").write_text(point)
        self.ev("crash_at", point)

    def anchor_state(self):
        if not self.anchor_on:
            return None
        return json.loads((self.anchor_dir / "state.json").read_text())

    def anchor_log(self):
        return jl(self.anchor_dir / "anchor.log") if self.anchor_on else None

    def effects(self):
        return jl(self.effects_path)

    def reconcile(self):
        return reconcile(self.anchor_log(), self.effects(), self.cap)

    def snapshot_all(self):
        return {"anchor": self.anchor_state(), "anchor_log": self.anchor_log(), "effects": self.effects()}


def refused(r, prefix=""):
    return r.get("ok") is False and str(r.get("error", "")).startswith(prefix)


# ---------------------------------------------------------------- hypotheses
class Rec:
    def __init__(self, hyp, rep, variant):
        self.hyp, self.rep, self.variant = hyp, rep, variant
        self.checks, self.raw, self.error = [], {}, None

    def check(self, name, expected, observed, ok):
        self.checks.append({"name": name, "expected": expected, "observed": observed, "pass": bool(ok)})

    def passed(self):
        return self.error is None and bool(self.checks) and all(c["pass"] for c in self.checks)

    def as_dict(self):
        return {"hyp": self.hyp, "rep": self.rep, "variant": self.variant, "pass": self.passed(),
                "error": self.error, "checks": self.checks, "raw": self.raw}


def fill(c, R, n, snaps=()):
    """spend n1..nn of AMOUNT each, snapshot after the versions listed in snaps (0 = genesis)"""
    if 0 in snaps:
        c.snapshot("S0")
    ok = True
    for i in range(1, n + 1):
        r = c.spend("n%d" % i, AMOUNT)
        ok = ok and r.get("ok") is True and r["result"]["version"] == i
        if i in snaps:
            c.snapshot("S%d" % i)
    R.check("setup spends land", "n1..n%d at versions 1..%d" % (n, n), ok, ok)


def h1(ctx, rep, variant, R):
    c = Case(ctx, "h1-r%d-%s" % (rep, variant))
    try:
        c.start_anchor()
        c.start_gate()
        fill(c, R, 5, snaps=(0, 3, 4))
        before = c.snapshot_all()
        if variant == "anchor-api":
            a = before["anchor"]
            tries = {
                "root increments": as_uid(0, c.anchor_sock, {"op": "increment", "to": a["version"] + 1,
                                                             "digest": "1" * 64}),
                "client increments": as_uid(UID_CLIENT, c.anchor_sock, {"op": "increment", "to": a["version"] + 1,
                                                                        "digest": "1" * 64}),
                "gate uid: to = current": as_uid(UID_GATE, c.anchor_sock, {"op": "increment", "to": a["version"],
                                                                           "digest": "1" * 64}),
                "gate uid: to = current - 1": as_uid(UID_GATE, c.anchor_sock,
                                                     {"op": "increment", "to": a["version"] - 1, "digest": "1" * 64}),
                "gate uid: to = current + 2": as_uid(UID_GATE, c.anchor_sock,
                                                     {"op": "increment", "to": a["version"] + 2, "digest": "1" * 64}),
                "gate uid: reset": as_uid(UID_GATE, c.anchor_sock, {"op": "set", "to": 0}),
                "client reads": as_uid(UID_CLIENT, c.anchor_sock, {"op": "read"}),
            }
            R.raw["tries"] = tries
            for k, r in tries.items():
                R.check("anchor refuses: " + k, "refused", r, refused(r))
            st = c.status()
            R.check("gate still serves", "status ok", st, st.get("ok") and st["result"]["status"] == "ok")
        else:
            mode, which = variant.split("-")
            name = {"genesis": "S0", "mid": "S3", "prev": "S4"}.get(which)
            if mode == "cold":
                c.stop_gate()
                if which == "delete":
                    c.delete_store()
                else:
                    c.restore(name)
                info, _ = c.start_gate()
                R.check("startup detects rollback", "status rollback", info, info["status"] == "rollback")
            else:
                c.restore(name, hot=True)
            attempts = [("n4", AMOUNT), ("f1", AMOUNT), ("n5", AMOUNT), ("n1", AMOUNT)]
            for nonce, amount in attempts:
                r = c.spend(nonce, amount)
                R.check("refused after restore: %s" % nonce, "fail closed", r, refused(r, "fail closed"))
            st = c.status()
            R.check("status reports rollback", "rollback", st, st.get("ok") and st["result"]["status"] == "rollback")
        after = c.snapshot_all()
        R.check("anchor unchanged", before["anchor"], after["anchor"], after["anchor"] == before["anchor"])
        R.check("anchor log unchanged", len(before["anchor_log"]), len(after["anchor_log"]),
                after["anchor_log"] == before["anchor_log"])
        R.check("no new effect", len(before["effects"]), len(after["effects"]), after["effects"] == before["effects"])
        rec = c.reconcile()
        R.raw["reconcile"] = rec
        R.check("reconciliation clean, 5 effects, anchor at 5", {"ok": True, "n": 5, "v": 5},
                {"ok": rec["ok"], "n": rec["n_effects"], "v": rec["anchor_version"], "violations": rec["violations"]},
                rec["ok"] and rec["n_effects"] == 5 and rec["anchor_version"] == 5)
    finally:
        c.close()
        R.raw["events"] = c.events


def h2(ctx, rep, variant, R):
    c = Case(ctx, "h2-r%d-%s" % (rep, variant))
    point, _, restore = variant.partition("+")
    try:
        c.start_anchor()
        c.start_gate()
        fill(c, R, 3, snaps=(2, 3))
        c.set_crash(point)
        r = c.spend("n4", AMOUNT)
        R.check("in-flight op gets no reply", "no reply", r, r.get("ok") is None)
        rc = c.wait_gate_exit()
        R.check("gate crashed at the point", CRASH_RC, rc, rc == CRASH_RC)
        if restore == "restore-pre":
            c.restore("S3")
        elif restore == "restore-older":
            c.restore("S2")
        info, dt = c.start_gate()
        R.raw["recovery_s"] = round(dt, 4)
        R.check("restart -> READY within RECOVERY_BOUND", "<= %.2f s" % RECOVERY_BOUND, round(dt, 4),
                dt <= RECOVERY_BOUND)
        if restore == "restore-older":
            R.check("startup fails closed", "rollback", info, info["status"] == "rollback")
            for nonce in ("n4", "n3", "f1"):
                rr = c.spend(nonce, AMOUNT)
                R.check("refused: %s" % nonce, "fail closed", rr, refused(rr, "fail closed"))
            want_v, want_n = 3, ["n1", "n2", "n3"]
        else:
            expect_rec = {"after_commit": "anchor_incremented", "after_anchor": "effect_reperformed",
                          "after_effect": None}[point] if not restore else None
            R.check("startup ok", "ok", info["status"], info["status"] == "ok")
            got = info["recovered"]["kind"] if info["recovered"] else None
            R.check("recovery action", expect_rec, info["recovered"], got == expect_rec)
            st = c.status()
            a = c.anchor_state()
            same = st.get("ok") and [st["result"]["version"], st["result"]["digest"]] == [a["version"], a["digest"]]
            R.check("anchor == store after restart", "equal (version, digest)", {"store": st, "anchor": a}, same)
            retry = c.spend("n4", AMOUNT)
            if restore == "restore-pre":
                R.check("retry of the lost op lands once", "version 4", retry,
                        retry.get("ok") is True and retry["result"]["version"] == 4)
            else:
                R.check("retry of in-flight nonce refused", "nonce already used", retry,
                        refused(retry, "nonce already used"))
            r5 = c.spend("n5", AMOUNT)
            R.check("next op lands", "version 5", r5, r5.get("ok") is True and r5["result"]["version"] == 5)
            want_v, want_n = 5, ["n1", "n2", "n3", "n4", "n5"]
        eff = c.effects()
        rec = c.reconcile()
        R.raw["reconcile"] = rec
        R.check("effects: exactly one per anchored version", want_n, [e["nonce"] for e in eff],
                [e["nonce"] for e in eff] == want_n and [e["version"] for e in eff] == list(range(1, want_v + 1)))
        R.check("reconciliation clean", {"ok": True, "v": want_v},
                {"ok": rec["ok"], "v": rec["anchor_version"], "violations": rec["violations"]},
                rec["ok"] and rec["anchor_version"] == want_v)
    finally:
        c.close()
        R.raw["events"] = c.events


def h3_ops():
    ops = [("u%02d" % i, 10 + 2 * (i % 5)) for i in range(1, 19)]
    ops.insert(10, ("u05", 10))           # a replay: the reference refuses it
    ops += [("big", 100), ("last", 40)]   # over the cap (refused), then a spend that fits
    return ops


def h3(ctx, rep, variant, R):
    c = Case(ctx, "h3-r%d" % rep, cap=H3_CAP)
    ref = Ledger(H3_CAP)
    try:
        c.start_anchor()
        info, _ = c.start_gate()
        readies = [info]
        spurious, wrong, lat, accepted = [], [], [], 0
        for i, (nonce, amount) in enumerate(h3_ops(), 1):
            t = time.monotonic()
            r = c.spend(nonce, amount)
            lat.append(time.monotonic() - t)
            want = ref.accepts(nonce, amount)
            got = r.get("ok") is True
            if want and not got:
                spurious.append([nonce, amount, r])
            if got and not want:
                wrong.append([nonce, amount, r])
            if want:
                ref.apply(nonce, amount)
            if got:
                accepted += 1
            if i % H3_BACKUP_EVERY == 0:
                c.snapshot("B%d" % i)
            if i % H3_RESTART_EVERY == 0:
                c.stop_gate()
                info, _ = c.start_gate()
                readies.append(info)
        R.raw["latency_ms"] = {"max": round(1000 * max(lat), 2), "median": round(1000 * sorted(lat)[len(lat) // 2], 2)}
        R.check("zero spurious refusals", [], spurious, not spurious)
        R.check("zero wrong acceptances", [], wrong, not wrong)
        R.check("expected refusals were the replay and the over-cap op", 2, len(h3_ops()) - accepted,
                len(h3_ops()) - accepted == 2)
        R.check("every restart clean", "status ok, nothing recovered", readies,
                all(x["status"] == "ok" and x["recovered"] is None for x in readies))
        st = c.status()
        R.check("final status ok", "ok", st, st.get("ok") and st["result"]["status"] == "ok"
                and st["result"]["spent"] == ref.spent)
        rec = c.reconcile()
        R.raw["reconcile"] = rec
        R.check("reconciliation clean", {"ok": True, "n": accepted, "total": ref.spent},
                {"ok": rec["ok"], "n": rec["n_effects"], "total": rec["total"], "violations": rec["violations"]},
                rec["ok"] and rec["n_effects"] == accepted == rec["anchor_version"] and rec["total"] == ref.spent)
    finally:
        c.close()
        R.raw["events"] = c.events


def h4(ctx, rep, variant, R):
    """NEGATIVE CONTROL: anchor disabled. The checks assert that the attack LANDS and that reconciliation SEES it."""
    c = Case(ctx, "h4-r%d" % rep, anchor_on=False)
    try:
        c.start_gate()
        fill(c, R, 5, snaps=(3,))
        c.stop_gate()
        c.restore("S3")
        info, _ = c.start_gate()
        R.check("control: startup does not notice", "ok", info["status"], info["status"] == "ok")
        r4 = c.spend("n4", AMOUNT)
        R.check("control: consumed nonce n4 replayed", "lands", r4, r4.get("ok") is True)
        rf = c.spend("f1", AMOUNT)
        R.check("control: budget re-spent (f1 past the cap)", "lands", rf, rf.get("ok") is True)
        rec = c.reconcile()
        R.raw["reconcile"] = rec
        R.check("reconciliation detects the replay", "duplicate_nonce", rec["violations"],
                "duplicate_nonce" in rec["violations"])
        R.check("reconciliation detects the re-spend", "over_cap", {"total": rec["total"], "cap": CAP,
                                                                    "violations": rec["violations"]},
                "over_cap" in rec["violations"])
    finally:
        c.close()
        R.raw["events"] = c.events


H = {"H1": (h1, H1_VARIANTS), "H2": (h2, H2_VARIANTS), "H3": (h3, ["-"]), "H4": (h4, ["-"])}


# ---------------------------------------------------------------- receipt
def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def git(*args):
    r = subprocess.run(["git", "-c", "safe.directory=%s" % REPO, "-C", str(REPO)] + list(args),
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True)
    return r.stdout.strip() if r.returncode == 0 else "ERROR: " + r.stderr.strip()


def tracked_files():
    return sorted(HERE.glob("*.py")) + [HERE / "README.md", PREREG]


def meta(args):
    rel = [str(p.relative_to(REPO)) for p in tracked_files()]
    return {
        "prereg_id": PREREG_ID, "kind": args.kind, "argv": sys.argv,
        "git_commit": git("rev-parse", "HEAD"), "git_branch": git("rev-parse", "--abbrev-ref", "HEAD"),
        "git_status_harness_and_prereg": git("status", "--porcelain", "--", *rel),
        "git_dirty_any": bool(git("status", "--porcelain")),
        "sha256": {str(p.relative_to(REPO)): sha(p) for p in tracked_files() if p.exists()},
        "uname_r": platform.release(), "uname_a": " ".join(platform.uname()),
        "python": sys.version, "python_executable": sys.executable,
        "sqlite": __import__("sqlite3").sqlite_version,
        "nproc": os.cpu_count(),
        "uids": {"anchor": UID_ANCHOR, "gate": UID_GATE, "client": UID_CLIENT},
        "constants": {k: globals()[k] for k in ("H1_VARIANTS", "H2_VARIANTS", "CAP", "AMOUNT", "H3_CAP",
                                                 "H3_RESTART_EVERY", "H3_BACKUP_EVERY", "CRASH_RC",
                                                 "RECOVERY_BOUND", "READY_TIMEOUT", "STOP_TIMEOUT", "CALL_TIMEOUT",
                                                 "WALL_LIMIT")},
    }


def preflight():
    problems = []
    if os.geteuid() != 0:
        problems.append("must run as root (separate numeric UIDs)")
    stale = proc_scan(set(ALL_UIDS))
    if stale:
        problems.append("processes already running under reserved UIDs: %s" % [e["pid"] for e in stale])
    return problems


def cleanup_all():
    rep = {"kill_uid": {}}
    for u in ALL_UIDS:
        if proc_scan({u}):
            rep["kill_uid"][u] = kill_uid(u)
    rep["left_procs"] = proc_scan(set(ALL_UIDS))
    return rep


def summary_md(m, verdicts, results):
    lines = ["# Anti-rollback run (%s, %s)" % (m["kind"], m["prereg_id"]), "",
             "- commit: `%s` (harness/prereg status: `%s`)" % (m["git_commit"], m["git_status_harness_and_prereg"]
                                                              or "clean"),
             "- kernel: `%s`, python `%s`, sqlite `%s`" % (m["uname_r"], m["python"].split()[0], m["sqlite"]),
             "- started %s, finished %s, wall %.1f s" % (m["started"], m["finished"], m["wall_s"]),
             "- overall: **%s**" % verdicts["overall"], "",
             "| hypothesis | cases passed | verdict |", "|---|---|---|"]
    for h in HYPS:
        if h in verdicts["per_hypothesis"]:
            v = verdicts["per_hypothesis"][h]
            lines.append("| %s%s | %d/%d | %s |" % (h, " (negative control)" if v["negative_control"] else "",
                                                     v["passed"], v["cases"], v["verdict"]))
    rs = [r["raw"]["recovery_s"] for r in results if "recovery_s" in r["raw"]]
    if rs:
        lines += ["", "H2 restart -> READY: max %.3f s, median %.3f s (bound %.2f s)" % (
            max(rs), sorted(rs)[len(rs) // 2], RECOVERY_BOUND)]
    lines += ["", "## Failed checks", ""]
    bad = [(r, c) for r in results for c in r["checks"] if not c["pass"]]
    errs = [r for r in results if r["error"]]
    for r, c in bad:
        lines.append("- %s rep %d %s: %s — expected %s, observed %s" % (
            r["hyp"], r["rep"], r["variant"], c["name"], json.dumps(c["expected"]), json.dumps(c["observed"])[:400]))
    for r in errs:
        lines.append("- %s rep %d %s: ERROR %s" % (r["hyp"], r["rep"], r["variant"], r["error"].splitlines()[-1]))
    if not bad and not errs:
        lines.append("none")
    return "\n".join(lines) + "\n"


class WallLimit(Exception):
    pass


def main():
    ap = argparse.ArgumentParser(description="Anti-rollback runtime check (root).")
    ap.add_argument("--out", required=True, help="receipt directory (must not exist)")
    ap.add_argument("--kind", choices=["dry", "evidence"], required=True)
    ap.add_argument("--reps", type=int, default=5)
    ap.add_argument("--only", default=",".join(HYPS), help="comma list of hypotheses (dry runs only)")
    ap.add_argument("--cleanup-stale", action="store_true", help="only kill reserved-UID processes and exit")
    args = ap.parse_args()
    if args.cleanup_stale:
        print(json.dumps(cleanup_all(), indent=1, default=str))
        return 0
    hyps = [h for h in args.only.split(",") if h]
    if any(h not in HYPS for h in hyps):
        sys.exit("unknown hypothesis in --only")
    if args.kind == "evidence" and (hyps != HYPS or args.reps != 5):
        sys.exit("evidence runs use all hypotheses and --reps 5 (prereg §4)")
    if args.kind == "evidence" and (not PREREG.exists() or "Status: DRAFT" in PREREG.read_text()):
        sys.exit("evidence runs need the frozen prereg (%s still DRAFT or missing)" % PREREG)
    out = Path(args.out)
    if out.exists():
        sys.exit("refusing to overwrite existing --out %s" % out)
    if not out.parent.is_dir():
        sys.exit("parent of --out does not exist: %s" % out.parent)
    out.mkdir()
    (out / "logs").mkdir()
    m = meta(args)
    m["started"] = datetime.datetime.utcnow().isoformat() + "Z"
    m["loadavg_start"] = os.getloadavg()
    t_start = time.monotonic()
    results, cleanup, infra, aborted = [], None, None, None
    problems = preflight()
    if args.kind == "evidence" and m["git_status_harness_and_prereg"]:
        problems.append("evidence run needs committed, unmodified harness and prereg files")
    ctx = None
    if problems:
        infra = problems
    else:
        def on_alarm(signum, frame):
            raise WallLimit("wall limit %d s reached" % WALL_LIMIT)
        signal.signal(signal.SIGALRM, on_alarm)
        signal.alarm(WALL_LIMIT)
        try:
            ctx = Ctx()
            m["sha256"]["<workdir>/code/anchor.py"] = sha(ctx.code / "anchor.py")
            m["sha256"]["<workdir>/code/gate.py"] = sha(ctx.code / "gate.py")
            for rep in range(1, args.reps + 1):
                for h in hyps:
                    fn, variants = H[h]
                    for var in variants:
                        R = Rec(h, rep, var)
                        t = time.monotonic()
                        try:
                            fn(ctx, rep, var, R)
                        except WallLimit:
                            R.error = traceback.format_exc()
                            results.append(R.as_dict())
                            raise
                        except Exception:
                            R.error = traceback.format_exc()
                        R.raw["elapsed_s"] = round(time.monotonic() - t, 3)
                        left = proc_scan(set(ALL_UIDS))
                        R.raw["after_left_procs"] = left
                        results.append(R.as_dict())
                        print("%s rep %d %-26s %s (%.2fs)" % (h, rep, var, "PASS" if R.passed() else "FAIL",
                                                              R.raw["elapsed_s"]), flush=True)
                        if left:
                            aborted = "residue after %s rep %d %s: %s" % (h, rep, var, left)
                            raise RuntimeError(aborted)
        except Exception:
            aborted = aborted or traceback.format_exc()
        finally:
            signal.alarm(0)
            cleanup = cleanup_all()
            if ctx is not None:
                for f in sorted(ctx.logs.iterdir()):
                    shutil.copy2(str(f), str(out / "logs" / f.name))
                shutil.rmtree(str(ctx.work), ignore_errors=True)
                cleanup["workdir_removed"] = not ctx.work.exists()
    m["finished"] = datetime.datetime.utcnow().isoformat() + "Z"
    m["wall_s"] = round(time.monotonic() - t_start, 2)
    m["loadavg_end"] = os.getloadavg()
    per = {}
    for h in hyps:
        rs = [r for r in results if r["hyp"] == h]
        n_ok = sum(r["pass"] for r in rs)
        want = args.reps * len(H[h][1])
        per[h] = {"reps": args.reps, "cases": want, "ran": len(rs), "passed": n_ok, "negative_control": h == "H4",
                  "verdict": "NOT-RUN" if infra else "PASS" if len(rs) == want and n_ok == want else "FAIL"}
    verdicts = {"prereg_id": PREREG_ID, "kind": args.kind, "infra_error": infra, "aborted": aborted,
                "cleanup_ok": cleanup is None or (not cleanup["left_procs"] and cleanup.get("workdir_removed", True)),
                "per_hypothesis": per}
    verdicts["overall"] = ("INFRA-ERROR" if infra else
                           "PASS" if not aborted and verdicts["cleanup_ok"] and all(
                               v["verdict"] == "PASS" for v in per.values()) else "FAIL")
    dump = lambda name, obj: (out / name).write_text(json.dumps(obj, indent=1, sort_keys=True, default=str) + "\n")
    dump("meta.json", m)
    dump("verdicts.json", verdicts)
    dump("cleanup.json", cleanup)
    with open(str(out / "results.jsonl"), "w") as fh:
        for r in results:
            fh.write(json.dumps(r, sort_keys=True, default=str) + "\n")
    (out / "summary.md").write_text(summary_md(m, verdicts, results))
    uid, gid = os.environ.get("SUDO_UID"), os.environ.get("SUDO_GID")
    if uid and gid:
        for root, dirs, files in os.walk(str(out)):
            for n in [root] + [os.path.join(root, f) for f in dirs + files]:
                os.chown(n, int(uid), int(gid))
    print(json.dumps({"overall": verdicts["overall"], "per_hypothesis": per, "aborted": aborted, "infra": infra},
                     indent=1, default=str))
    return 0 if verdicts["overall"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
