#!/usr/bin/env python3
"""SC-16 deploy admission (unprivileged). Preregistration: prereg/SC16-DEPLOY-ADMISSION.md (PREREG-SC16-ADMIT-v1).

Defensive reference test on one Linux host. A benign agent (this runner) stages artifacts into a content-addressed
store and points a MUTABLE tag at them; a separate reviewer process reviews BY DIGEST and signs (digest, target) with
an Ed25519 key it alone holds; a separate approver verifies that signature and issues a signed one-use approval
(nonce, digest, target); an admission controller, the only writer of the disposable target directories, deploys
only content fetched BY DIGEST whose digest is reviewed and approved for exactly that target, once. Each hypothesis
is repeated --reps times on fresh processes:

  H1 every deployed file's SHA-256 has a valid reviewer signature for its target, by a reviewer who is not its
     stager, and a valid one-use approval for that target (independent reconciliation from the principals' own logs);
     failing reviews, wrong targets, self-review and forged signatures are refused
                                    (sc16_safe, sc16_reviewed_content, sc16_safe_disjoint, sc16_safe_authenticated,
                                     distinct_blocks_self_review)
  H2 tag moved after approval: admission deploys the approved digest, never the new content   (verify_blocks_toctou)
  H3 a replayed approval is refused                                    (deployed half of no_nonce_redeploys)
  H4 usefulness: honest deploys succeed within L_DEP
  H5 admin HALT: no deploy after the halt                          (halt_freezes, no_halt_check_breaks deployed half)
  H6 NEGATIVE_CONTROL configurations caught by the reconciliation: deploy-by-tag, no target binding, self-review
     without the distinctness check, no nonce check   (toctou_slot_breaks, no_target_binding_breaks,
                                                       self_review_without_distinct_check, no_nonce_redeploys)

Receipts go to --out, which must not exist. No root, no accounts, no network: Unix sockets in a fresh
/var/tmp/sc16-run-* directory, removed afterwards. Python 3.9 compatible (system interpreter); signatures with the
system /usr/bin/openssl (Ed25519).
"""
import argparse
import base64
import datetime
import hashlib
import json
import math
import os
import platform
import re
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
sys.path.insert(0, str(HERE))
import reconcile  # noqa: E402

REPO = HERE.parents[2]
PREREG = REPO / "prereg" / "SC16-DEPLOY-ADMISSION.md"
PREREG_ID = "PREREG-SC16-ADMIT-v1"
HYPS = ["H1", "H2", "H3", "H4", "H5", "H6"]
CONTROLS = {"H6"}
OPENSSL = "/usr/bin/openssl"

# Preregistered constants (prereg §2-§3). Changing any of them needs a new prereg ID.
H1_HONEST = 8
H4_DEPLOYS = 30
LIFETIME = 30.0
READY_TIMEOUT = 15.0
WALL_LIMIT = 115
H6_CONFIGS = {
    "a_deploy_by_tag": {"admission": ["--by-tag"]},
    "b_no_target_binding": {"admission": ["--no-target-binding"]},
    "c_self_review": {"reviewer": ["--no-distinct-check"]},
    "d_no_nonce": {"admission": ["--no-nonce"]},
}
# Tolerance fixed from dry-run calibration (prereg §3.0).
L_DEP = 0.40                # s, H4: every honest stage -> review -> approve -> deploy completes within this (calibrated)


def artifact(i, extra=""):
    return ("release %s\n%s%s\n" % (i, "benign build artifact payload line\n" * 40, extra)).encode()


# ---------------------------------------------------------------- plumbing
class Rec:
    def __init__(self, hyp, rep):
        self.hyp, self.rep = hyp, rep
        self.checks, self.raw, self.error = [], {}, None

    def check(self, name, expected, observed, ok):
        self.checks.append({"name": name, "expected": expected, "observed": observed, "pass": bool(ok)})

    def passed(self):
        return self.error is None and bool(self.checks) and all(c["pass"] for c in self.checks)

    def as_dict(self):
        return {"hyp": self.hyp, "rep": self.rep, "negative_control": self.hyp in CONTROLS, "pass": self.passed(),
                "error": self.error, "checks": self.checks, "raw": self.raw}


class Ctx:
    def __init__(self):
        self.work = Path(tempfile.mkdtemp(prefix="sc16-run-", dir="/var/tmp"))
        self.work.chmod(0o700)
        self.logs = self.work / "logs"
        self.logs.mkdir()
        self.py = sys.executable

    def script(self, name, *args):
        return [self.py, "-I", "-S", "-B", str(HERE / name)] + [str(a) for a in args]


def read_tag(p, tag, timeout=READY_TIMEOUT):
    fd, buf, t0 = p.stdout.fileno(), b"", time.monotonic()
    while b"\n" not in buf:
        rem = timeout - (time.monotonic() - t0)
        if rem <= 0:
            raise TimeoutError("no %s within %.1fs from pid %d" % (tag, timeout, p.pid))
        r, _, _ = select.select([fd], [], [], rem)
        if not r:
            continue
        chunk = os.read(fd, 65536)
        if not chunk:
            raise RuntimeError("EOF before %s from pid %d (rc=%s)" % (tag, p.pid, p.poll()))
        buf += chunk
    line = buf.split(b"\n", 1)[0].decode()
    if not line.startswith(tag + " "):
        raise RuntimeError("unexpected output: %r" % line)
    return json.loads(line[len(tag) + 1:])


def ancestors():
    out, pid = set(), os.getpid()
    while pid > 1:
        out.add(pid)
        try:
            with open("/proc/%d/status" % pid) as fh:
                pid = int([l for l in fh if l.startswith("PPid:")][0].split()[1])
        except (OSError, IndexError, ValueError):
            break
    return out


def proc_scan(marker):
    """live processes (not this runner or its ancestors) with a command-line ARGUMENT that starts with marker"""
    out, skip = [], ancestors()
    for d in os.listdir("/proc"):
        if not d.isdigit() or int(d) in skip:
            continue
        try:
            with open("/proc/%s/cmdline" % d, "rb") as fh:
                args = [x.decode("utf-8", "replace") for x in fh.read().split(b"\0") if x]
            with open("/proc/%s/stat" % d) as fh:
                st = fh.read()
        except (FileNotFoundError, ProcessLookupError, PermissionError):
            continue
        state = st[st.rindex(")") + 2:].split()[0]
        if any(x.startswith(marker) for x in args) and state not in ("Z", "X"):
            out.append({"pid": int(d), "state": state, "cmd": " ".join(args)[:200]})
    return out


def rpc(path, obj, timeout=10.0):
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    s.settimeout(timeout)
    try:
        s.connect(str(path))
        f = s.makefile("rwb", buffering=0)
        f.write((json.dumps(obj) + "\n").encode())
        line = f.readline()
        if not line:
            raise ConnectionError("no reply")
        return json.loads(line)
    finally:
        s.close()


class Stack:
    """registry + reviewer + approver + admission controller"""

    def __init__(self, ctx, tag, admission=(), reviewer=()):
        self.ctx, self.tag = ctx, tag
        self.d = ctx.work / tag
        self.d.mkdir()
        self.procs = []
        d = self.d
        self.reg, self.rev_sock, self.app_sock = d / "registry.sock", d / "reviewer.sock", d / "approver.sock"
        self.rev_log, self.app_log, self.index = d / "reviewer.jsonl", d / "approver.jsonl", d / "registry-index.jsonl"
        self.deploy_log, self.targets, self.adm_dir = d / "deploys.jsonl", d / "targets", d / "admission-priv"
        self.adm_dir.mkdir(mode=0o700)
        rv = self._spawn("reviewer", ctx.script("signer.py", "--role", "reviewer", "--name", "reviewer-1", "--dir",
                                                d / "reviewer-priv", "--sock", self.rev_sock, "--registry", self.reg,
                                                "--log", self.rev_log, "--openssl", OPENSSL, "--lifetime", LIFETIME,
                                                *reviewer))
        r = read_tag(rv, "READY")
        self.rpub, rpid = r["pub"], r["pid"]
        apv = self._spawn("approver", ctx.script("signer.py", "--role", "approver", "--name", "approver-1", "--dir",
                                                 d / "approver-priv", "--sock", self.app_sock, "--registry", self.reg,
                                                 "--log", self.app_log, "--reviewer-pub", self.rpub, "--openssl",
                                                 OPENSSL, "--lifetime", LIFETIME))
        r = read_tag(apv, "READY")
        self.apub, apid = r["pub"], r["pid"]
        (d / "principals.json").write_text(json.dumps({str(os.getpid()): "agent-1", str(rpid): "reviewer-1",
                                                       str(apid): "approver-1"}))
        read_tag(self._spawn("registry", ctx.script("registry.py", "--sock", self.reg, "--cas", d / "cas", "--index",
                                                    self.index, "--principals", d / "principals.json", "--lifetime",
                                                    LIFETIME)), "READY")
        ad = self._spawn("admission", ctx.script("admission.py", "--dir", self.adm_dir, "--targets", self.targets,
                                                 "--registry", self.reg, "--reviewer-pub", self.rpub, "--approver-pub",
                                                 self.apub, "--deploy-log", self.deploy_log, "--used",
                                                 self.adm_dir / "used.txt", "--openssl", OPENSSL, "--lifetime",
                                                 LIFETIME, *admission))
        self.config = read_tag(ad, "READY")["config"]
        self.agent, self.admin = self.adm_dir / "agent.sock", self.adm_dir / "admin.sock"
        self.replies = []

    def _spawn(self, name, argv):
        with open(str(self.ctx.logs / ("%s-%s.stderr" % (self.tag, name))), "wb") as se:
            p = subprocess.Popen(argv, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=se, close_fds=True)
        self.procs.append(p)
        return p

    def _r(self, what, path, obj):
        r = rpc(path, obj)
        self.replies.append({"call": what, "req": {k: v for k, v in obj.items() if k != "data_b64"}, "reply": r})
        return r

    def stage(self, data):
        return self._r("stage", self.reg, {"op": "put", "data_b64": base64.b64encode(data).decode()})["digest"]

    def tag_set(self, tag, digest):
        return self._r("tag_set", self.reg, {"op": "tag_set", "tag": tag, "digest": digest})

    def review(self, digest, target):
        return self._r("review", self.rev_sock, {"op": "review", "digest": digest, "target": target})

    def reviewer_stage(self, data):
        return self._r("reviewer_stage", self.rev_sock, {"op": "stage",
                                                         "data_b64": base64.b64encode(data).decode()})["digest"]

    def approve(self, digest, target, review_sig, tag=None):
        return self._r("approve", self.app_sock, {"op": "approve", "digest": digest, "target": target,
                                                  "review_sig": review_sig, "tag": tag})

    def deploy(self, approval, review_sig, target):
        return self._r("deploy", self.agent, {"op": "deploy", "approval": approval, "review_sig": review_sig,
                                              "target": target})

    def halt(self):
        return self._r("halt", self.admin, {"op": "halt"})

    def flow(self, data, target, tag="app"):
        """honest flow: stage, tag, review, approve, deploy"""
        dg = self.stage(data)
        self.tag_set(tag, dg)
        rv = self.review(dg, target)
        ap = self.approve(dg, target, rv.get("sig"), tag)
        dp = self.deploy(ap.get("approval"), rv.get("sig"), target)
        return dg, rv, ap, dp

    def reconcile(self):
        files = reconcile.scan_targets(str(self.targets)) if self.targets.exists() else []
        args = (files, reconcile.load(str(self.deploy_log)), reconcile.load(str(self.rev_log)),
                reconcile.load(str(self.app_log)), reconcile.load_index(str(self.index)), self.rpub, self.apub,
                reconcile.Verifier(str(self.d)))
        return reconcile.reconcile(*args), args

    def close(self):
        for p in self.procs:
            if p.poll() is None:
                try:
                    p.kill()
                except OSError:
                    pass
        for p in self.procs:
            try:
                p.wait(timeout=5)
            except subprocess.TimeoutExpired:
                pass
            if p.stdout:
                p.stdout.close()


def keep(out, st):
    d = out / "logs" / st.tag
    d.mkdir(parents=True)
    for f in (st.rev_log, st.app_log, st.index, st.deploy_log, st.d / "principals.json"):
        if f.exists():
            shutil.copy2(str(f), str(d / f.name))
    for name, pub in (("reviewer-pub.pem", st.rpub), ("approver-pub.pem", st.apub)):
        shutil.copy2(pub, str(d / name))
    files = reconcile.scan_targets(str(st.targets)) if st.targets.exists() else []
    with open(str(d / "targets-manifest.json"), "w") as fh:
        json.dump(files, fh, indent=1)
    with open(str(d / "client.json"), "w") as fh:
        json.dump(st.replies, fh, indent=1, default=str)


def check_reconcile(R, rc, name="reconciliation"):
    R.raw.setdefault("reconcile", {})[name] = rc
    R.check("%s: every deployed file has a valid review for its target by a non-stager and a valid one-use "
            "approval for exactly its digest and target (sc16_safe, sc16_reviewed_content, sc16_safe_disjoint)"
            % name, {"defects": 0}, {"files": rc["files"], "defects": rc["defects"]}, rc["ok"])


def agent_forger(st):
    """the agent's OWN Ed25519 key: signatures it makes must not be accepted as the reviewer's or approver's"""
    k = st.d / "agent-key.pem"
    subprocess.run([OPENSSL, "genpkey", "-algorithm", "ed25519", "-out", str(k)], check=True,
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

    def sign(msg):
        with tempfile.NamedTemporaryFile(dir=str(st.d), delete=False) as fh:
            fh.write(msg)
        try:
            return subprocess.run([OPENSSL, "pkeyutl", "-sign", "-inkey", str(k), "-rawin", "-in", fh.name],
                                  stdout=subprocess.PIPE, check=True).stdout.hex()
        finally:
            os.unlink(fh.name)
    return sign


# ---------------------------------------------------------------- hypotheses
def h1(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h1" % rep)
    want, neg = [], {}
    try:
        for i in range(H1_HONEST):
            t = "staging" if i % 2 == 0 else "prod"
            dg, rv, ap, dp = st.flow(artifact("%d.%d" % (rep, i)), t, tag="app-%d" % i)
            want.append((t, dg, bool(dp.get("ok"))))
        # (1) review fails -> no approval -> nothing deploys
        dg = st.stage(artifact("bad", "FORBIDDEN step"))
        rv = st.review(dg, "prod")
        ap = st.approve(dg, "prod", rv.get("sig"))
        neg["failed review"] = {"review": rv.get("error"), "approve": ap.get("error")}
        # (2) approved for staging, deployed to prod
        dg = st.stage(artifact("wrong-target"))
        rv = st.review(dg, "staging")
        ap = st.approve(dg, "staging", rv.get("sig"))
        neg["wrong target"] = st.deploy(ap.get("approval"), rv.get("sig"), "prod").get("error")
        # (3) self-review: the reviewer stages content and is asked to review it
        dg = st.reviewer_stage(artifact("reviewer-staged"))
        neg["self review"] = st.review(dg, "prod").get("error")
        # (4) forged signatures made with the agent's own key
        sign = agent_forger(st)
        dg = st.stage(artifact("forged"))
        fake_rv = sign(("sc16-review|%s|%s" % (dg, "prod")).encode())
        neg["forged review -> approver"] = st.approve(dg, "prod", fake_rv).get("error")
        fake_ap = {"nonce": "f" * 32, "digest": dg, "target": "prod", "tag": None, "approver": "approver-1"}
        fake_ap["sig"] = sign(("sc16-approval|%s|%s|%s|" % (fake_ap["nonce"], dg, "prod")).encode())
        neg["forged approval -> admission"] = st.deploy(fake_ap, fake_rv, "prod").get("error")
        rc, args = st.reconcile()
    finally:
        st.close()
    keep(out, st)
    files = reconcile.scan_targets(str(st.targets))
    got = sorted((f["target"], f["sha"]) for f in files)
    exp = sorted((t, d) for t, d, _ in want)
    R.raw.update(refusals=neg, deployed=got)
    R.check("exactly the %d honest artifacts are deployed, each to its approved target" % H1_HONEST, exp, got,
            got == exp and all(ok for _, _, ok in want))
    expn = {"failed review": {"review": "review failed",
                              "approve": "no valid review signature for this digest and target"},
            "wrong target": "target differs from the approved target",
            "self review": "reviewer is the stager",
            "forged review -> approver": "no valid review signature for this digest and target",
            "forged approval -> admission": "bad approval signature"}
    R.check("refused with the right reason: failed review, wrong target, self-review (distinct_blocks_self_review), "
            "forged review and approval signatures (sc16_safe_authenticated)", expn, neg, neg == expn)
    check_reconcile(R, rc)
    mt = reconcile.mutation_selftest(*args)
    R.check("reconciliation sensitivity: each injected defect in a copy of the stored evidence is flagged", True, mt,
            all(mt.values()) and len(mt) == 6)


def h2(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h2" % rep)
    res = []
    try:
        for i in range(3):
            tag = "app-%d" % i
            a = st.stage(artifact("A%d.%d" % (rep, i)))
            st.tag_set(tag, a)
            rv = st.review(a, "prod")
            ap = st.approve(a, "prod", rv.get("sig"), tag)
            b = st.stage(artifact("B%d.%d" % (rep, i), "content pushed after approval"))
            st.tag_set(tag, b)
            dp = st.deploy(ap.get("approval"), rv.get("sig"), "prod")
            res.append({"A": a, "B": b, "deploy": dp})
        rc, _ = st.reconcile()
    finally:
        st.close()
    keep(out, st)
    files = reconcile.scan_targets(str(st.targets))
    shas = [f["sha"] for f in files]
    R.raw.update(cases=res, deployed=shas)
    R.check("H2: after the tag moved, admission deployed exactly the approved digests (verify_blocks_toctou)",
            sorted(r["A"] for r in res), sorted(shas), sorted(shas) == sorted(r["A"] for r in res))
    R.check("H2: no content the tag was moved to after approval was deployed", [], [r["B"] for r in res if r["B"] in shas],
            not [r for r in res if r["B"] in shas])
    check_reconcile(R, rc)


def h3(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h3" % rep)
    res = []
    try:
        for i in range(3):
            dg, rv, ap, dp = st.flow(artifact("R%d.%d" % (rep, i)), "prod", tag="app-%d" % i)
            again = st.deploy(ap.get("approval"), rv.get("sig"), "prod")
            other = st.deploy(ap.get("approval"), rv.get("sig"), "staging")
            res.append({"first": dp.get("ok"), "replay": again.get("error"), "replay_other_target": other.get("error")})
        rc, _ = st.reconcile()
    finally:
        st.close()
    keep(out, st)
    files = reconcile.scan_targets(str(st.targets))
    R.raw.update(cases=res, files=len(files))
    ok = all(r["first"] and r["replay"] == "approval already used" and r["replay_other_target"] for r in res)
    R.check("H3: each approval deploys once; replays (same or other target) are refused (no_nonce_redeploys, "
            "deployed half)", {"first": True, "replay": "approval already used", "files": 3}, {"cases": res,
                                                                                            "files": len(files)},
            ok and len(files) == 3)
    check_reconcile(R, rc)


def h4(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h4" % rep)
    lat = []
    try:
        for i in range(H4_DEPLOYS):
            t0 = time.monotonic()
            dg, rv, ap, dp = st.flow(artifact("U%d.%d" % (rep, i)), "staging" if i % 3 else "prod", tag="app-%d" % i)
            lat.append({"ok": bool(dp.get("ok")), "lat_s": time.monotonic() - t0})
        rc, _ = st.reconcile()
    finally:
        st.close()
    keep(out, st)
    ls = sorted(x["lat_s"] for x in lat)
    pc = lambda q: round(ls[min(len(ls) - 1, int(round(q * (len(ls) - 1))))] * 1e3, 2)
    R.raw.update(latency_ms={"p50": pc(0.5), "p95": pc(0.95), "max": pc(1.0)}, max_latency_s=max(ls))
    okn = sum(1 for x in lat if x["ok"])
    R.check("H4: all %d honest deploys succeed, each within L_DEP = %.2f s" % (H4_DEPLOYS, L_DEP),
            {"ok": H4_DEPLOYS, "max_s": "<= %.2f" % L_DEP}, {"ok": okn, "latency_ms": R.raw["latency_ms"]},
            okn == H4_DEPLOYS and max(ls) <= L_DEP)
    check_reconcile(R, rc)


def h5(ctx, out, rep, R):
    st = Stack(ctx, "r%d-h5" % rep)
    try:
        for i in range(2):
            st.flow(artifact("P%d.%d" % (rep, i)), "prod", tag="pre-%d" % i)
        pend = []
        for i in range(3):
            dg = st.stage(artifact("Q%d.%d" % (rep, i)))
            rv = st.review(dg, "prod")
            pend.append((st.approve(dg, "prod", rv.get("sig")).get("approval"), rv.get("sig")))
        h = st.halt()
        after = [st.deploy(ap, sig, "prod").get("error") for ap, sig in pend]
        rc, args = st.reconcile()
    finally:
        st.close()
    keep(out, st)
    deps = reconcile.load(str(st.deploy_log))
    late = [d["file"] for d in deps if d.get("t") is None or d["t"] > h["t"]]
    files = reconcile.scan_targets(str(st.targets))
    R.raw.update(refusals_after_halt=after, files=len(files))
    R.check("precondition: deploys before the HALT", 2, len(files) - len(late), len(files) - len(late) == 2)
    R.check("H5: approved deploys after the HALT are refused, nothing is written after it (halt_freezes, "
            "no_halt_check_breaks deployed half)", {"refusals": ["halted"] * 3, "late_files": []},
            {"refusals": after, "late_files": late}, after == ["halted"] * 3 and not late and len(files) == 2)
    check_reconcile(R, rc)


def h6(ctx, out, rep, R):
    fired = {}
    for name, flags in H6_CONFIGS.items():
        st = Stack(ctx, "r%d-h6%s" % (rep, name[0]), admission=flags.get("admission", ()),
                   reviewer=flags.get("reviewer", ()))
        try:
            expect = []
            for i in range(2):
                tag = "app-%d" % i
                if name.startswith("a"):
                    a = st.stage(artifact("A%s.%d" % (rep, i)))
                    st.tag_set(tag, a)
                    rv = st.review(a, "prod")
                    ap = st.approve(a, "prod", rv.get("sig"), tag)
                    b = st.stage(artifact("B%s.%d" % (rep, i), "content pushed after approval"))
                    st.tag_set(tag, b)
                    st.deploy(ap.get("approval"), rv.get("sig"), "prod")
                    expect.append("prod")
                elif name.startswith("b"):
                    a = st.stage(artifact("T%s.%d" % (rep, i)))
                    rv = st.review(a, "staging")
                    ap = st.approve(a, "staging", rv.get("sig"))
                    st.deploy(ap.get("approval"), rv.get("sig"), "prod")
                    expect.append("prod")
                elif name.startswith("c"):
                    a = st.reviewer_stage(artifact("S%s.%d" % (rep, i)))
                    rv = st.review(a, "prod")
                    ap = st.approve(a, "prod", rv.get("sig"))
                    st.deploy(ap.get("approval"), rv.get("sig"), "prod")
                    expect.append("prod")
                else:
                    a = st.stage(artifact("N%s.%d" % (rep, i)))
                    rv = st.review(a, "prod")
                    ap = st.approve(a, "prod", rv.get("sig"))
                    st.deploy(ap.get("approval"), rv.get("sig"), "prod")
                    st.deploy(ap.get("approval"), rv.get("sig"), "prod")
                    expect += ["prod", "prod"]
            rc, _ = st.reconcile()
        finally:
            st.close()
        keep(out, st)
        files = reconcile.scan_targets(str(st.targets))
        fires = (sorted(f["target"] for f in files) == sorted(expect) and
                 sorted(rc["flagged_files"]) == sorted(f["file"] for f in files) and not rc["ok"])
        fired[name] = {"config": st.config, "deployed": [f["file"] for f in files],
                       "defects": [d["defects"] for d in rc["defects"]], "fires": fires}
    R.raw["controls"] = fired
    for name, f in fired.items():
        R.check("H6 CONTROL %s fires: the weakened configuration deploys and reconciliation flags every deployed "
                "file" % name, {"fires": True}, {k: v for k, v in f.items() if k != "config"}, f["fires"])


H = {"H1": h1, "H2": h2, "H3": h3, "H4": h4, "H5": h5, "H6": h6}


# ---------------------------------------------------------------- receipt
def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def git(*args):
    r = subprocess.run(["git", "-C", str(REPO)] + list(args), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       universal_newlines=True)
    return r.stdout.strip() if r.returncode == 0 else "ERROR: " + r.stderr.strip()


def tracked_files():
    return sorted(HERE.glob("*.py")) + [HERE / "README.md", PREREG]


def calibration():
    txt = PREREG.read_text() if PREREG.exists() else ""
    st = re.search(r"^CALIBRATION-STATUS: (\w+)\s*$", txt, re.M)
    vals = {k: float(v) for k, v in re.findall(r"^((?:TAU|L)_\w+) = ([0-9.]+)\s*$", txt, re.M)}
    return {"status": st.group(1) if st else None, "prereg_values": vals,
            "harness_values": {"L_DEP": L_DEP}}


def meta(args):
    rel = [str(p.relative_to(REPO)) for p in tracked_files()]
    models = ["ControlStack/Scenarios/SC16Deploy.lean", "ControlStack/Scenarios/SC16Disjoint.lean",
              "ControlStack/Scenarios/AuthInstancesA.lean"]
    return {
        "prereg_id": PREREG_ID, "kind": args.kind, "argv": sys.argv,
        "git_commit": git("rev-parse", "HEAD"), "git_branch": git("rev-parse", "--abbrev-ref", "HEAD"),
        "git_status_harness_and_prereg": git("status", "--porcelain", "--untracked-files=all", "--", *rel),
        "git_dirty_any": bool(git("status", "--porcelain")),
        "sha256": {str(p.relative_to(REPO)): sha(p) for p in tracked_files() if p.exists()},
        "model_sha256": {m: sha(REPO / m) for m in models},
        "calibration": calibration(),
        "uname_r": platform.release(), "uname_a": " ".join(platform.uname()), "python": sys.version,
        "python_executable": sys.executable, "nproc": os.cpu_count(), "uid": os.getuid(),
        "clock": "time.monotonic_ns (CLOCK_MONOTONIC); one host",
        "openssl": subprocess.run([OPENSSL, "version"], stdout=subprocess.PIPE, universal_newlines=True).stdout.strip(),
        "constants": {k: globals()[k] for k in ("H1_HONEST", "H4_DEPLOYS", "LIFETIME", "WALL_LIMIT", "H6_CONFIGS",
                                                 "L_DEP", "OPENSSL")},
    }


def preflight(args, m):
    problems = []
    if sys.version_info < (3, 9):
        problems.append("python >= 3.9 required")
    if not os.access(OPENSSL, os.X_OK):
        problems.append("%s not available" % OPENSSL)
    if not sys.platform.startswith("linux"):
        problems.append("linux required")
    stale = proc_scan("/var/tmp/sc16-run-")
    if stale:
        problems.append("processes of an earlier sc16 run still alive: %s" % [e["pid"] for e in stale])
    if args.kind == "evidence":
        if m["git_status_harness_and_prereg"]:
            problems.append("evidence run needs committed, unmodified harness and prereg files")
        c = m["calibration"]
        if c["status"] != "FIXED":
            problems.append("prereg calibration status is %s, not FIXED (prereg §3.0)" % c["status"])
        for k, v in c["harness_values"].items():
            if c["prereg_values"].get(k) != float(v):
                problems.append("harness %s %s != prereg %s" % (k, v, c["prereg_values"].get(k)))
    return problems


def summary_md(m, verdicts, results):
    lines = ["# SC-16 deploy admission (%s, %s)" % (m["kind"], m["prereg_id"]), "",
             "- commit: `%s` (harness/prereg status: `%s`)" % (m["git_commit"], m["git_status_harness_and_prereg"]
                                                              or "clean"),
             "- calibration: %s, L_DEP = %s s" % (m["calibration"]["status"], L_DEP),
             "- kernel: `%s`, python `%s`" % (m["uname_r"], m["python"].split()[0]),
             "- started %s, finished %s, wall %.1f s" % (m["started"], m["finished"], m["wall_s"]),
             "- overall: **%s**" % verdicts["overall"], "",
             "| hypothesis | kind | reps passed | verdict |", "|---|---|---|---|"]
    for h in HYPS:
        if h in verdicts["per_hypothesis"]:
            v = verdicts["per_hypothesis"][h]
            lines.append("| %s | %s | %d/%d | %s |" % (h, "NEGATIVE_CONTROL" if h in CONTROLS else "claim",
                                                     v["passed"], v["reps"], v["verdict"]))
    lines += ["", "## Key measurements per repetition", ""]
    for r in results:
        raw, s = r["raw"], ""
        if r["hyp"] == "H4":
            s = "latency ms %s" % raw.get("latency_ms")
        elif r["hyp"] == "H6":
            s = "controls fired: %s" % {k: v["fires"] for k, v in raw.get("controls", {}).items()}
        else:
            s = "deployed files %s" % (raw.get("reconcile", {}).get("reconciliation", {}).get("files"))
        lines.append("- %s rep %d: %s" % (r["hyp"], r["rep"], s))
    lines += ["", "## Failed checks", ""]
    bad = [(r["hyp"], r["rep"], c) for r in results for c in r["checks"] if not c["pass"]]
    errs = [(r["hyp"], r["rep"], r["error"]) for r in results if r["error"]]
    for h, rp, c in bad:
        lines.append("- %s rep %d: %s — expected %s, observed %s" % (h, rp, c["name"], json.dumps(c["expected"]),
                                                                   json.dumps(c["observed"], default=str)[:400]))
    for h, rp, e in errs:
        lines.append("- %s rep %d: ERROR %s" % (h, rp, e.splitlines()[-1] if e else e))
    if not bad and not errs:
        lines.append("none")
    return "\n".join(lines) + "\n"


class WallLimit(Exception):
    pass


def main():
    ap = argparse.ArgumentParser(description="SC-16 deploy admission check (unprivileged).")
    ap.add_argument("--out", required=True, help="receipt directory (must not exist)")
    ap.add_argument("--kind", choices=["dry", "evidence"], required=True)
    ap.add_argument("--reps", type=int, default=5)
    ap.add_argument("--only", default=",".join(HYPS), help="comma list of hypotheses (dry runs only)")
    args = ap.parse_args()
    if os.geteuid() == 0:
        sys.exit("refusing to run as root: this harness is unprivileged by design")
    hyps = [h for h in args.only.split(",") if h]
    if any(h not in HYPS for h in hyps):
        sys.exit("unknown hypothesis in --only")
    if args.kind == "evidence" and (hyps != HYPS or args.reps != 5):
        sys.exit("evidence runs use all hypotheses and --reps 5 (prereg §4)")
    out = Path(args.out)
    if out.exists():
        sys.exit("refusing to overwrite existing --out %s" % out)
    if not out.parent.is_dir():
        sys.exit("parent of --out does not exist: %s" % out.parent)
    m = meta(args)
    problems = preflight(args, m)
    if args.kind == "evidence" and problems:
        sys.exit("refusing evidence run: " + "; ".join(problems))
    out.mkdir()
    (out / "logs").mkdir()
    m["started"] = datetime.datetime.utcnow().isoformat() + "Z"
    m["loadavg_start"] = os.getloadavg()
    t_start = time.monotonic()
    results, infra, aborted, ctx, residue = [], None, None, None, None
    if problems:
        infra = problems
    else:
        def on_alarm(signum, frame):
            raise WallLimit("wall limit %d s reached" % WALL_LIMIT)
        signal.signal(signal.SIGALRM, on_alarm)
        signal.alarm(WALL_LIMIT)
        try:
            ctx = Ctx()
            for rep in range(1, args.reps + 1):
                for h in hyps:
                    R = Rec(h, rep)
                    t = time.monotonic()
                    try:
                        H[h](ctx, out, rep, R)
                    except WallLimit:
                        R.error = traceback.format_exc()
                        results.append(R.as_dict())
                        raise
                    except Exception:
                        R.error = traceback.format_exc()
                    R.raw["elapsed_s"] = round(time.monotonic() - t, 3)
                    left = proc_scan(str(ctx.work))
                    R.raw["after"] = {"left_procs": left, "loadavg": os.getloadavg()}
                    results.append(R.as_dict())
                    print("%s rep %d: %s (%.1fs)" % (h, rep, "PASS" if R.passed() else "FAIL", R.raw["elapsed_s"]),
                          flush=True)
                    if left:
                        aborted = "residue after %s rep %d: %s" % (h, rep, left)
                        raise RuntimeError(aborted)
        except BaseException:
            aborted = aborted or traceback.format_exc()
        finally:
            signal.alarm(0)
            if ctx is not None:
                for f in sorted(ctx.logs.iterdir()):
                    shutil.copy2(str(f), str(out / "logs" / f.name))
                residue = proc_scan(str(ctx.work))
                for e in residue:
                    try:
                        os.kill(e["pid"], signal.SIGKILL)
                    except OSError:
                        pass
                shutil.rmtree(str(ctx.work), ignore_errors=True)
    m["finished"] = datetime.datetime.utcnow().isoformat() + "Z"
    m["wall_s"] = round(time.monotonic() - t_start, 2)
    m["loadavg_end"] = os.getloadavg()
    cleanup = {"residue_killed": residue, "workdir_removed": ctx is None or not ctx.work.exists()}
    per = {}
    for h in hyps:
        rs = [r for r in results if r["hyp"] == h]
        n_ok = sum(r["pass"] for r in rs)
        per[h] = {"reps": args.reps, "ran": len(rs), "passed": n_ok, "negative_control": h in CONTROLS,
                  "verdict": "NOT-RUN" if infra else "PASS" if len(rs) == args.reps and n_ok == args.reps else "FAIL"}
    verdicts = {"prereg_id": PREREG_ID, "kind": args.kind, "infra_error": infra, "aborted": aborted,
                "cleanup_ok": not residue and cleanup["workdir_removed"], "per_hypothesis": per,
                "calibration": m["calibration"]}
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
    print(json.dumps({"overall": verdicts["overall"], "per_hypothesis": per, "aborted": aborted, "infra": infra},
                     indent=1, default=str))
    return 0 if verdicts["overall"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
