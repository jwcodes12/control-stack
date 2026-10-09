#!/usr/bin/env python3
"""SC-07 egress quota check (root required). Preregistration: prereg/SC07-EGRESS-QUOTA.md (PREREG-SC07-EGRESSQ-v1).

Defensive operational test of an egress control: a trusted gateway namespace forwards a sandboxed job's traffic
only to an allowlisted destination and caps the bytes it forwards there with an nftables quota. Workloads are benign
(random-data uploads over plain TCP; one connection attempt to a non-allowlisted address). Checks, each repeated
--reps times on a freshly built topology (three new namespaces per hypothesis x repetition):

  H1 allowlist   : the job's connection to the non-allowlisted sink fails; that sink receives 0 bytes from the job
                   (its own count) although it is listening (gateway probe delivered) and the allowed sink works.
  H2 quota       : a 3x-quota upload to the allowed sink: sink receives <= quota + TOL_QUOTA and >= quota - TOL_LOW;
                   the gateway's forwarded-bytes counter and the sink's count agree within TOL_AGREE; quota drops seen.
  H3 usefulness  : a 0.5x-quota upload completes with byte-exact delivery (length and SHA-256 at the sink).
  H4 HALT        : HALT (forward chain flushed to drop-all) during a paced upload: sink bytes received after the
                   HALT took effect <= TOL_HALT; the upload does not complete; a later connection fails.
  H5 no bypass   : structural check of the job namespace (only lo + one veth whose peer is the gateway; every route
                   via the gateway; no IPv6; the job process is unprivileged in that namespace) and every byte the
                   sink receives from the job was counted by the gateway.
  H6 control     : with the quota rule removed (SC07_NEGATIVE_CONTROL=1, recorded), the same 3x upload is delivered
                   in full.

Receipts go to --out, which must not exist. Nothing creates accounts: UIDs are bare numbers set with setuid.
Python 3.9 compatible (runs under the system interpreter via sudo).
"""
import argparse
import datetime
import hashlib
import json
import os
import platform
import secrets
import select
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import traceback
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True  # never leave root-owned __pycache__ in the repo
sys.path.insert(0, str(HERE))
import gw  # noqa: E402

REPO = HERE.parents[2]
PREREG = REPO / "prereg" / "SC07-EGRESS-QUOTA.md"
PREREG_ID = "PREREG-SC07-EGRESSQ-v1"
UID_SINK, UID_JOB, UID_PROBE = 23801, 23802, 23803
ALL_UIDS = tuple(gw.UIDS)
HYPS = ["H1", "H2", "H3", "H4", "H5", "H6"]
KiB, MiB = 1024, 1024 * 1024

# Preregistered constants (§3 of the prereg). Changing any of them needs a new prereg ID.
QUOTA = 8 * MiB                      # nft quota object job_q: "over QUOTA bytes" (IP packet lengths, upload only)
H2_BYTES = 3 * QUOTA
H3_BYTES = QUOTA // 2
H6_BYTES = 3 * QUOTA
H4_BYTES = 6 * MiB                   # below the quota, so only HALT can stop it
H4_RATE = 4 * MiB                    # bytes/s, paced so the upload is in progress for ~1.5 s
H4_HALT_AT = 1 * MiB                 # HALT once the sink has received this many bytes from the job
SMALL_BYTES = 64 * KiB               # positive-control uploads in H1 and H5
PROBE_BYTES = 16                     # H1 liveness probe from the gateway to the non-allowlisted sink
TOL_QUOTA = 1500                     # H2: sink bytes <= QUOTA + TOL_QUOTA (one MTU)  [fixed from dry runs, §3.1]
TOL_LOW = 128 * KiB                  # H2: sink bytes >= QUOTA - TOL_LOW              [fixed from dry runs, §3.1]
TOL_AGREE = 64 * KiB                 # H2: |gateway fwd_up bytes - sink bytes| <= TOL_AGREE  [fixed, §3.1]
TOL_HALT = 128 * KiB                 # H4: sink bytes received after HALT took effect        [fixed, §3.1]
CONNECT_TIMEOUT = 1.0                # s
STALL_TIMEOUT = 1.0                  # s without send progress -> the job gives up
ACK_TIMEOUT = 3.0                    # s
JOB_DEADLINE = 8.0                   # s
SETTLE = 0.3                         # s after the job ends before the sink is stopped
READY_TIMEOUT = 5.0
WALL_LIMIT = 115                     # s, whole run
CONST_NAMES = ("QUOTA", "H2_BYTES", "H3_BYTES", "H6_BYTES", "H4_BYTES", "H4_RATE", "H4_HALT_AT", "SMALL_BYTES",
               "PROBE_BYTES", "TOL_QUOTA", "TOL_LOW", "TOL_AGREE", "TOL_HALT", "CONNECT_TIMEOUT", "STALL_TIMEOUT",
               "ACK_TIMEOUT", "JOB_DEADLINE", "SETTLE", "WALL_LIMIT")


# ---------------------------------------------------------------- independent /proc observation
def proc_scan(uids):
    out = []
    for d in os.listdir("/proc"):
        if not d.isdigit():
            continue
        try:
            with open("/proc/%s/status" % d) as fh:
                st = fh.read()
        except (FileNotFoundError, ProcessLookupError, PermissionError):
            continue
        uid = None
        for line in st.splitlines():
            if line.startswith("Uid:"):
                uid = int(line.split()[1])
                break
        if uid in uids:
            out.append(int(d))
    return out


def proc_status(pid):
    with open("/proc/%d/status" % pid) as fh:
        st = dict(l.split(":", 1) for l in fh.read().splitlines() if ":" in l)
    return {k: st[k].strip() for k in ("Uid", "Gid", "Groups", "CapInh", "CapPrm", "CapEff", "CapAmb", "NoNewPrivs")
            if k in st}


# ---------------------------------------------------------------- helpers
class Rec:
    def __init__(self, hyp, rep):
        self.hyp, self.rep = hyp, rep
        self.checks, self.raw, self.error = [], {}, None

    def check(self, name, expected, observed, ok):
        self.checks.append({"name": name, "expected": expected, "observed": observed, "pass": bool(ok)})

    def passed(self):
        return self.error is None and bool(self.checks) and all(c["pass"] for c in self.checks)

    def as_dict(self):
        return {"hyp": self.hyp, "rep": self.rep, "pass": self.passed(), "error": self.error,
                "checks": self.checks, "raw": self.raw}


class Ctx:
    def __init__(self):
        self.token = secrets.token_hex(3)
        self.work = Path(tempfile.mkdtemp(prefix="sc07-run-", dir="/var/tmp"))
        self.work.chmod(0o755)
        code = self.work / "code"
        code.mkdir(mode=0o755)
        for f in ("sink.py", "job.py"):
            shutil.copy2(str(HERE / f), str(code / f))
            (code / f).chmod(0o644)
        self.code = code
        self.logs = self.work / "logs"
        self.logs.mkdir(mode=0o755)
        self.py = sys.executable
        self.n = 0

    def argv(self, script, *args):
        return [self.py, "-I", "-S", str(self.code / script)] + [str(a) for a in args]

    def log(self, tag):
        self.n += 1
        return open(str(self.logs / ("%03d-%s.stderr" % (self.n, tag))), "wb")

    def state_dir(self, tag):
        d = self.work / ("state-" + tag)
        d.mkdir(mode=0o755)
        os.chown(str(d), UID_SINK, UID_SINK)
        return d


def read_line(p, timeout):
    fd, buf, t0 = p.stdout.fileno(), b"", time.monotonic()
    while b"\n" not in buf:
        rem = timeout - (time.monotonic() - t0)
        if rem <= 0:
            raise TimeoutError("no output line within %.1fs from pid %d" % (timeout, p.pid))
        r, _, _ = select.select([fd], [], [], rem)
        if not r:
            continue
        chunk = os.read(fd, 65536)
        if not chunk:
            raise RuntimeError("EOF before output line from pid %d (rc=%s)" % (p.pid, p.poll()))
        buf += chunk
    return buf.split(b"\n", 1)[0].decode()


def read_ready(p, timeout=READY_TIMEOUT):
    line = read_line(p, timeout)
    if not line.startswith("READY "):
        raise RuntimeError("unexpected output: %r" % line)
    return json.loads(line[6:])


class Sinks:
    """Both sink processes (allowed and not-allowlisted) in the sink namespace, run as UID_SINK."""

    def __init__(self, ctx, T, tag):
        self.T, self.dir = T, ctx.state_dir(tag)
        self.p, self.state = {}, {}
        for label, ip in (("allowed", gw.SINK_ALLOWED), ("denied", gw.SINK_DENIED)):
            st = self.dir / ("%s.json" % label)
            with ctx.log("%s-sink-%s" % (tag, label)) as lf:
                self.p[label] = T.spawn("sink", UID_SINK, ctx.argv("sink.py", "--bind", ip, "--port", gw.SINK_PORT,
                                                                   "--state", st, "--label", label), stderr=lf)
            self.state[label] = st
        self.ready = {k: read_ready(p) for k, p in self.p.items()}

    def peek(self, label):
        try:
            return json.loads(self.state[label].read_text())
        except (FileNotFoundError, ValueError):
            return None

    def stop(self):
        for p in self.p.values():
            if p.poll() is None:
                p.send_signal(signal.SIGTERM)
        out = {}
        for k, p in self.p.items():
            try:
                p.wait(timeout=3)
            except subprocess.TimeoutExpired:
                p.kill()
            s = self.peek(k)
            out[k] = s
        return out


def from_peer(state, ip):
    """Connections and bytes the sink recorded from peer ip (the sink's own count)."""
    if state is None:
        return {"conns": [], "n": 0, "bytes": 0}
    cs = [c for c in state["conns"] if c["peer"].split(":")[0] == ip]
    return {"conns": cs, "n": len(cs), "bytes": sum(c["bytes"] for c in cs)}


def strip_timeline(state):
    if state is None:
        return None
    s = json.loads(json.dumps(state))
    for c in s["conns"]:
        tl = c.pop("timeline", None)
        c["timeline_len"] = None if tl is None else len(tl)
    return s


def run_job(ctx, T, tag, uid=UID_JOB, role="job", dst=gw.SINK_ALLOWED, nbytes=SMALL_BYTES, rate=0, wait=True):
    with ctx.log(tag) as lf:
        p = T.spawn(role, uid, ctx.argv("job.py", "upload", "--dst", dst, "--port", gw.SINK_PORT, "--bytes", nbytes,
                                        "--rate", rate, "--connect-timeout", CONNECT_TIMEOUT, "--stall-timeout",
                                        STALL_TIMEOUT, "--ack-timeout", ACK_TIMEOUT, "--deadline", JOB_DEADLINE),
                    stderr=lf)
    return finish_job(p) if wait else p


def finish_job(p, timeout=JOB_DEADLINE + ACK_TIMEOUT + 2):
    line = read_line(p, timeout)
    p.wait(timeout=3)
    r = json.loads(line)
    r["rc"] = p.returncode
    return r


def quota_refs(node, path="$"):
    """Every quota object or quota statement anywhere in an `nft -j list ruleset` document."""
    out = []
    if isinstance(node, dict):
        for k, v in node.items():
            if k == "quota":
                out.append(path + ".quota")
            out += quota_refs(v, path + "." + k)
    elif isinstance(node, list):
        for i, v in enumerate(node):
            out += quota_refs(v, "%s[%d]" % (path, i))
    return out


def new_topology(ctx, tag, quota):
    T = gw.Topology(ctx.token, tag)
    return T, T.up(quota)


# ---------------------------------------------------------------- hypotheses
def h1(ctx, rep, R):
    T, setup = new_topology(ctx, "h1r%d" % rep, QUOTA)
    R.raw["setup"] = setup
    try:
        S = Sinks(ctx, T, "h1r%d" % rep)
        job = run_job(ctx, T, "h1-job-denied", dst=gw.SINK_DENIED, nbytes=H3_BYTES)
        c_after_job = T.counters()
        probe = run_job(ctx, T, "h1-gw-probe", uid=UID_PROBE, role="gw", dst=gw.SINK_DENIED, nbytes=PROBE_BYTES)
        ok_small = run_job(ctx, T, "h1-job-allowed", dst=gw.SINK_ALLOWED, nbytes=SMALL_BYTES)
        time.sleep(SETTLE)
        st = S.stop()
        den_job = from_peer(st["denied"], gw.JOB_IP)
        den_gw = from_peer(st["denied"], gw.GW_SINK_IP)
        R.raw.update(job_denied=job, gw_probe=probe, job_allowed=ok_small, counters_after_job=c_after_job,
                     counters=T.counters(), sinks={k: strip_timeline(v) for k, v in st.items()})
        R.check("job connection to non-allowlisted %s:%d fails" % (gw.SINK_DENIED, gw.SINK_PORT), False,
                {"connected": job["connected"], "error": job["connect_error"]}, not job["connected"])
        R.check("non-allowlisted sink: bytes and connections from the job (its own count)", [0, 0],
                [den_job["bytes"], den_job["n"]], den_job["bytes"] == 0 and den_job["n"] == 0)
        R.check("gateway deny_drop counter saw the attempt (packets >= 1)", ">= 1",
                c_after_job["deny_drop"]["packets"], c_after_job["deny_drop"]["packets"] >= 1)
        R.check("gateway forwarded nothing upstream for the denied attempt (fwd_up packets)", 0,
                c_after_job["fwd_up"]["packets"], c_after_job["fwd_up"]["packets"] == 0)
        R.check("liveness: non-allowlisted sink listening (gateway probe delivered %d bytes)" % PROBE_BYTES,
                PROBE_BYTES, den_gw["bytes"], probe["completed"] and den_gw["bytes"] == PROBE_BYTES)
        R.check("positive control: %d-byte upload to the allowed sink completes" % SMALL_BYTES, True,
                ok_small["completed"], ok_small["completed"])
    finally:
        R.raw["cleanup"] = T.close()


def h2(ctx, rep, R):
    T, setup = new_topology(ctx, "h2r%d" % rep, QUOTA)
    R.raw["setup"] = setup
    try:
        S = Sinks(ctx, T, "h2r%d" % rep)
        job = run_job(ctx, T, "h2-job", nbytes=H2_BYTES)
        time.sleep(SETTLE)
        st = S.stop()
        c, q = T.counters(), T.quotas()
        a = from_peer(st["allowed"], gw.JOB_IP)
        d = from_peer(st["denied"], gw.JOB_IP)
        R.raw.update(job=job, counters=c, quotas=q, sinks={k: strip_timeline(v) for k, v in st.items()})
        sink_b, fwd = a["bytes"], c["fwd_up"]["bytes"]
        R.raw["derived"] = {"sink_minus_quota": sink_b - QUOTA, "fwd_up_minus_sink": fwd - sink_b,
                            "fwd_up_minus_quota": fwd - QUOTA, "fwd_up_packets": c["fwd_up"]["packets"],
                            "quota_drop_packets": c["quota_drop"]["packets"]}
        jq = q.get("job_q") or {}
        qrefs = quota_refs(T.ruleset_json())
        R.check("ruleset: quota object job_q 'over %d bytes' and a quota statement present" % QUOTA,
                {"bytes": QUOTA, "inv": True, "refs": ">= 2"}, {"bytes": jq.get("bytes"), "inv": jq.get("inv"),
                                                               "refs": len(qrefs)},
                jq.get("bytes") == QUOTA and jq.get("inv") is True and len(qrefs) >= 2)
        R.check("upload of 3x quota did not complete", False, job["completed"], not job["completed"])
        R.check("sink bytes from job <= quota + TOL_QUOTA", "<= %d" % (QUOTA + TOL_QUOTA), sink_b,
                sink_b <= QUOTA + TOL_QUOTA)
        R.check("sink bytes from job >= quota - TOL_LOW (quota was reached, not a stall elsewhere)",
                ">= %d" % (QUOTA - TOL_LOW), sink_b, sink_b >= QUOTA - TOL_LOW)
        R.check("gateway fwd_up bytes and sink count agree within TOL_AGREE", "|diff| <= %d" % TOL_AGREE,
                {"fwd_up": fwd, "sink": sink_b, "diff": fwd - sink_b}, abs(fwd - sink_b) <= TOL_AGREE)
        R.check("gateway quota_drop counter >= 1 packet (quota was binding)", ">= 1", c["quota_drop"]["packets"],
                c["quota_drop"]["packets"] >= 1)
        R.check("non-allowlisted sink received nothing from the job", 0, d["bytes"], d["bytes"] == 0)
    finally:
        R.raw["cleanup"] = T.close()


def h3(ctx, rep, R):
    T, setup = new_topology(ctx, "h3r%d" % rep, QUOTA)
    R.raw["setup"] = setup
    try:
        S = Sinks(ctx, T, "h3r%d" % rep)
        job = run_job(ctx, T, "h3-job", nbytes=H3_BYTES)
        time.sleep(SETTLE)
        st = S.stop()
        c = T.counters()
        a = from_peer(st["allowed"], gw.JOB_IP)
        R.raw.update(job=job, counters=c, quotas=T.quotas(), sinks={k: strip_timeline(v) for k, v in st.items()})
        conn = a["conns"][0] if a["n"] == 1 else None
        R.check("job completed (ack OK <bytes> <sha256> received and matching)", True, job["completed"],
                job["completed"])
        R.check("sink recorded exactly one connection from the job", 1, a["n"], a["n"] == 1)
        R.check("sink byte count == uploaded bytes", H3_BYTES, conn and conn["bytes"],
                conn is not None and conn["bytes"] == H3_BYTES)
        R.check("sink SHA-256 == job SHA-256", job["sha256"], conn and conn["sha256"],
                conn is not None and conn["sha256"] == job["sha256"])
        R.check("sink connection ended by EOF with ack sent", ["eof", True], conn and [conn["closed"], conn["ack_sent"]],
                conn is not None and conn["closed"] == "eof" and conn["ack_sent"])
        R.check("no quota drops for an under-quota upload", 0, c["quota_drop"]["packets"],
                c["quota_drop"]["packets"] == 0)
    finally:
        R.raw["cleanup"] = T.close()


def h4(ctx, rep, R):
    T, setup = new_topology(ctx, "h4r%d" % rep, QUOTA)
    R.raw["setup"] = setup
    try:
        S = Sinks(ctx, T, "h4r%d" % rep)
        p = run_job(ctx, T, "h4-job", nbytes=H4_BYTES, rate=H4_RATE, wait=False)
        t0, seen = time.monotonic(), 0
        while time.monotonic() - t0 < 5.0:
            seen = from_peer(S.peek("allowed"), gw.JOB_IP)["bytes"]
            if seen >= H4_HALT_AT or p.poll() is not None:
                break
            time.sleep(0.005)
        job_running = p.poll() is None
        c_before = T.counters()
        h = T.halt()
        c_halt = T.counters()
        job = finish_job(p)
        c_mid = T.counters()
        later = run_job(ctx, T, "h4-job-after-halt", nbytes=SMALL_BYTES)
        time.sleep(SETTLE)
        st = S.stop()
        c_end = T.counters()
        a = from_peer(st["allowed"], gw.JOB_IP)
        rs = T.ruleset_json()
        conn = a["conns"][0] if a["conns"] else None
        tl = conn["timeline"] if conn else []

        def received_by(t):
            b = 0
            for tt, cum in tl:
                if tt <= t:
                    b = cum
            return b
        after_end = a["bytes"] - received_by(h["t_end"])
        after_start = a["bytes"] - received_by(h["t_start"])
        fwd_rules = [e["rule"] for e in rs["nftables"] if "rule" in e and e["rule"]["chain"] == "forward"]
        fwd_chain = [e["chain"] for e in rs["nftables"] if "chain" in e and e["chain"]["name"] == "forward"][0]
        R.raw.update(halt=h, seen_at_halt=seen, job=job, later=later, counters_before=c_before, counters_halt=c_halt,
                     counters_mid=c_mid, counters_end=c_end, ruleset_after=rs,
                     sinks={k: strip_timeline(v) for k, v in st.items()},
                     derived={"after_halt_end": after_end, "after_halt_start": after_start,
                              "sink_total": a["bytes"], "halt_latency_s": h["latency_s"]},
                     timeline_near_halt=[e for e in tl if h["t_start"] - 0.1 <= e[0] <= h["t_end"] + 0.5])
        R.check("precondition: upload in progress at HALT (job running, sink saw >= %d bytes, < total)"
                % H4_HALT_AT, True, {"job_running": job_running, "seen": seen},
                job_running and H4_HALT_AT <= seen < H4_BYTES)
        R.check("sink bytes received after HALT took effect <= TOL_HALT", "<= %d" % TOL_HALT,
                {"after_end": after_end, "after_start": after_start}, after_end <= TOL_HALT)
        R.check("upload did not complete; sink total < upload size", [False, "< %d" % H4_BYTES],
                [job["completed"], a["bytes"]], not job["completed"] and a["bytes"] < H4_BYTES)
        R.check("gateway forwarded no upload bytes after HALT (fwd_up unchanged)", c_halt["fwd_up"],
                c_end["fwd_up"], c_end["fwd_up"] == c_halt["fwd_up"])
        R.check("gateway halt_drop counter >= 1 (upload traffic dropped after HALT)", ">= 1",
                c_end["halt_drop"]["packets"], c_end["halt_drop"]["packets"] >= 1)
        R.check("connection after HALT fails; sink saw no new connection from the job", [False, 1],
                [later["connected"], a["n"]], not later["connected"] and a["n"] == 1)
        R.check("forward chain after HALT: policy drop, only the halt_drop rule", ["drop", 1],
                [fwd_chain.get("policy"), len(fwd_rules)], fwd_chain.get("policy") == "drop" and len(fwd_rules) == 1)
    finally:
        R.raw["cleanup"] = T.close()


def h5(ctx, rep, R):
    T, setup = new_topology(ctx, "h5r%d" % rep, QUOTA)
    R.raw["setup"] = setup
    hold = None
    try:
        job_ns = T.ns["job"]
        links = json.loads(T.ip("job", "-j", "-d", "link", "show").stdout)
        gw_links = json.loads(T.ip("gw", "-j", "link", "show").stdout)
        routes = json.loads(T.ip("job", "-j", "route", "show", "table", "all").stdout)
        rules = json.loads(T.ip("job", "-j", "rule", "show").stdout)
        addr6 = json.loads(T.ip("job", "-6", "-j", "addr", "show").stdout or "[]")
        rget = {ip: json.loads(T.ip("job", "-j", "route", "get", ip).stdout) for ip in (gw.SINK_ALLOWED,
                                                                                     gw.SINK_DENIED)}
        R.raw.update(job_links=links, job_routes=routes, job_rules=rules, job_addr6=addr6, route_get=rget,
                     gw_links=[{k: l.get(k) for k in ("ifindex", "ifname")} for l in gw_links])
        names = sorted(l["ifname"] for l in links)
        R.check("job namespace interfaces are exactly lo + one veth", ["lo", gw.IF_JOB], names,
                names == sorted(["lo", gw.IF_JOB]))
        vj = [l for l in links if l["ifname"] == gw.IF_JOB]
        kind = vj and vj[0].get("linkinfo", {}).get("info_kind")
        peer_idx = vj and vj[0].get("link_index")
        gw_peer = [l["ifname"] for l in gw_links if l["ifindex"] == peer_idx]
        has_netnsid = bool(vj) and "link_netnsid" in vj[0]
        R.check("the veth's peer is the gateway's job-side interface (in another namespace)",
                {"kind": "veth", "peer": gw.IF_GW_JOB, "peer_in_other_ns": True},
                {"kind": kind, "peer": gw_peer, "peer_in_other_ns": has_netnsid},
                kind == "veth" and gw_peer == [gw.IF_GW_JOB] and has_netnsid)
        nonlocal_ = [r for r in routes if r.get("table") != "local"]
        bad = [r for r in nonlocal_ if r.get("dev") != gw.IF_JOB or (r.get("gateway") not in (None, gw.GW_JOB_IP))]
        default = [r for r in nonlocal_ if r.get("dst") == "default"]
        R.check("every non-local route uses the veth; the only gateway is %s" % gw.GW_JOB_IP, [], bad, not bad)
        R.check("exactly one default route, via the gateway", [{"gateway": gw.GW_JOB_IP, "dev": gw.IF_JOB}],
                [{"gateway": r.get("gateway"), "dev": r.get("dev")} for r in default],
                len(default) == 1 and default[0].get("gateway") == gw.GW_JOB_IP)
        local_bad = [r for r in routes if r.get("table") == "local" and r.get("dev") not in ("lo", gw.IF_JOB)]
        R.check("local-table routes only on lo / the veth", [], local_bad, not local_bad)
        prio = sorted(r.get("priority") for r in rules)
        R.check("policy routing rules are the defaults (0 local, 32766 main, 32767 default)", [0, 32766, 32767],
                prio, prio == [0, 32766, 32767])
        R.check("no IPv6 address in the job namespace", 0, sum(len(a.get("addr_info", [])) for a in addr6),
                sum(len(a.get("addr_info", [])) for a in addr6) == 0)
        rg = {ip: [(r.get("gateway"), r.get("dev")) for r in v] for ip, v in rget.items()}
        R.check("route lookup to both sink addresses goes via the gateway",
                {ip: [[gw.GW_JOB_IP, gw.IF_JOB]] for ip in rget}, rg,
                all(v == [(gw.GW_JOB_IP, gw.IF_JOB)] for v in rg.values()))
        # The job process: right namespace, unprivileged.
        with ctx.log("h5-hold") as lf:
            hold = T.spawn("job", UID_JOB, ctx.argv("job.py", "hold", "--lifetime", 10), stdin=subprocess.PIPE,
                           stderr=lf)
        hr = read_ready(hold)
        pst = proc_status(hr["pid"])
        pns = os.stat("/proc/%d/ns/net" % hr["pid"]).st_ino
        R.raw.update(job_proc=pst, job_proc_netns=pns, job_netns=gw.ns_inode(job_ns))
        uids = pst["Uid"].split()
        R.check("job process runs in the job namespace", gw.ns_inode(job_ns), pns, pns == gw.ns_inode(job_ns))
        R.check("job process: uid %d (real/eff/saved/fs), CapEff=CapPrm=CapAmb=0, NoNewPrivs=1" % UID_JOB,
                {"uid": [str(UID_JOB)] * 4, "CapEff": 0, "CapPrm": 0, "CapAmb": 0, "NoNewPrivs": "1"},
                pst, uids == [str(UID_JOB)] * 4 and int(pst["CapEff"], 16) == 0 and int(pst["CapPrm"], 16) == 0
                and int(pst.get("CapAmb", "0"), 16) == 0 and pst.get("NoNewPrivs") == "1")
        hold.stdin.close()
        hold.wait(timeout=3)
        # Behavioural cross-check: every byte the sink got from the job crossed the gateway's counted rule.
        S = Sinks(ctx, T, "h5r%d" % rep)
        job = run_job(ctx, T, "h5-job", nbytes=SMALL_BYTES)
        time.sleep(SETTLE)
        st = S.stop()
        c = T.counters()
        a = from_peer(st["allowed"], gw.JOB_IP)
        R.raw.update(job=job, counters=c, sinks={k: strip_timeline(v) for k, v in st.items()})
        R.check("small upload completed and gateway fwd_up bytes >= sink bytes from the job",
                {"completed": True, "fwd_up>=sink": True}, {"completed": job["completed"], "fwd_up":
                                                             c["fwd_up"]["bytes"], "sink": a["bytes"]},
                job["completed"] and a["bytes"] == SMALL_BYTES and c["fwd_up"]["bytes"] >= a["bytes"])
    finally:
        if hold is not None and hold.poll() is None:
            hold.kill()
        R.raw["cleanup"] = T.close()


def h6(ctx, rep, R):
    os.environ["SC07_NEGATIVE_CONTROL"] = "1"
    try:
        T, setup = new_topology(ctx, "h6r%d" % rep, None)
    finally:
        os.environ.pop("SC07_NEGATIVE_CONTROL", None)
    R.raw["SC07_NEGATIVE_CONTROL"] = "1"
    R.raw["setup"] = setup
    try:
        S = Sinks(ctx, T, "h6r%d" % rep)
        job = run_job(ctx, T, "h6-job", nbytes=H6_BYTES)
        time.sleep(SETTLE)
        st = S.stop()
        c, q = T.counters(), T.quotas()
        a = from_peer(st["allowed"], gw.JOB_IP)
        R.raw.update(job=job, counters=c, quotas=q, sinks={k: strip_timeline(v) for k, v in st.items()})
        conn = a["conns"][0] if a["n"] == 1 else None
        qrefs = quota_refs(T.ruleset_json())
        R.check("control flagged and ruleset has no quota (no quota object, no quota statement)", [True, {}, []],
                [R.raw["SC07_NEGATIVE_CONTROL"] == "1", q, qrefs],
                R.raw["SC07_NEGATIVE_CONTROL"] == "1" and not q and not qrefs)
        R.check("3x-quota upload completes", True, job["completed"], job["completed"])
        R.check("sink bytes == 3x quota, SHA-256 match", [H6_BYTES, job["sha256"]],
                conn and [conn["bytes"], conn["sha256"]],
                conn is not None and conn["bytes"] == H6_BYTES and conn["sha256"] == job["sha256"])
        R.check("delivered bytes exceed what the quota admits (> quota + TOL_QUOTA)", "> %d" % (QUOTA + TOL_QUOTA),
                a["bytes"], a["bytes"] > QUOTA + TOL_QUOTA)
    finally:
        R.raw["cleanup"] = T.close()


H = {"H1": h1, "H2": h2, "H3": h3, "H4": h4, "H5": h5, "H6": h6}


# ---------------------------------------------------------------- receipt
def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def git(*args):
    r = subprocess.run(["git", "-c", "safe.directory=%s" % REPO, "-C", str(REPO)] + list(args),
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True)
    return r.stdout.strip() if r.returncode == 0 else "ERROR: " + r.stderr.strip()


def tracked_files():
    return sorted(HERE.glob("*.py")) + [HERE / "README.md", PREREG]


HOST_SYSCTLS = ("net.ipv4.ip_forward", "net.ipv6.conf.all.disable_ipv6", "net.ipv6.conf.default.disable_ipv6",
                "net.ipv6.conf.all.forwarding")


def host_snapshot():
    """Read-only view of the host network namespace (the runner's own)."""
    def h(argv):
        r = gw.run(argv, check=False)
        return hashlib.sha256(r.stdout.encode()).hexdigest() if r.returncode == 0 else "ERROR"
    sysctls = {}
    for k in HOST_SYSCTLS:
        try:
            sysctls[k] = Path("/proc/sys/" + k.replace(".", "/")).read_text().strip()
        except OSError:
            sysctls[k] = None
    return {"links": gw.host_links(), "sysctls": sysctls,
            "routes4_sha256": h(["ip", "-4", "route", "show", "table", "all"]),
            "routes6_sha256": h(["ip", "-6", "route", "show", "table", "all"]),
            "nft_ruleset_stateless_sha256": h(["nft", "-s", "list", "ruleset"]),
            "netns": gw.list_netns()}


def meta(args):
    rel = [str(p.relative_to(REPO)) for p in tracked_files()]
    return {
        "prereg_id": PREREG_ID,
        "kind": args.kind,
        "argv": sys.argv,
        "git_commit": git("rev-parse", "HEAD"),
        "git_branch": git("rev-parse", "--abbrev-ref", "HEAD"),
        "git_status_harness_and_prereg": git("status", "--porcelain", "--untracked-files=all", "--", *rel),
        "git_dirty_any": bool(git("status", "--porcelain")),
        "sha256": {str(p.relative_to(REPO)): sha(p) for p in tracked_files() if p.exists()},
        "uname_r": platform.release(),
        "uname_a": " ".join(platform.uname()),
        "python": sys.version,
        "python_executable": sys.executable,
        "nft_version": gw.run(["nft", "--version"], check=False).stdout.strip(),
        "ip_version": gw.run(["ip", "-V"], check=False).stdout.strip(),
        "nproc": os.cpu_count(),
        "uids": {"sink": UID_SINK, "job": UID_JOB, "probe": UID_PROBE, "reserved_range": [ALL_UIDS[0],
                                                                                          ALL_UIDS[-1]]},
        "addresses": {"job": gw.JOB_IP, "gw_job": gw.GW_JOB_IP, "gw_sink": gw.GW_SINK_IP,
                      "sink_allowed": gw.SINK_ALLOWED, "sink_denied": gw.SINK_DENIED, "port": gw.SINK_PORT},
        "ruleset_with_quota": gw.ruleset(QUOTA),
        "halt_script": gw.HALT_SCRIPT,
        "constants": {k: globals()[k] for k in CONST_NAMES},
        "env_SC07_NEGATIVE_CONTROL_at_start": os.environ.get("SC07_NEGATIVE_CONTROL"),
    }


def ours(names, token=None):
    return [n for n in names if n.startswith(gw.PREFIX) and (token is None or n.startswith(gw.PREFIX + token))]


def preflight():
    problems = []
    if os.geteuid() != 0:
        problems.append("must run as root")
    for tool in ("ip", "nft", "ss", "sysctl"):
        if not shutil.which(tool, path=gw.ENV["PATH"]):
            problems.append("missing tool: %s" % tool)
    if problems:
        return problems
    if ours(gw.list_netns()):
        problems.append("sc07- namespaces already exist (stale run? use --cleanup-stale): %s"
                        % ours(gw.list_netns()))
    if [l for l in gw.host_links() if l.startswith("sc07")]:
        problems.append("host has sc07* interfaces")
    stale = proc_scan(set(ALL_UIDS))
    if stale:
        problems.append("processes already running under reserved UIDs: %s" % stale)
    if os.environ.get("SC07_NEGATIVE_CONTROL"):
        problems.append("SC07_NEGATIVE_CONTROL must not be set at start (H6 sets it locally)")
    return problems


def cleanup_all(token=None):
    """Kill reserved-UID processes, delete our sc07- namespaces (only this run's token when given)."""
    rep = {"killed": [], "deleted": [], "errors": []}
    for pid in proc_scan(set(ALL_UIDS)):
        try:
            os.kill(pid, signal.SIGKILL)
            rep["killed"].append(pid)
        except ProcessLookupError:
            pass
    time.sleep(0.1)
    for n in ours(gw.list_netns(), token):
        r = gw.run(["ip", "netns", "pids", n], check=False)
        ino = os.stat(str(gw.NETNS_DIR / n)).st_ino
        for pid in [int(x) for x in r.stdout.split()]:
            try:
                if os.stat("/proc/%d/ns/net" % pid).st_ino == ino:
                    os.kill(pid, signal.SIGKILL)
                    rep["killed"].append(pid)
            except (FileNotFoundError, ProcessLookupError):
                pass
        r = gw.run(["ip", "netns", "del", n], check=False)
        (rep["deleted"] if r.returncode == 0 else rep["errors"]).append(n if r.returncode == 0 else
                                                                        "%s: %s" % (n, r.stderr.strip()))
    rep["left_netns"] = ours(gw.list_netns())
    rep["left_procs"] = proc_scan(set(ALL_UIDS))
    rep["host_sc07_links"] = [l for l in gw.host_links() if l.startswith("sc07")]
    return rep


def summary_md(m, verdicts, results):
    lines = ["# SC-07 egress quota run (%s, %s)" % (m["kind"], m["prereg_id"]), "",
             "- commit: `%s` (harness/prereg status: `%s`)" % (m["git_commit"], m["git_status_harness_and_prereg"]
                                                              or "clean"),
             "- kernel: `%s`, python `%s`, %s" % (m["uname_r"], m["python"].split()[0], m["nft_version"]),
             "- started %s, finished %s, wall %.1f s" % (m["started"], m["finished"], m["wall_s"]),
             "- host unchanged: %s" % json.dumps(verdicts.get("host_unchanged")),
             "- overall: **%s**" % verdicts["overall"], "",
             "| hypothesis | reps passed | verdict |", "|---|---|---|"]
    for h in HYPS:
        if h in verdicts["per_hypothesis"]:
            v = verdicts["per_hypothesis"][h]
            lines.append("| %s | %d/%d | %s |" % (h, v["passed"], v["reps"], v["verdict"]))
    lines += ["", "## Key measurements per repetition", ""]
    for r in results:
        d = r["raw"].get("derived")
        if d:
            lines.append("- %s rep %d: %s" % (r["hyp"], r["rep"], json.dumps(d, sort_keys=True)))
    lines += ["", "## Failed checks", ""]
    bad = [(r["hyp"], r["rep"], c) for r in results for c in r["checks"] if not c["pass"]]
    errs = [(r["hyp"], r["rep"], r["error"]) for r in results if r["error"]]
    for h, rp, c in bad:
        lines.append("- %s rep %d: %s — expected %s, observed %s" % (h, rp, c["name"], json.dumps(c["expected"]),
                                                                   json.dumps(c["observed"], default=str)))
    for h, rp, e in errs:
        lines.append("- %s rep %d: ERROR %s" % (h, rp, e.splitlines()[-1] if e else e))
    if not bad and not errs:
        lines.append("none")
    return "\n".join(lines) + "\n"


class WallLimit(Exception):
    pass


def main():
    ap = argparse.ArgumentParser(description="SC-07 egress quota check (root).")
    ap.add_argument("--out", required=True, help="receipt directory (must not exist)")
    ap.add_argument("--kind", choices=["dry", "evidence"], required=True)
    ap.add_argument("--reps", type=int, default=5)
    ap.add_argument("--only", default=",".join(HYPS), help="comma list of hypotheses (dry runs only)")
    ap.add_argument("--cleanup-stale", action="store_true", help="only remove stale sc07- namespaces and exit")
    args = ap.parse_args()
    if args.cleanup_stale:
        print(json.dumps(cleanup_all(), indent=1, default=str))
        return 0
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
    out.mkdir()
    (out / "logs").mkdir()
    m = meta(args)
    m["started"] = datetime.datetime.utcnow().isoformat() + "Z"
    m["loadavg_start"] = os.getloadavg()
    t_start = time.monotonic()
    results, cleanup, infra, aborted, host_before, host_after = [], None, None, None, None, None
    problems = preflight()
    if args.kind == "evidence" and m["git_status_harness_and_prereg"]:
        problems.append("evidence run needs committed, unmodified harness and prereg files")
    ctx = None
    if problems:
        infra = problems
    else:
        host_before = host_snapshot()

        def on_alarm(signum, frame):
            raise WallLimit("wall limit %d s reached" % WALL_LIMIT)
        signal.signal(signal.SIGALRM, on_alarm)
        signal.alarm(WALL_LIMIT)
        try:
            ctx = Ctx()
            m["run_token"] = ctx.token
            for f in ("sink.py", "job.py"):
                m["sha256"]["<workdir>/code/" + f] = sha(ctx.code / f)
            for rep in range(1, args.reps + 1):
                for h in hyps:
                    R = Rec(h, rep)
                    t = time.monotonic()
                    try:
                        H[h](ctx, rep, R)
                    except WallLimit:
                        R.error = traceback.format_exc()
                        results.append(R.as_dict())
                        raise
                    except Exception:
                        R.error = traceback.format_exc()
                    R.raw["elapsed_s"] = round(time.monotonic() - t, 3)
                    # Stop rule: nothing of ours may survive a hypothesis.
                    left_p = proc_scan(set(ALL_UIDS))
                    left_n = ours(gw.list_netns())
                    left_l = [l for l in gw.host_links() if l.startswith("sc07")]
                    R.raw["after"] = {"left_procs": left_p, "left_netns": left_n, "host_sc07_links": left_l}
                    results.append(R.as_dict())
                    print("%s rep %d: %s (%.1fs)" % (h, rep, "PASS" if R.passed() else "FAIL",
                                                      R.raw["elapsed_s"]), flush=True)
                    if left_p or left_n or left_l:
                        aborted = "residue after %s rep %d: procs %s netns %s links %s" % (h, rep, left_p, left_n,
                                                                                         left_l)
                        raise RuntimeError(aborted)
        except Exception:
            aborted = aborted or traceback.format_exc()
        finally:
            signal.alarm(0)
            cleanup = cleanup_all(ctx.token if ctx else None)
            if ctx is not None:
                for f in sorted(ctx.logs.iterdir()):
                    shutil.copy2(str(f), str(out / "logs" / f.name))
                shutil.rmtree(str(ctx.work), ignore_errors=True)
            host_after = host_snapshot()
    m["finished"] = datetime.datetime.utcnow().isoformat() + "Z"
    m["wall_s"] = round(time.monotonic() - t_start, 2)
    m["loadavg_end"] = os.getloadavg()
    m["host_before"], m["host_after"] = host_before, host_after
    per = {}
    for h in hyps:
        rs = [r for r in results if r["hyp"] == h]
        n_ok = sum(r["pass"] for r in rs)
        complete = len(rs) == args.reps
        per[h] = {"reps": args.reps, "ran": len(rs), "passed": n_ok,
                  "verdict": "NOT-RUN" if infra else "PASS" if complete and n_ok == args.reps else "FAIL"}
    host_unchanged = None
    if host_before and host_after:
        host_unchanged = {k: host_before[k] == host_after[k] for k in host_before}
    verdicts = {"prereg_id": PREREG_ID, "kind": args.kind, "infra_error": infra, "aborted": aborted,
                "cleanup_ok": cleanup is None or (not cleanup["left_netns"] and not cleanup["left_procs"]
                                                  and not cleanup["host_sc07_links"]),
                "host_unchanged": host_unchanged,
                "host_required_ok": host_unchanged is None or (host_unchanged["sysctls"] and host_unchanged["netns"]),
                "per_hypothesis": per}
    verdicts["overall"] = ("INFRA-ERROR" if infra else
                           "PASS" if not aborted and verdicts["cleanup_ok"] and verdicts["host_required_ok"] and all(
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
    print(json.dumps({"overall": verdicts["overall"], "per_hypothesis": per, "aborted": aborted, "infra": infra,
                      "host_unchanged": host_unchanged}, indent=1, default=str))
    return 0 if verdicts["overall"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
