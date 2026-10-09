#!/usr/bin/env python3
"""SC-07 trusted egress gateway: network namespaces, veths, nftables allowlist + per-job byte quota + HALT (root).

Topology (one instance per hypothesis x repetition, all names unique and prefixed "sc07-"):

    netns sc07-<tok>-<tag>-job          netns sc07-<tok>-<tag>-gw                  netns sc07-<tok>-<tag>-sink
    sc07j 10.207.1.2/24  <== veth ==>   sc07gj 10.207.1.1/24
    default via 10.207.1.1              sc07gs 10.207.2.1/24  <== veth ==>        sc07s 10.207.2.10/24 (allowed sink)
                                        ip_forward=1, nftables table inet sc07          10.207.2.20/24 (not allowlisted)
                                                                                  default via 10.207.2.1

The gateway's forward chain (policy drop) forwards only job 10.207.1.2 -> 10.207.2.10 tcp/8080 (and the return
direction 10.207.2.10:8080 -> job). The upload direction passes a named nftables quota object `job_q`
(`over QUOTA bytes`): once the quota is consumed, the rule `quota name "job_q" ... drop` matches and the packet is
dropped. Accepted upload packets are counted by the named counter `fwd_up`; quota drops by `quota_drop`; everything
not allowlisted by `deny_drop`. HALT atomically flushes the forward chain and leaves one rule `counter name
"halt_drop" drop` (policy drop stays), so nothing is forwarded afterwards.

Host-safety bounds are enforced here, not only by the caller:
  * namespaces only with names starting "sc07-"; veths are created inside our namespaces (never in the host
    namespace); nothing is attached to a host interface; no host route, host nftables or host sysctl is touched
    (sysctls are written only through `ip netns exec <our ns>`, where net.* sysctls are per-namespace);
  * addresses only from 10.207.0.0/16;
  * processes started in a namespace run as a numeric UID in 23800..23809 (setgroups/setgid/setuid in the child,
    no_new_privs set, no account created), entered with setns(CLONE_NEWNET) before the credential drop;
  * the no-quota ruleset (negative control) is refused unless SC07_NEGATIVE_CONTROL=1 is in the environment.
Python 3.9 compatible.
"""
import ctypes
import ipaddress
import json
import os
import signal
import subprocess
import time
from pathlib import Path

PREFIX = "sc07-"
NET = ipaddress.ip_network("10.207.0.0/16")
UIDS = range(23800, 23810)
JOB_IP, GW_JOB_IP, GW_SINK_IP = "10.207.1.2", "10.207.1.1", "10.207.2.1"
SINK_ALLOWED, SINK_DENIED, SINK_PORT = "10.207.2.10", "10.207.2.20", 8080
IF_JOB, IF_GW_JOB, IF_GW_SINK, IF_SINK = "sc07j", "sc07gj", "sc07gs", "sc07s"
TABLE = "sc07"
COUNTERS = ("fwd_up", "fwd_down", "quota_drop", "deny_drop", "halt_drop")
ENV = {"PATH": "/usr/sbin:/usr/bin:/sbin:/bin", "LANG": "C.UTF-8"}
CLONE_NEWNET = 0x40000000
PR_SET_NO_NEW_PRIVS = 38
NETNS_DIR = Path("/run/netns")
# net.* sysctls written inside our namespaces only (per-netns). Read back after writing.
NS_SYSCTLS = {
    "job": {"net.ipv6.conf.all.disable_ipv6": "1", "net.ipv6.conf.default.disable_ipv6": "1",
            "net.ipv4.ip_forward": "0"},
    "gw": {"net.ipv6.conf.all.disable_ipv6": "1", "net.ipv6.conf.default.disable_ipv6": "1",
           "net.ipv4.ip_forward": "1"},
    "sink": {"net.ipv6.conf.all.disable_ipv6": "1", "net.ipv6.conf.default.disable_ipv6": "1",
             "net.ipv4.ip_forward": "0"},
}
_libc = ctypes.CDLL(None, use_errno=True)


class Unsafe(Exception):
    """A requested operation is outside the host-safety bounds."""


def run(argv, input=None, check=True, timeout=10):
    r = subprocess.run(argv, input=input, stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True,
                       timeout=timeout, env=ENV)
    if check and r.returncode != 0:
        raise RuntimeError("%s failed rc=%d: %s" % (" ".join(argv), r.returncode, r.stderr.strip()))
    return r


def _ns_ok(name):
    if not name.startswith(PREFIX) or "/" in name:
        raise Unsafe("namespace name outside bound: %r" % name)
    return name


def _addr_ok(cidr):
    if ipaddress.ip_interface(cidr).ip not in NET:
        raise Unsafe("address outside 10.207.0.0/16: %r" % cidr)
    return cidr


def list_netns():
    """All named network namespaces (host-wide list; read-only)."""
    r = run(["ip", "-j", "netns", "list"], check=False)
    try:
        return [e["name"] for e in json.loads(r.stdout or "[]")]
    except ValueError:
        return [l.split()[0] for l in r.stdout.splitlines() if l.strip()]


def host_links():
    """Interface names in the host (runner's) network namespace; read-only."""
    return sorted(e["ifname"] for e in json.loads(run(["ip", "-j", "link", "show"]).stdout or "[]"))


def ns_inode(name):
    return os.stat(str(NETNS_DIR / _ns_ok(name))).st_ino


def ruleset(quota_bytes):
    """The gateway's nftables ruleset. quota_bytes=None is the negative control (no quota rule) and is refused
    unless SC07_NEGATIVE_CONTROL=1."""
    if quota_bytes is None and os.environ.get("SC07_NEGATIVE_CONTROL") != "1":
        raise Unsafe("ruleset without quota requires SC07_NEGATIVE_CONTROL=1")
    up = 'iifname "%s" oifname "%s" ip saddr %s ip daddr %s tcp dport %d' % (IF_GW_JOB, IF_GW_SINK, JOB_IP,
                                                                           SINK_ALLOWED, SINK_PORT)
    down = 'iifname "%s" oifname "%s" ip saddr %s tcp sport %d ip daddr %s' % (IF_GW_SINK, IF_GW_JOB, SINK_ALLOWED,
                                                                             SINK_PORT, JOB_IP)
    lines = ["table inet %s {" % TABLE]
    lines += ["  counter %s { }" % c for c in COUNTERS]
    if quota_bytes is not None:
        lines.append("  quota job_q { over %d bytes }" % int(quota_bytes))
    lines += ["  chain forward {",
              "    type filter hook forward priority filter; policy drop;",
              '    %s counter name "fwd_down" accept' % down]
    if quota_bytes is not None:
        lines.append('    %s quota name "job_q" counter name "quota_drop" drop' % up)
    lines += ['    %s counter name "fwd_up" accept' % up,
              '    counter name "deny_drop" drop',
              "  }",
              "  chain input {",
              "    type filter hook input priority filter; policy accept;",
              '    iifname "%s" drop' % IF_GW_JOB,
              "  }",
              "}"]
    return "\n".join(lines) + "\n"


HALT_SCRIPT = ("flush chain inet %s forward\n"
               'add rule inet %s forward counter name "halt_drop" drop\n') % (TABLE, TABLE)


def _enter(ns_path, uid):
    """preexec_fn: enter the network namespace (still root), then drop to the numeric UID with no_new_privs."""
    def fn():
        fd = os.open(ns_path, os.O_RDONLY)
        if _libc.setns(fd, CLONE_NEWNET) != 0:
            os._exit(121)
        os.close(fd)
        if _libc.prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0:
            os._exit(122)
        os.setgroups([])
        os.setgid(uid)
        os.setuid(uid)
        os.umask(0o022)
    return fn


class Topology:
    def __init__(self, token, tag):
        self.ns = {r: _ns_ok("%s%s-%s-%s" % (PREFIX, token, tag, r)) for r in ("job", "gw", "sink")}
        self.created = []
        self.procs = []
        self.quota = None
        self.halted = False
        self.log = []

    # ------------------------------------------------------------ setup
    def ip(self, role, *args):
        return run(["ip", "-n", self.ns[role]] + list(args))

    def nsexec(self, role, argv, **kw):
        return run(["ip", "netns", "exec", self.ns[role]] + list(argv), **kw)

    def ipbatch(self, role, cmds):
        """Several ip commands in one process, executed inside the namespace of role (ip -n <ns> -batch -)."""
        return run(["ip", "-n", self.ns[role], "-batch", "-"], input="\n".join(cmds) + "\n")

    def up(self, quota_bytes):
        existing = set(list_netns())
        for name in self.ns.values():
            if name in existing:
                raise Unsafe("namespace already exists: %s" % name)
        self.created = list(self.ns.values())
        run(["ip", "-batch", "-"], input="".join("netns add %s\n" % n for n in self.created))
        sysctl_rb = {}
        for role in ("job", "gw", "sink"):
            # One process per namespace: write, then read back in the same order (net.* sysctls are per-netns).
            keys = sorted(NS_SYSCTLS[role])
            out = self.nsexec(role, ["sh", "-c", 'sysctl -q -w "$@" && sysctl -n %s' % " ".join(keys), "sysctl"]
                              + ["%s=%s" % (k, NS_SYSCTLS[role][k]) for k in keys]).stdout.split()
            sysctl_rb[role] = dict(zip(keys, out))
            if sysctl_rb[role] != NS_SYSCTLS[role]:
                raise RuntimeError("sysctl read-back mismatch in %s: %r" % (role, sysctl_rb[role]))
        # veth pairs created inside our namespaces: the first end in the namespace given by -n, the peer directly
        # in the other namespace. No device ever exists in the host namespace.
        self.ipbatch("job", ["link set lo up",
                             "link add %s type veth peer name %s netns %s" % (IF_JOB, IF_GW_JOB, self.ns["gw"]),
                             "addr add %s dev %s" % (_addr_ok(JOB_IP + "/24"), IF_JOB),
                             "link set %s up" % IF_JOB])
        self.ipbatch("gw", ["link set lo up",
                            "link add %s type veth peer name %s netns %s" % (IF_GW_SINK, IF_SINK, self.ns["sink"]),
                            "addr add %s dev %s" % (_addr_ok(GW_JOB_IP + "/24"), IF_GW_JOB),
                            "addr add %s dev %s" % (_addr_ok(GW_SINK_IP + "/24"), IF_GW_SINK),
                            "link set %s up" % IF_GW_JOB, "link set %s up" % IF_GW_SINK])
        self.ipbatch("sink", ["link set lo up",
                              "addr add %s dev %s" % (_addr_ok(SINK_ALLOWED + "/24"), IF_SINK),
                              "addr add %s dev %s" % (_addr_ok(SINK_DENIED + "/24"), IF_SINK),
                              "link set %s up" % IF_SINK,
                              "route add default via %s dev %s" % (GW_SINK_IP, IF_SINK)])
        self.ipbatch("job", ["route add default via %s dev %s" % (GW_JOB_IP, IF_JOB)])
        self.install(quota_bytes)
        return {"namespaces": dict(self.ns), "sysctls": sysctl_rb, "ruleset": self.ruleset_text()}

    def install(self, quota_bytes):
        script = ruleset(quota_bytes)
        self.nsexec("gw", ["nft", "-f", "-"], input=script)
        self.quota = quota_bytes

    # ------------------------------------------------------------ gateway operations
    def ruleset_text(self):
        return self.nsexec("gw", ["nft", "list", "ruleset"]).stdout

    def ruleset_json(self):
        return json.loads(self.nsexec("gw", ["nft", "-j", "list", "ruleset"]).stdout)

    def counters(self):
        out = {}
        for e in json.loads(self.nsexec("gw", ["nft", "-j", "list", "counters", "table", "inet", TABLE]).stdout)[
                "nftables"]:
            if "counter" in e:
                out[e["counter"]["name"]] = {"packets": e["counter"]["packets"], "bytes": e["counter"]["bytes"]}
        return out

    def quotas(self):
        out = {}
        for e in json.loads(self.nsexec("gw", ["nft", "-j", "list", "quotas", "table", "inet", TABLE]).stdout)[
                "nftables"]:
            if "quota" in e:
                q = e["quota"]
                out[q["name"]] = {"bytes": q.get("bytes"), "used": q.get("used"), "inv": q.get("inv")}
        return out

    def halt(self):
        """Admin HALT: one nft transaction flushes the forward chain and adds a single counted drop rule."""
        t0 = time.monotonic()
        self.nsexec("gw", ["nft", "-f", "-"], input=HALT_SCRIPT)
        t1 = time.monotonic()
        self.halted = True
        return {"t_start": t0, "t_end": t1, "latency_s": round(t1 - t0, 6)}

    # ------------------------------------------------------------ processes
    def spawn(self, role, uid, argv, stdout=subprocess.PIPE, stderr=None, stdin=subprocess.DEVNULL):
        if uid not in UIDS:
            raise Unsafe("uid outside 23800..23809: %r" % uid)
        p = subprocess.Popen(argv, preexec_fn=_enter(str(NETNS_DIR / self.ns[role]), uid), stdin=stdin,
                             stdout=stdout, stderr=stderr, cwd="/", env=dict(ENV), close_fds=True)
        self.procs.append(p)
        return p

    def ns_pids(self):
        """{namespace name: [pids]} for every live process whose /proc/<pid>/ns/net is one of ours (one /proc scan,
        same information as `ip netns pids`)."""
        ino = {}
        for name in self.created:
            try:
                ino[ns_inode(name)] = name
            except FileNotFoundError:
                pass
        out = {n: [] for n in ino.values()}
        for d in os.listdir("/proc"):
            if d.isdigit():
                try:
                    i = os.stat("/proc/%s/ns/net" % d).st_ino
                except (FileNotFoundError, ProcessLookupError, PermissionError):
                    continue
                if i in ino:
                    out[ino[i]].append(int(d))
        return out

    # ------------------------------------------------------------ teardown
    def close(self):
        rep = {"terminated": 0, "killed": 0, "ns_pids_killed": [], "sockets": {}, "deleted": [], "errors": []}
        for p in self.procs:
            if p.poll() is None:
                p.send_signal(signal.SIGTERM)
                rep["terminated"] += 1
        t0 = time.monotonic()
        while any(p.poll() is None for p in self.procs) and time.monotonic() - t0 < 2.0:
            time.sleep(0.01)
        for p in self.procs:
            if p.poll() is None:
                p.kill()
                rep["killed"] += 1
            try:
                p.wait(timeout=2)
            except subprocess.TimeoutExpired:
                rep["errors"].append("pid %d did not exit" % p.pid)
            for f in (p.stdout, p.stderr, p.stdin):
                if f:
                    try:
                        f.close()
                    except OSError:
                        pass
        for pass_ in range(3):
            pids = self.ns_pids()
            if not any(pids.values()):
                break
            for name, ps in pids.items():
                for pid in ps:
                    try:
                        os.kill(pid, signal.SIGKILL)
                        rep["ns_pids_killed"].append(pid)
                    except ProcessLookupError:
                        pass
            time.sleep(0.05)
        existing = set(list_netns())
        dels = []
        for role, name in self.ns.items():
            if name not in self.created or name not in existing:
                continue
            # Sockets left in our namespace (TIME-WAIT is harmless; anything else is aborted with ss -K so the
            # namespace is freed promptly when deleted).
            r = run(["ss", "-N", name, "-tanH"], check=False)
            ss = [l for l in r.stdout.split("\n") if l.strip()]
            rep["sockets"][role] = ss
            if any(not l.startswith("TIME-WAIT") for l in ss):
                run(["ss", "-N", name, "-K", "-tan"], check=False)
            dels.append(name)
        if dels:
            r = run(["ip", "-force", "-batch", "-"], input="".join("netns del %s\n" % n for n in dels), check=False)
            if r.returncode != 0:
                rep["errors"].append("ip netns del: %s" % r.stderr.strip())
        rep["deleted"] = [n for n in dels if n not in set(list_netns())]
        left = set(list_netns())
        rep["left_netns"] = sorted(n for n in self.created if n in left)
        rep["host_sc07_links"] = [l for l in host_links() if l.startswith("sc07")]
        rep["ok"] = not rep["left_netns"] and not rep["host_sc07_links"] and not rep["errors"]
        return rep
