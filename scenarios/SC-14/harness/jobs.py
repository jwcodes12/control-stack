#!/usr/bin/env python3
"""SC-14 trusted per-job budget controller (root). Model: ControlStack/Scenarios/SC14Runaway.lean (`sc14_safe`;
witnesses `aggregate_cap_breaks`, `rate_burst_breaks`, `no_expiry_breaks`).

A job is a cgroup <top>/job-<name> with a budget VECTOR, each component metered by the kernel or by this controller
(never by the job's own report):
  memory  memory.max (kernel; memory.swap.max = 0 so the cap cannot be sidestepped by swapping)   metered: memory.peak
  pids    pids.max (kernel)                                                                         metered: pids.peak
  rate    cpu.max quota per 100 ms period (kernel)                                                  metered: cpu.stat
  cpu     cumulative CPU-time budget: this controller polls cpu.stat usage_usec every POLL seconds and writes
          cgroup.kill once usage reaches the budget (tolerance = one poll of the rate cap + kill latency)
  expiry  a lease deadline: the controller writes cgroup.kill at the deadline and refuses later launches
Network egress is NOT part of this harness (see the prereg).

mode="per_resource" is the deployed design. mode="aggregate" is the negative control (`aggregate_cap_breaks`): the
kernel caps are set to the host maxima and the controller enforces only the SUM of per-resource fractions
(cpu/cpu_cap + memory/memory_cap + pids/pids_cap <= agg_cap), so one resource can exceed its own cap.
"""
import threading
import time
from pathlib import Path

import cgctl

POLL = 0.01


class Refused(Exception):
    pass


class Job:
    def __init__(self, name, path, budget, mode, agg_cap):
        self.name, self.path, self.budget, self.mode, self.agg_cap = name, path, budget, mode, agg_cap
        self.t_start = None
        self.deadline = None
        self.killed = None  # {"reason", "t", "usage_usec"}
        self.expired = False
        self.popens = []


class JobCtl:
    def __init__(self, cg):
        self.cg, self.jobs, self.lock = cg, {}, threading.Lock()
        self.stop = threading.Event()
        self.t = threading.Thread(target=self._meter, daemon=True)
        self.t.start()

    def create(self, name, budget, mode="per_resource", agg_cap=None):
        if mode == "per_resource":
            path, lim = self.cg.make("job-" + name, cpu_max="%d 100000" % budget["rate_quota"],
                                     pids_max=budget["pids"], memory_max=budget["memory"])
        elif mode == "aggregate":
            path, lim = self.cg.make("job-" + name)  # host maxima only
        else:
            raise ValueError(mode)
        swap = Path(path) / "memory.swap.max"
        if swap.exists():
            cgctl.w(swap, "0")
            if cgctl.r(swap).strip() != "0":
                raise RuntimeError("memory.swap.max read-back mismatch")
        with self.lock:
            self.jobs[name] = Job(name, path, dict(budget), mode, agg_cap)
        return self.jobs[name], lim

    def launch(self, name, uid, argv, stdout=None):
        j = self.jobs[name]
        with self.lock:
            if j.killed or j.expired:
                raise Refused("job %s is finished/expired" % name)
            now = time.monotonic()
            if j.t_start is None:
                j.t_start = now
                if j.budget.get("expiry_s"):
                    j.deadline = now + j.budget["expiry_s"]
            p = self.cg.launch(j.path, uid, argv, stdout=stdout)
            j.popens.append(p)
        return p

    def usage(self, j):
        st = cgctl.kv(cgctl.r(Path(j.path) / "cpu.stat"))
        return {"usage_usec": st.get("usage_usec", 0), "nr_throttled": st.get("nr_throttled", 0),
                "memory.current": int(cgctl.r(Path(j.path) / "memory.current")),
                "pids.current": int(cgctl.r(Path(j.path) / "pids.current"))}

    def stats(self, name):
        j = self.jobs[name]
        p = Path(j.path)
        out = self.usage(j)
        for k in ("memory.peak", "pids.peak"):
            try:
                out[k] = int(cgctl.r(p / k))
            except (FileNotFoundError, ValueError):
                out[k] = None
        out["memory.events"] = cgctl.kv(cgctl.r(p / "memory.events"))
        out["pids.events"] = cgctl.kv(cgctl.r(p / "pids.events"))
        out["settings"] = {k: cgctl.r(p / k).strip() for k in ("cpu.max", "memory.max", "pids.max")}
        return out

    def _kill(self, j, reason, u):
        j.killed = {"reason": reason, "t": time.monotonic(), "usage_usec": u["usage_usec"]}
        if reason == "expiry":
            j.expired = True
        self.cg.kill(j.path)

    def _meter(self):
        while not self.stop.is_set():
            now = time.monotonic()
            with self.lock:
                for j in self.jobs.values():
                    if j.t_start is None or j.killed or not Path(j.path).exists():
                        continue
                    try:
                        u = self.usage(j)
                    except (FileNotFoundError, OSError):
                        continue
                    b = j.budget
                    if j.deadline is not None and now >= j.deadline:
                        self._kill(j, "expiry", u)
                    elif j.mode == "per_resource" and u["usage_usec"] >= b["cpu_usec"]:
                        self._kill(j, "cpu_budget", u)
                    elif j.mode == "aggregate":
                        frac = (u["usage_usec"] / b["cpu_usec"] + u["memory.current"] / b["memory"] +
                                u["pids.current"] / b["pids"])
                        if frac > j.agg_cap:
                            self._kill(j, "aggregate", u)
                    for p in j.popens:
                        p.poll()
            time.sleep(POLL)

    def close(self):
        self.stop.set()
        self.t.join(timeout=2)
        for j in self.jobs.values():
            for p in j.popens:
                try:
                    p.wait(timeout=2)
                except Exception:
                    pass
                if p.stdout:
                    p.stdout.close()
