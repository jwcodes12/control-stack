#!/usr/bin/env python3
"""SC-17 drift reconcile: the trusted reconciler (prereg/SC17-DRIFT-RECONCILE.md).

On an absolute schedule start + j * period (period = W ticks), it reads the desired state and its version from the
apply gate and the live state from the cluster; if they differ it pushes the desired state (with its version) through
the cluster's trusted socket, which reverts out-of-band grants. Every run is logged. Self-contained (python -I -S).
"""
import argparse
import json
import os
import socket
import sys
import time


def rpc(path, obj, timeout=2.0):
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    s.settimeout(timeout)
    try:
        s.connect(path)
        f = s.makefile("rwb", buffering=0)
        f.write((json.dumps(obj) + "\n").encode())
        return json.loads(f.readline())
    finally:
        s.close()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--gate", required=True, help="gate read socket")
    ap.add_argument("--cluster-ctl", required=True)
    ap.add_argument("--period", type=float, required=True)
    ap.add_argument("--log", required=True)
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    fd = os.open(a.log, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    t0 = time.monotonic()
    sys.stdout.write("READY " + json.dumps({"pid": os.getpid()}) + "\n")
    sys.stdout.flush()
    j = 1
    while time.monotonic() - t0 < a.lifetime:
        nxt = t0 + j * a.period
        time.sleep(max(0.0, nxt - time.monotonic()))
        j += 1
        rec = {"t_start": time.monotonic_ns(), "late_s": round(time.monotonic() - nxt, 6)}
        try:
            d = rpc(a.gate, {"op": "get_desired"})
            live = rpc(a.cluster_ctl, {"op": "get"})
            if sorted(map(tuple, live["live"])) != sorted(map(tuple, d["desired"])):
                r = rpc(a.cluster_ctl, {"op": "set_state", "grants": d["desired"], "version": d["version"],
                                        "by": "reconciler"})
                rec.update(pushed=True, ok=r.get("ok"), removed=r.get("removed"))
            else:
                rec.update(pushed=False)
        except (OSError, ValueError, KeyError) as e:
            rec.update(error=str(e))
        rec["t_end"] = time.monotonic_ns()
        os.write(fd, (json.dumps(rec) + "\n").encode())


if __name__ == "__main__":
    main()
