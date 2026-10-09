#!/usr/bin/env python3
"""SC-22 replication sampling: the independent replicator (prereg/SC22-REPLICATION.md).

  submit    {config, reports}: store the reports and log a COMMITMENT (SHA-256 of the canonical reports) with a time
            stamp; nothing is sampled yet
  draw      {config, trials, N, B, seed}: pre-draw samples and RETURN them (visible-sample control only)
  replicate {config, N, B, seed}: refuse unless the reports are committed; for every trial draw a uniformly random
            sample of B of the N findings with the replicator's own RNG (a seed the reporter never sees), drawn AFTER
            the commitment (or use the pre-drawn visible sample), re-run the toy experiment on the sampled findings
            and flag every mismatch; log {t, sample, flags, detected}
Self-contained.
"""
import argparse
import hashlib
import json
import os
import random
import socket
import sys
import threading
import time


def experiment(t, i):
    return ((t + 1) * 2654435761 + (i + 1) * 40503) % 1000003 % 1000


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sock", required=True)
    ap.add_argument("--log", required=True)
    ap.add_argument("--lifetime", type=float, default=60.0)
    a = ap.parse_args()
    lock = threading.Lock()
    store, predrawn = {}, {}
    logf = open(a.log, "a")

    def log(objs):
        for o in objs:
            logf.write(json.dumps(o) + "\n")
        logf.flush()
        os.fsync(logf.fileno())

    def handle(m):
        op, cfg = m.get("op"), m.get("config")
        with lock:
            if op == "submit":
                rep = m["reports"]
                c = hashlib.sha256(json.dumps(rep, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
                store[cfg] = {"reports": rep, "commitment": c, "t_commit": time.monotonic_ns()}
                log([{"ev": "commit", "config": cfg, "commitment": c, "n": len(rep), "t": store[cfg]["t_commit"]}])
                return {"ok": True, "commitment": c}
            if op == "draw":
                rng = random.Random(m["seed"])
                S = [sorted(rng.sample(range(int(m["N"])), int(m["B"]))) for _ in range(int(m["trials"]))]
                predrawn[cfg] = S
                log([{"ev": "draw_visible", "config": cfg, "t": time.monotonic_ns()}])
                return {"ok": True, "samples": S}
            if op == "replicate":
                st = store.get(cfg)
                if st is None:
                    return {"ok": False, "error": "no committed reports"}
                N, B = int(m["N"]), int(m["B"])
                rng = random.Random(m["seed"])
                t_draw = time.monotonic_ns()
                out, und = [], 0
                for r in st["reports"]:
                    t = r["t"]
                    S = predrawn[cfg][t] if cfg in predrawn else sorted(rng.sample(range(N), B))
                    flags = [i for i in S if r["claims"][i] != experiment(t, i)]
                    und += not flags
                    out.append({"ev": "replicate", "config": cfg, "t": t, "sample": S, "flags": flags,
                                "detected": bool(flags), "t_draw": t_draw, "visible": cfg in predrawn})
                log(out)
                return {"ok": True, "trials": len(out), "undetected": und, "t_commit": st["t_commit"],
                        "t_draw": t_draw}
        return {"ok": False, "error": "unknown op"}

    def serve(conn):
        f = conn.makefile("rwb")
        try:
            for line in f:
                try:
                    r = handle(json.loads(line))
                except Exception as e:
                    r = {"ok": False, "error": "%s: %s" % (type(e).__name__, e)}
                f.write((json.dumps(r) + "\n").encode())
                f.flush()
        except OSError:
            pass
        finally:
            conn.close()

    lis = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    lis.bind(a.sock)
    os.chmod(a.sock, 0o600)
    lis.listen(4)
    threading.Timer(a.lifetime, lambda: os._exit(0)).start()
    sys.stdout.write("READY " + json.dumps({"pid": os.getpid()}) + "\n")
    sys.stdout.flush()
    while True:
        conn, _ = lis.accept()
        threading.Thread(target=serve, args=(conn,), daemon=True).start()


if __name__ == "__main__":
    main()
