#!/usr/bin/env python3
"""SC-22 replication sampling: the scripted reporter (prereg/SC22-REPLICATION.md).

For each trial t it "reports" N findings: finding i's true value is experiment(t, i) (a deterministic toy experiment);
it MISREPORTS k of them (value + 1), choosing which with its own RNG WITHOUT seeing the replication sample (NON_ADAPTIVE,
as in the model) - or, in the visible-sample control, choosing only findings outside the sample it was shown
(`observable_sample_nogo`). It logs, per trial, the set it misreported (its own log, for the analysis) and submits all
reports to the replicator, which commits to them before any hidden sample is drawn. Self-contained.
"""
import argparse
import json
import os
import random
import socket
import sys
import threading


def experiment(t, i):
    return ((t + 1) * 2654435761 + (i + 1) * 40503) % 1000003 % 1000


def rpc(path, obj, timeout=60.0):
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    s.settimeout(timeout)
    try:
        s.connect(path)
        f = s.makefile("rwb")
        f.write((json.dumps(obj) + "\n").encode())
        f.flush()
        return json.loads(f.readline())
    finally:
        s.close()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sock", required=True)
    ap.add_argument("--replicator", required=True)
    ap.add_argument("--log", required=True)
    ap.add_argument("--lifetime", type=float, default=60.0)
    a = ap.parse_args()

    def handle(m):
        N, k, T = int(m["N"]), int(m["k"]), int(m["trials"])
        rng = random.Random(m["seed"])
        visible = m.get("visible")
        reports, logged = [], []
        for t in range(T):
            cand = list(range(N)) if visible is None else sorted(set(range(N)) - set(visible[t]))
            A = sorted(rng.sample(cand, k))
            claims = [experiment(t, i) + (1 if i in A else 0) for i in range(N)]
            reports.append({"t": t, "claims": claims})
            logged.append({"config": m["config"], "t": t, "misreported": A})
        with open(a.log, "a") as fh:
            for r in logged:
                fh.write(json.dumps(r) + "\n")
            fh.flush()
            os.fsync(fh.fileno())
        return rpc(a.replicator, {"op": "submit", "config": m["config"], "reports": reports})

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
