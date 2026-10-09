#!/usr/bin/env python3
"""SC-20 data provenance: a principal process, source, reviewer or trainer (prereg/SC20-DATA-PROVENANCE.md).

Each has its own fsync'd log (record, then a {"commit": seq, "t": ns} line).
  source    {"op": "ingest", "id", "content"}: log {id, digest, source}, then send to the store's ingest socket
            (the store names the source by this process's pid).
  reviewer  {"op": "promote", "id"}: fetch the CURRENT content and its writer from the store, log
            {id, digest, writer, reviewer}, then promote exactly that digest. {"op": "write_and_promote", "id",
            "content"}: write an example AS this reviewer and try to promote it (the self-promotion case).
  trainer   {"op": "train"}: read the frozen manifest, read each listed example from storage, RE-CHECK its digest
            against the frozen digest (refuse the whole run on any mismatch; --no-recheck is the NEGATIVE_CONTROL),
            and compute a trivial deterministic statistic (SHA-256 over the consumed contents, label mean). Log the
            run with the digest of every consumed content.
Self-contained; self-exits after --lifetime seconds.
"""
import argparse
import hashlib
import json
import os
import socket
import sys
import threading
import time


def digest(content):
    return hashlib.sha256(json.dumps(content, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


class Conn:
    def __init__(self, path):
        self.s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        self.s.settimeout(20.0)
        self.s.connect(path)
        self.f = self.s.makefile("rwb", buffering=0)

    def call(self, obj):
        self.f.write((json.dumps(obj) + "\n").encode())
        return json.loads(self.f.readline())

    def close(self):
        self.s.close()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--role", choices=["source", "reviewer", "trainer"], required=True)
    ap.add_argument("--name", default="")
    ap.add_argument("--sock", required=True)
    ap.add_argument("--store-dir", required=True, help="the store's socket directory")
    ap.add_argument("--store", help="trainer: the storage directory (read-only)")
    ap.add_argument("--manifest", help="trainer: the frozen manifest file")
    ap.add_argument("--log", required=True)
    ap.add_argument("--no-recheck", action="store_true")
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    fd = os.open(a.log, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
    lock, seq = threading.Lock(), [0]
    me = a.name or "pid:%d" % os.getpid()
    sock = lambda r: os.path.join(a.store_dir, r + ".sock")

    def record(rec):
        with lock:
            rec["seq"] = seq[0]
            seq[0] += 1
            os.write(fd, (json.dumps(rec) + "\n").encode())
            os.fsync(fd)
            os.write(fd, (json.dumps({"commit": rec["seq"], "t": time.monotonic_ns()}) + "\n").encode())
            return rec

    def promote(c, id_):
        g = c.call({"op": "get", "id": id_})
        if not g.get("ok"):
            return g
        record({"id": id_, "digest": g["digest"], "writer": g["writer"], "reviewer": me, "verdict": "promote"})
        return c.call({"op": "promote", "id": id_, "digest": g["digest"]})

    def handle(m):
        op = m.get("op")
        if a.role == "source" and op == "ingest":
            record({"id": m["id"], "digest": digest(m["content"]), "source": me})
            c = Conn(sock("ingest"))
            try:
                return c.call({"id": m["id"], "content": m["content"]})
            finally:
                c.close()
        if a.role == "reviewer" and op in ("promote", "write_and_promote"):
            if op == "write_and_promote":
                w = Conn(sock("agent"))
                try:
                    w.call({"id": m["id"], "content": m["content"]})
                finally:
                    w.close()
            c = Conn(sock("review"))
            try:
                return promote(c, str(m["id"]))
            finally:
                c.close()
        if a.role == "trainer" and op == "train":
            man = json.load(open(a.manifest))["manifest"]
            consumed, bad = [], []
            for id_, d in man:
                try:
                    content = json.load(open(os.path.join(a.store, "examples", "%s.json" % id_)))
                except (OSError, ValueError):
                    bad.append({"id": id_, "why": "unreadable"})
                    continue
                cd = digest(content)
                if cd != d:
                    bad.append({"id": id_, "why": "digest differs from the frozen manifest"})
                    if not a.no_recheck:
                        continue
                consumed.append((id_, cd, content))
            if bad and not a.no_recheck:
                rec = record({"ok": False, "refused": bad, "frozen": man, "consumed": []})
                return {"ok": False, "error": "training refused: %d example(s) differ from the frozen manifest" %
                        len(bad), "seq": rec["seq"]}
            h = hashlib.sha256()
            for _, cd, _ in consumed:
                h.update(bytes.fromhex(cd))
            labels = [c.get("label", 0) for _, _, c in consumed]
            stat = {"n": len(consumed), "hash": h.hexdigest(),
                    "label_mean": round(sum(labels) / len(labels), 6) if labels else None}
            rec = record({"ok": True, "frozen": man, "consumed": [[i, d] for i, d, _ in consumed], "stat": stat,
                          "mismatches_ignored": bad, "config": {"no_recheck": a.no_recheck}})
            return {"ok": True, "stat": stat, "seq": rec["seq"]}
        return {"ok": False, "error": "unknown op for %s" % a.role}

    def serve(conn):
        f = conn.makefile("rwb", buffering=0)
        try:
            for line in f:
                try:
                    r = handle(json.loads(line))
                except Exception as e:
                    r = {"ok": False, "error": "%s: %s" % (type(e).__name__, e)}
                f.write((json.dumps(r) + "\n").encode())
        except OSError:
            pass
        finally:
            conn.close()

    lis = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    lis.bind(a.sock)
    os.chmod(a.sock, 0o600)
    lis.listen(16)
    threading.Timer(a.lifetime, lambda: os._exit(0)).start()
    sys.stdout.write("READY " + json.dumps({"pid": os.getpid(), "role": a.role, "name": me}) + "\n")
    sys.stdout.flush()
    while True:
        conn, _ = lis.accept()
        threading.Thread(target=serve, args=(conn,), daemon=True).start()


if __name__ == "__main__":
    main()
