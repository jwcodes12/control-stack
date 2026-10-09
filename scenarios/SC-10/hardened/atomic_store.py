#!/usr/bin/env python3
"""SC-10 v2 *reference* serialized policy-decision journal.

Not the frozen preregistered harness; NOT an external firewall or network effect
adapter. Every successful write or decision is linearized under one store-owned
lock (the single-threaded Unix-socket service), and durably journaled before
acknowledgment. Runtime-to-Lean correspondence is still a separate obligation.
"""
import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import socket
import stat
import struct

MAX_LINE = 64 * 1024


def canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True).encode()


def sha(obj):
    return hashlib.sha256(canonical(obj)).hexdigest()


def policy_checked(value):
    if (not isinstance(value, dict) or set(value) != {"allow"}
            or not isinstance(value["allow"], list)
            or any(not isinstance(host, str) or not host or len(host) > 253
                   for host in value["allow"])
            or len(value["allow"]) > 1024
            or len(set(value["allow"])) != len(value["allow"])):
        raise ValueError("policy must contain only a distinct nonempty string allowlist")
    return {"allow": list(value["allow"])}


class AtomicPolicyJournal:
    """Durability is about this journal's decisions, not later external effects."""

    def __init__(self, path, admin_pid):
        self.path = Path(path)
        self.admin_pid = admin_pid
        self.versions = []
        self.events = []
        self.poisoned = False
        flags = os.O_RDWR | os.O_CREAT | os.O_APPEND
        if hasattr(os, "O_NOFOLLOW"):
            flags |= os.O_NOFOLLOW
        self.fd = os.open(self.path, flags, 0o600)
        try:
            fcntl.flock(self.fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            if not stat.S_ISREG(os.fstat(self.fd).st_mode):
                raise ValueError("journal is not a regular file")
            # Open with O_APPEND; read from offset zero to validate every prior
            # acknowledged event. A torn or malformed tail fails closed.
            os.lseek(self.fd, 0, os.SEEK_SET)
            with os.fdopen(os.dup(self.fd), "rb") as fh:
                data = fh.read()
            if data and not data.endswith(b"\n"):
                raise ValueError("incomplete journal tail; manual recovery required")
            prev_hash = "0" * 64
            for raw in data.splitlines():
                if len(raw) > MAX_LINE:
                    raise ValueError("oversized journal line")
                item = json.loads(raw)
                if canonical(item) != raw or item.get("seq") != len(self.events) or item.get("prev") != prev_hash:
                    raise ValueError("journal canonical form, sequence or chain mismatch")
                self._replay(item)
                self.events.append(item)
                prev_hash = sha(item)
        except Exception:
            os.close(self.fd)
            raise

    def _replay(self, entry):
        kind = entry.get("kind")
        if kind == "write":
            pol = policy_checked(entry["policy"])
            if (entry["version"] != len(self.versions) or
                    entry["digest"] != sha(pol) or
                    not isinstance(entry.get("writer_pid"), int)):
                raise ValueError("invalid policy-write journal entry")
            self.versions.append((pol, entry["digest"], entry["writer_pid"]))
        elif kind == "decide":
            if not self.versions:
                raise ValueError("decision without a policy")
            pol, digest, _ = self.versions[-1]
            if (entry["version"] != len(self.versions) - 1 or entry["digest"] != digest or
                    entry["decision"] != ("allow" if entry["host"] in pol["allow"] else "deny")):
                raise ValueError("stale or inconsistent decision in journal")
        else:
            raise ValueError("unknown journal entry type")

    def _commit(self, fields):
        if self.poisoned:
            raise RuntimeError("journal unavailable after failed write")
        record = {"seq": len(self.events), "prev": sha(self.events[-1]) if self.events else "0" * 64, **fields}
        raw = canonical(record) + b"\n"
        if len(raw) > MAX_LINE:
            raise ValueError("journal entry exceeds maximum size")
        try:
            view = memoryview(raw)
            while view:
                n = os.write(self.fd, view)
                if n <= 0:
                    raise OSError("short journal write")
                view = view[n:]
            os.fsync(self.fd)
        except Exception:
            # A partial durable tail would make later recovery impossible.
            self.poisoned = True
            raise
        self._replay(record)
        self.events.append(record)
        return record

    def handle(self, peer_pid, request):
        if not isinstance(request, dict):
            return {"ok": False, "error": "invalid request"}
        op = request.get("op")
        if op == "write":
            if peer_pid != self.admin_pid:
                return {"ok": False, "error": "admin pid required"}
            try:
                pol = policy_checked(request.get("policy"))
            except (TypeError, ValueError) as exc:
                return {"ok": False, "error": str(exc)}
            entry = self._commit({"kind": "write", "version": len(self.versions),
                                  "writer_pid": peer_pid, "policy": pol, "digest": sha(pol)})
            return {"ok": True, "version": entry["version"], "seq": entry["seq"]}
        if op == "decide":
            host = request.get("host")
            if not isinstance(host, str) or not host or len(host) > 253:
                return {"ok": False, "error": "invalid host"}
            if not self.versions:
                return {"ok": False, "error": "no policy"}
            pol, digest, _ = self.versions[-1]
            result = "allow" if host in pol["allow"] else "deny"
            entry = self._commit({"kind": "decide", "host": host,
                                  "version": len(self.versions) - 1,
                                  "digest": digest, "decision": result})
            return {"ok": True, "decision": result, "version": entry["version"],
                    "digest": digest, "seq": entry["seq"]}
        return {"ok": False, "error": "unknown operation"}

    def close(self):
        os.close(self.fd)


def serve(sockpath, journal_path, admin_pid):
    """One request at a time; socket peer pid is observed by the kernel."""
    store = AtomicPolicyJournal(journal_path, admin_pid)
    with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as server:
        server.bind(sockpath)
        os.chmod(sockpath, 0o600)
        server.listen(16)
        try:
            while True:
                conn, _ = server.accept()
                with conn:
                    conn.settimeout(1.0)
                    peer = struct.unpack("3i", conn.getsockopt(socket.SOL_SOCKET, socket.SO_PEERCRED, 12))[0]
                    with conn.makefile("rwb", buffering=0) as rw:
                        try:
                            while True:
                                line = rw.readline(MAX_LINE + 1)
                                if not line:
                                    break
                                if len(line) > MAX_LINE or not line.endswith(b"\n"):
                                    break  # reject oversized / unterminated framing
                                try:
                                    result = store.handle(peer, json.loads(line))
                                except (ValueError, TypeError, json.JSONDecodeError):
                                    result = {"ok": False, "error": "invalid JSON or request"}
                                rw.write(canonical(result) + b"\n")
                        except (OSError, TimeoutError):
                            pass
        finally:
            store.close()
            os.unlink(sockpath)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--socket", required=True)
    parser.add_argument("--journal", required=True)
    parser.add_argument("--admin-pid", type=int, required=True)
    args = parser.parse_args()
    serve(args.socket, args.journal, args.admin_pid)
