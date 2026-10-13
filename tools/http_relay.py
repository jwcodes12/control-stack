#!/usr/bin/env python3
"""Outbox relay: forward receipt-verified published bytes to a LOCAL HTTP destination (gate G7).

This is deliberately NOT part of the pinned trusted slice and NOT part of the deployment claim. The claimed effect is the
local-file publication (`<release_id>.body`, receipted in `publication_receipts`). This relay is a separate, unprivileged
reader downstream of that outbox: it opens the broker database read-only, runs the same read-only release-log verification
the reconciler uses, and only then POSTs the sink file of a release whose receipt is present. It cannot release anything the
broker did not release, because it never writes the broker database and sends only bytes whose SHA-256 equals the logged digest.

Delivery semantics are at-least-once on the wire. Each request carries `Idempotency-Key: release-<id>-<sha256>`; a destination
that honours the key stores one copy even if an acknowledgement is lost and the relay retries. The relay records an
acknowledgement only for a 2xx response whose JSON body echoes the same SHA-256, in its own append-only SQLite file (never in
the broker database). Without a destination that honours the key, a crash between the POST and the acknowledgement record
re-sends the same bytes: that is stated, not hidden.

Destinations are restricted to literal loopback addresses (127.0.0.0/8, ::1) unless the operator passes --allow-host
explicitly; redirects are refused. No third party is contacted by default.
"""
import argparse
import hashlib
import http.client
import ipaddress
import json
import sqlite3
import sys
import time
import urllib.parse
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from deployment.reconcile import release_log_problems  # noqa: E402

MAX_BODY = 1024 * 1024
STATE_DDL = (
    """CREATE TABLE IF NOT EXISTS http_acks (
       release_id INTEGER PRIMARY KEY, digest TEXT NOT NULL, url TEXT NOT NULL, status INTEGER NOT NULL,
       echoed_sha256 TEXT NOT NULL, attempts INTEGER NOT NULL, acked_at REAL NOT NULL)""",
    """CREATE TRIGGER IF NOT EXISTS http_acks_no_update BEFORE UPDATE ON http_acks
       BEGIN SELECT RAISE(ABORT, 'http_acks is append-only'); END""",
    """CREATE TRIGGER IF NOT EXISTS http_acks_no_delete BEFORE DELETE ON http_acks
       BEGIN SELECT RAISE(ABORT, 'http_acks is append-only'); END""",
)


class RelayError(Exception):
    pass


def check_destination(url, allow_hosts=frozenset()):
    """Return (host, port, path). Only http, only a literal loopback IP (or an explicitly allowed host), no credentials."""
    parts = urllib.parse.urlsplit(url)
    if parts.scheme != "http" or not parts.hostname or parts.username or parts.password or parts.fragment:
        raise RelayError("destination must be a plain http URL with a host and no credentials or fragment")
    host = parts.hostname
    try:
        loopback = ipaddress.ip_address(host).is_loopback
    except ValueError:
        loopback = False  # a DNS name is never assumed to be loopback
    if not loopback and host not in allow_hosts:
        raise RelayError("destination host is not a literal loopback address and was not allowed explicitly")
    return host, parts.port or 80, (parts.path or "/") + ("?" + parts.query if parts.query else "")


def post_once(host, port, path, body, digest, release_id, timeout):
    conn = http.client.HTTPConnection(host, port, timeout=timeout)
    try:
        conn.request("POST", path, body=body, headers={
            "Content-Type": "application/octet-stream", "Content-Length": str(len(body)),
            "Idempotency-Key": "release-%d-%s" % (release_id, digest), "X-Release-Id": str(release_id)})
        resp = conn.getresponse()
        data = resp.read(MAX_BODY)
        return resp.status, data
    finally:
        conn.close()


def verified_releases(db_path, sink):
    """Release ids with a publication receipt, after the whole release log verified clean. Fails closed on any problem."""
    problems = release_log_problems(db_path, sink)
    if problems is None:
        raise RelayError("database has no release_log (generation older than r2-v8): nothing can be verified")
    if problems:
        raise RelayError("release log does not verify: " + "; ".join(problems[:5]))
    db = sqlite3.connect("file:" + str(Path(db_path).resolve()) + "?mode=ro", uri=True)
    try:
        has = db.execute("SELECT 1 FROM sqlite_master WHERE name='publication_receipts'").fetchone()
        if not has:
            return []
        return [(rid, digest) for rid, digest in db.execute(
            "SELECT p.release_id, p.observed_sha256 FROM publication_receipts p ORDER BY p.release_id")]
    finally:
        db.close()


def relay(db_path, sink, url, state_path, *, timeout=5.0, retries=2, allow_hosts=frozenset(), sleep=time.sleep):
    host, port, path = check_destination(url, allow_hosts)
    sink = Path(sink)
    todo = verified_releases(db_path, sink)
    state = sqlite3.connect(str(state_path))
    for statement in STATE_DDL:
        state.execute(statement)
    state.commit()
    report = {"url": url, "verified": len(todo), "sent": 0, "already_acked": 0, "failed": []}
    try:
        for rid, digest in todo:
            prior = state.execute("SELECT digest,url FROM http_acks WHERE release_id=?", (rid,)).fetchone()
            if prior is not None:
                if prior != (digest, url):
                    raise RelayError("release %d was acknowledged for a different digest or destination" % rid)
                report["already_acked"] += 1
                continue
            body = (sink / (str(rid) + ".body")).read_bytes()
            if len(body) > MAX_BODY or hashlib.sha256(body).hexdigest() != digest:
                raise RelayError("sink bytes for release %d differ from the verified digest" % rid)
            last = None
            for attempt in range(1, retries + 2):
                try:
                    status, data = post_once(host, port, path, body, digest, rid, timeout)
                except (OSError, http.client.HTTPException) as exc:
                    last = "transport error: " + type(exc).__name__
                    sleep(0.05 * attempt)
                    continue
                if not 200 <= status < 300:
                    last = "HTTP %d" % status  # includes 3xx: redirects are refused, never followed
                    sleep(0.05 * attempt)
                    continue
                try:
                    echoed = json.loads(data.decode())["sha256"]
                except (ValueError, KeyError, TypeError, UnicodeDecodeError):
                    last = "acknowledgement body is not JSON with a sha256"
                    continue
                if echoed != digest:
                    last = "destination echoed a different SHA-256"
                    continue
                state.execute("INSERT INTO http_acks VALUES (?,?,?,?,?,?,?)",
                              (rid, digest, url, status, echoed, attempt, time.time()))
                state.commit()
                report["sent"] += 1
                last = None
                break
            if last is not None:
                report["failed"].append({"release_id": rid, "reason": last})
        return report
    finally:
        state.close()


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0], allow_abbrev=False)
    ap.add_argument("--db", type=Path, required=True)
    ap.add_argument("--sink", type=Path, required=True)
    ap.add_argument("--url", required=True)
    ap.add_argument("--state", type=Path, required=True, help="relay's own append-only acknowledgement database")
    ap.add_argument("--allow-host", action="append", default=[], help="explicitly allow a non-loopback host (operator decision)")
    ap.add_argument("--timeout", type=float, default=5.0)
    a = ap.parse_args()
    try:
        report = relay(a.db, a.sink, a.url, a.state, timeout=a.timeout, allow_hosts=frozenset(a.allow_host))
    except RelayError as exc:
        print("REFUSED:", exc, file=sys.stderr)
        return 2
    print(json.dumps(report, indent=2, sort_keys=True))
    return 1 if report["failed"] else 0


if __name__ == "__main__":
    sys.exit(main())
