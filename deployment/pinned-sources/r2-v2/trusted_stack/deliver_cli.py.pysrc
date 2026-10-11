"""Trusted, one-shot local effect dispatcher (never an agent-facing RPC).

Example, in a dedicated, isolated trusted OS owner context:
  python3 -m trusted_stack.deliver_cli --db /private/gate.db \
    --out /private/effects --release-id 1 \
    --agents 1001 --reviewers 1002 --approvers 1003 --admins 1004
The controller database and receiver directory must ALREADY exist with
private broker-owned permissions; this CLI cannot bootstrap either.
"""
import argparse
import os
import sys
from pathlib import Path

from trusted_stack.controller import Controller, Denied, Principals
from trusted_stack.outbox_receiver import deliver_record


def _uids(raw):
    try:
        values = raw.split(",")
        if any(not x or not x.isascii() or not x.isdecimal() for x in values):
            raise ValueError()
        result = frozenset(int(x) for x in values)
        if not result or any(x < 0 or x > 2**32 - 1 for x in result):
            raise ValueError()
        return result
    except ValueError as exc:
        raise argparse.ArgumentTypeError("invalid numeric UID role set") from exc


def main():
    p = argparse.ArgumentParser(description="Trusted fixed-file receiver only")
    p.add_argument("--db", type=Path, required=True)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--release-id", type=int, required=True)
    for role in ("agents", "reviewers", "approvers", "admins"):
        p.add_argument("--" + role, type=_uids, required=True)
    a = p.parse_args()
    try:
        principals = Principals(
            agents=a.agents, reviewers=a.reviewers,
            approvers=a.approvers, admins=a.admins)
        # The current process must be the trusted DB-owning OS UID. The role
        # flags do NOT grant rights: Controller._open validates actual UID.
        if not principals.allows(os.geteuid(), "admins"):
            raise Denied("current OS principal is not an admin")
        controller = Controller(a.db, principals)
        path = deliver_record(controller, a.release_id, a.out)
    except (Denied, ValueError, OSError):
        print("DENIED", file=sys.stderr)
        raise SystemExit(1)
    print(path)


if __name__ == "__main__":
    main()
