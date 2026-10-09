"""Fidelity countermodel: the broker's shared counters and quota are observable.

Run from repository root:
    PYTHONPATH=. python3 reviews/trusted-stack-shared-state-countermodel.py

This exercises Controller and server.run_one directly. It does NOT test SO_PEERCRED
or prove anything about a deployed process sandbox. All signatures and leases are
granted by distinct designated trusted roles *before* the adversary chooses its
message. The only effects here are SQLite release rows.

Source audit: jwcodes12/control-stack @ 1ace0787b6c77a669c7a35b1e3e311d53b64b3dd.
"""
from pathlib import Path
from tempfile import TemporaryDirectory

from trusted_stack.controller import Controller, Denied, Principals
from trusted_stack.server import run_one

SENDER = 11001
RECEIVER = 11002
REVIEWER = 12001
APPROVER = 13001
ADMIN = 14001
PRINCIPALS = Principals(
    agents=frozenset((SENDER, RECEIVER)),
    reviewers=frozenset((REVIEWER,)),
    approvers=frozenset((APPROVER,)),
    admins=frozenset((ADMIN,)),
)


def new_broker(folder: str, cap: int) -> tuple[Controller, str]:
    c = Controller.bootstrap(Path(folder) / "control.sqlite3", PRINCIPALS, cap, clock=lambda: 100)
    digest = c.stage(SENDER, b"preapproved benign content")
    c.review(REVIEWER, digest)
    return c, digest


def preapprove(c: Controller, digest: str, agent: int, lease: str, count: int) -> None:
    c.issue_lease(ADMIN, lease, agent, count, 200)
    for i in range(count):
        c.approve(APPROVER, f"n-{lease}-{i}", digest, "approved/sink", agent, lease, 200)


def thirty_two_bit_observation(secret: int) -> None:
    assert 0 <= secret < 2**32
    with TemporaryDirectory() as tmp:
        c, digest = new_broker(tmp, 32)
        preapprove(c, digest, SENDER, "sender", 32)
        before = run_one(c, RECEIVER, {"op": "state"})["releases"]
        recovered = 0
        for i in range(32):
            if (secret >> i) & 1:
                c.release(SENDER, f"n-sender-{i}", digest, "approved/sink", "sender")
            after = run_one(c, RECEIVER, {"op": "state"})["releases"]
            bit = after - before
            assert bit in (0, 1)
            recovered |= bit << i
            before = after
        assert recovered == secret, (recovered, secret)


def quota_denial_signal(bit: int) -> None:
    """Even hiding state() leaves a 1-bit channel through shared capacity."""
    assert bit in (0, 1)
    with TemporaryDirectory() as tmp:
        c, digest = new_broker(tmp, 1)
        preapprove(c, digest, SENDER, "sender", 1)
        preapprove(c, digest, RECEIVER, "receiver", 1)
        if bit:
            c.release(SENDER, "n-sender-0", digest, "approved/sink", "sender")
        try:
            c.release(RECEIVER, "n-receiver-0", digest, "approved/sink", "receiver")
            receiver_allowed = True
        except Denied:
            receiver_allowed = False
        assert receiver_allowed == (bit == 0), (bit, receiver_allowed)


if __name__ == "__main__":
    for secret in (0, 1, 0x12345678, 0xFFFFFFFF, 0xA5A5A5A5):
        thirty_two_bit_observation(secret)
    for bit in (0, 1):
        quota_denial_signal(bit)
    print("PASS: countermodel observed shared-counter and shared-quota channels")
