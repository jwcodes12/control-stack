"""Independent bounded transition oracle for the SQLite broker.

Compare admission AND every persistent table after each action, including denied
actions and reopen. This is a finite differential check, not Lean refinement or
crash/power-loss, trusted-clock, rollback or external-effect certification.
"""
import hashlib
import random
import sqlite3
import tempfile
import unittest
from pathlib import Path

from trusted_stack.controller import Controller, Denied, Principals
from trusted_stack.server import run_one

A, B, R, P, ADMIN, OUTSIDER = 101, 102, 201, 301, 401, 501
PRINCIPALS = Principals(frozenset({A, B}), frozenset({R}),
                        frozenset({P}), frozenset({ADMIN}))
BODIES = (b"first specimen", b"second specimen")
DIGESTS = tuple(hashlib.sha256(x).hexdigest() for x in BODIES)


class Model:
    def __init__(self):
        self.cap, self.spent, self.halted = 3, 0, False
        self.artifacts, self.reviews, self.leases, self.approvals = {}, {}, {}, {}
        self.releases = []

    def apply(self, uid, op, params, now):
        if op == "restart":
            return True
        if op == "halt":
            if uid != ADMIN:
                return False
            self.halted = True
            return True
        if self.halted:
            return False
        if op == "stage":
            if uid not in (A, B):
                return False
            body = params["body"]
            self.artifacts[hashlib.sha256(body).hexdigest()] = body
            return True
        if op == "review":
            digest = params["digest"]
            if uid != R or digest not in self.artifacts:
                return False
            self.reviews[digest] = uid
            return True
        if op == "issue_lease":
            key = params["lease_id"]
            owner, budget, expiry = (params[x] for x in ("agent_uid", "budget", "expires"))
            if (uid != ADMIN or owner not in (A, B) or key in self.leases
                    or budget < 1 or expiry <= now):
                return False
            self.leases[key] = [owner, budget, 0, expiry, 0]
            return True
        if op == "approve":
            nonce, digest, destination, owner, key, expiry = (params[x] for x in
                ("nonce", "digest", "destination", "agent_uid", "lease_id", "expires"))
            lease = self.leases.get(key)
            if (uid != P or owner not in (A, B) or nonce in self.approvals
                    or digest not in self.reviews or expiry <= now or lease is None
                    or lease[0] != owner or lease[3] <= now or lease[4]):
                return False
            self.approvals[nonce] = [digest, destination, owner, key, uid, expiry, 0]
            return True
        if op == "revoke":
            key = params["lease_id"]
            if uid != ADMIN or key not in self.leases:
                return False
            self.leases[key][4] = 1
            return True
        if op == "release":
            nonce, digest, dest, key, cost = (params[x] for x in
                ("nonce", "digest", "destination", "lease_id", "cost"))
            approval, lease = self.approvals.get(nonce), self.leases.get(key)
            # Derive authorization from the named facts, not SQL tuple order.
            facts = [uid in (A, B), approval is not None, lease is not None,
                     type(cost) is int and cost >= 1, digest in self.artifacts,
                     digest in self.reviews]
            if approval is not None:
                facts.extend([approval[0] == digest, approval[1] == dest,
                    approval[2] == uid, approval[3] == key, approval[4] == P,
                    approval[5] > now, approval[6] == 0])
            if lease is not None:
                facts.extend([lease[0] == uid, lease[3] > now, lease[4] == 0,
                    lease[2] + cost <= lease[1], self.spent + cost <= self.cap])
            if not all(facts):
                return False
            lease[2] += cost
            self.spent += cost
            approval[6] = 1
            self.releases.append((len(self.releases) + 1, digest, dest, uid,
                                  nonce, key, cost, now))
            return True
        raise AssertionError("oracle action missing")

    def snapshot(self):
        return {
            "meta": [(1, self.cap, int(self.halted), self.spent)],
            "artifacts": sorted(self.artifacts.items()),
            "reviews": sorted(self.reviews.items()),
            "leases": sorted((k, *v) for k, v in self.leases.items()),
            "approvals": sorted((k, *v) for k, v in self.approvals.items()),
            "releases": self.releases[:],
        }


def lease(key="l0", owner=A, budget=2, expires=110):
    return dict(lease_id=key, agent_uid=owner, budget=budget, expires=expires)


def approval(nonce="n0", digest=DIGESTS[0], dest="stage/first", owner=A,
             key="l0", expires=105):
    return dict(nonce=nonce, digest=digest, destination=dest, agent_uid=owner,
                lease_id=key, expires=expires)


def release(nonce="n0", digest=DIGESTS[0], dest="stage/first", key="l0", cost=1):
    return dict(nonce=nonce, digest=digest, destination=dest, lease_id=key, cost=cost)


PREFIX = [(100, A, "stage", dict(body=BODIES[0])),
          (100, R, "review", dict(digest=DIGESTS[0])),
          (100, ADMIN, "issue_lease", lease()),
          (100, P, "approve", approval())]


class TransitionTests(unittest.TestCase):
    def check_trace(self, trace):
        model = Model()
        now = [100]
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "state.sqlite3"
            gate = Controller.bootstrap(path, PRINCIPALS, model.cap, lambda: now[0])
            for index, (time, uid, op, params) in enumerate(trace):
                now[0] = time
                expected = model.apply(uid, op, params, time)
                try:
                    if op == "restart":
                        gate = Controller(path, PRINCIPALS, lambda: now[0])
                    else:
                        getattr(gate, op)(uid, **params)
                    actual = True
                except Denied:
                    actual = False
                context = (index, time, uid, op, params)
                self.assertEqual(actual, expected, context)
                with sqlite3.connect(path) as db:
                    snapshot = {table: sorted(db.execute("SELECT * FROM " + table).fetchall())
                                for table in model.snapshot()}
                db.close()
                self.assertEqual(snapshot, model.snapshot(), context)
                self.assertLessEqual(model.spent, model.cap)
                self.assertEqual(sum(row[6] for row in model.releases), model.spent)
                self.assertEqual(len({row[4] for row in model.releases}), len(model.releases))
                for key, row in model.leases.items():
                    self.assertLessEqual(row[2], row[1])
                    self.assertEqual(row[2], sum(r[6] for r in model.releases if r[5] == key))

    def test_boundaries_replay_roles_restart_and_halt(self):
        controls = [
            [(105, A, "release", release())],  # expiry is exclusive
            [(110, P, "approve", approval("n1", expires=120))],
            [(100, A, "release", release(dest="stage/other"))],
            [(100, B, "release", release())],
            [(100, OUTSIDER, "release", release())],
            [(100, A, "release", release(cost=3))],
            [(100, A, "release", release()), (100, A, "release", release())],
            [(100, ADMIN, "revoke", dict(lease_id="l0")), (100, A, "release", release())],
            [(100, ADMIN, "halt", {}), (100, A, "restart", {}), (100, A, "release", release())],
            [(100, A, "halt", {}), (100, A, "release", release())],
            [(100, A, "release", release()), (99, A, "restart", {}),
             (99, A, "release", release()), (99, P, "approve", approval())],
            [(100, A, "release", release(cost=2)),
             (100, ADMIN, "issue_lease", lease("l1", budget=2)),
             (100, P, "approve", approval("n1", key="l1")),
             (100, A, "release", release("n1", key="l1", cost=2)),
             (100, A, "release", release("n1", key="l1"))],
        ]
        for n, suffix in enumerate(controls):
            with self.subTest(control=n):
                self.check_trace(PREFIX + suffix)

    def test_seeded_joint_traces(self):
        # 64 reproducible histories; 4,544 attempted transitions including HALT.
        # Each starts live/provisioned, with HALT at the end to avoid mostly
        # trivial halted traces. Time may move backward, explicitly uncertified.
        for seed in range(64):
            rng = random.Random(seed)
            trace = PREFIX[:]
            for _ in range(64):
                key, nonce = rng.choice(("l0", "l1")), rng.choice(("n0", "n1", "n2"))
                owner = rng.choice((A, B))
                digest = rng.choice(DIGESTS)
                dest = rng.choice(("stage/first", "stage/second"))
                op, uid, params = rng.choice([
                    ("stage", rng.choice((A, B, R)), dict(body=rng.choice(BODIES))),
                    ("review", rng.choice((R, A)), dict(digest=digest)),
                    ("issue_lease", rng.choice((ADMIN, A)), lease(key, owner, rng.choice((1, 2, 4)))),
                    ("approve", rng.choice((P, A)), approval(nonce, digest, dest, owner, key)),
                    ("release", rng.choice((A, B, OUTSIDER)), release(nonce, digest, dest, key, rng.choice((1, 2, 4)))),
                    ("revoke", rng.choice((ADMIN, A)), dict(lease_id=key)),
                    ("restart", A, {}),
                ])
                trace.append((rng.choice((99, 100, 104, 105, 110)), uid, op, params))
            trace += [(100, ADMIN, "halt", {}), (100, A, "restart", {}),
                      (99, A, "release", release())]
            with self.subTest(seed=seed):
                self.check_trace(trace)

    def test_broker_cost_cannot_be_chosen_by_agent(self):
        with tempfile.TemporaryDirectory() as tmp:
            gate = Controller.bootstrap(Path(tmp) / "state", PRINCIPALS, 3, lambda: 100)
            with self.assertRaises(Denied):
                run_one(gate, A, {"op": "release", **release(cost=2)})

    def test_corrupt_reviewed_bytes_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "state.sqlite3"
            gate = Controller.bootstrap(path, PRINCIPALS, 3, lambda: 100)
            for _, uid, op, params in PREFIX:
                getattr(gate, op)(uid, **params)
            with sqlite3.connect(path) as db:
                db.execute("UPDATE artifacts SET body=? WHERE digest=?", (b"swapped bytes", DIGESTS[0]))
            db.close()
            with self.assertRaises(Denied):
                gate.release(A, **release())
            self.assertEqual(gate.state(ADMIN)["spent"], 0)
            self.assertEqual(gate.state(ADMIN)["releases"], 0)


if __name__ == "__main__":
    unittest.main()
