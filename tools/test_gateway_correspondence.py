#!/usr/bin/env python3
"""Independent finite-state differential checks for the concrete Python gateway.

These checks assert equality with a separately implemented *abstract* transition
model on enumerated traces. They do not certify all receiver observations or a
formal Lean/Python refinement. Only standard-library modules are used.
"""
from __future__ import annotations

import itertools
import json
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "gateway"))
from gateway import Channel, Gateway, GatewayError, LifetimeLedger, Schema


def reference_delivery(channels, trace):
    """Small transition specification derived from GatewayCore.gstep.

    State is (accepted prefix per channel, blanked, frozen view). This function
    never imports the production implementation and is independent of its state.
    """
    buffers = {c.name: [] for c in channels}
    config = {c.name: c for c in channels}
    blanked = False
    snapshot = None

    def render():
        if blanked:
            return {c.name: tuple(None for _ in range(c.slots)) for c in channels}
        return {c.name: tuple(buffers[c.name] + [None] * (c.slots - len(buffers[c.name])))
                for c in channels}

    for kind, name, payload in trace:
        if snapshot is not None:
            continue
        if kind == "close":
            snapshot = render()
        elif kind == "other":
            blanked = True
        elif kind == "send":
            c = config.get(name) if type(name) is str else None
            if c is None or len(buffers[c.name]) >= c.slots:
                blanked = True
            else:
                if type(payload) is not dict or set(payload) != {k for k, _ in c.schema.fields}:
                    blanked = True
                    continue
                vals = []
                for field, choices in c.schema.fields:
                    value = payload[field]
                    if not any(type(value) is type(v) and value == v for v in choices):
                        blanked = True
                        break
                    vals.append(value)
                else:
                    buffers[c.name].append(tuple(vals))
        else:
            raise AssertionError("unsupported model action")
    return snapshot if snapshot is not None else render()


def actual_delivery(channels, trace):
    gate = Gateway(channels, budget_bits=16)
    try:
        gate.deliver()
    except GatewayError:
        pass
    else:
        raise AssertionError("receiver should not see view before trusted close")
    for kind, name, payload in trace:
        if kind == "close":
            gate.close()
        elif kind == "other":
            gate.act()
        elif kind == "send":
            gate.send(name, payload)
        else:
            raise AssertionError("unsupported action")
    gate.close()
    return gate.deliver()


class GatewayCoreCorrespondenceTests(unittest.TestCase):
    @staticmethod
    def channels():
        return [Channel("repair", Schema((("id", (0, 1)),)), 1)]

    def test_exhaustive_single_channel_traces_up_to_length_five(self):
        cases = [
            ("send", "repair", {"id": 0}),
            ("send", "repair", {"id": 1}),
            ("send", "repair", {"id": 2}),
            ("send", "repair", {"id": True}),
            ("send", "unregistered", {"id": 0}),
            ("other", None, None),
            ("close", None, None),
        ]
        count = 0
        for length in range(6):
            for trace in itertools.product(cases, repeat=length):
                expected = reference_delivery(self.channels(), trace)
                actual = actual_delivery(self.channels(), trace)
                self.assertEqual(actual, expected, f"length={length} trace={trace}")
                count += 1
        self.assertEqual(count, sum(7 ** n for n in range(6)))

    def test_multiple_channels_and_multi_slot_traces(self):
        channels = [
            Channel("repair", Schema((("id", (0, 1)),)), 2),
            Channel("flag", Schema((("ok", (True, False)),)), 1),
        ]
        actions = [
            ("send", "repair", {"id": 0}), ("send", "repair", {"id": 1}),
            ("send", "repair", {"id": True}), ("send", "repair", {"id": 3}),
            ("send", "flag", {"ok": True}), ("send", "flag", {"ok": False}),
            ("send", "flag", {"ok": 1}), ("send", "unknown", {"id": 0}),
            ("other", None, None), ("close", None, None),
        ]
        for length in range(4):
            for trace in itertools.product(actions, repeat=length):
                self.assertEqual(actual_delivery(channels, trace),
                                 reference_delivery(channels, trace), repr(trace))

    def test_view_alphabet_is_constructively_reachable(self):
        channels = [
            Channel("repair", Schema((("id", (0, 1)),)), 2),
            Channel("flag", Schema((("ok", (True, False)),)), 1),
        ]
        observed = set()
        for a in [(), (0,), (1,), (0, 0), (0, 1), (1, 0), (1, 1)]:
            for b in [(), (True,), (False,)]:
                trace = [("send", "repair", {"id": v}) for v in a]
                trace += [("send", "flag", {"ok": v}) for v in b]
                v = actual_delivery(channels, trace)
                observed.add(tuple((k, v[k]) for k in sorted(v)))
        self.assertEqual(len(observed), 21)
        self.assertEqual(Gateway(channels).view_space_size(), 21)

    def test_original_sc01_exact_budget_and_durable_sixth_rejection(self):
        contract = json.loads((ROOT / "gateway/scenario/contract.json").read_text())
        self.assertEqual(contract["deadline_seconds"], 0.25)
        self.assertEqual(contract["episodes_per_lineage"], 5)
        self.assertEqual(contract["lifetime_view_cardinality"], 9 ** 5)
        self.assertLessEqual(9 ** 5, 2 ** 16)
        self.assertGreater(9 ** 6, 2 ** 16)
        channel = Channel("repair", Schema((("id", tuple(range(8))),)), 1)
        with tempfile.TemporaryDirectory() as directory:
            file = Path(directory) / "ledger.sqlite3"
            ledger = LifetimeLedger.create(file, 16)
            for episode in range(5):
                g = Gateway([channel], 16, ledger, "fixed-lineage", require_lifetime=True)
                g.send("repair", {"id": episode})
                g.close()
                self.assertEqual(g.deliver(), {"repair": ((episode,),)})
            self.assertEqual(LifetimeLedger(file, 16).usage("fixed-lineage"), (9 ** 5, 5))
            with self.assertRaises(GatewayError):
                Gateway([channel], 16, LifetimeLedger(file, 16),
                        "fixed-lineage", require_lifetime=True)
            self.assertEqual(LifetimeLedger(file, 16).usage("fixed-lineage"), (9 ** 5, 5))

    def test_historical_vm_usefulness_is_not_promoted(self):
        p = ROOT / "gateway/vm/receipts/usefulness-20261008-linkfix.json"
        receipt = json.loads(p.read_text())
        self.assertEqual(receipt["status"], "usefulness-failed")
        self.assertEqual(receipt["contract"]["deadline_seconds"], 0.25)
        self.assertEqual(len(receipt["records"]), 64)
        self.assertFalse(receipt["summary"]["usefulness_gate_passed"])
        for condition in ("baseline", "mediated"):
            result = receipt["summary"][condition]
            self.assertEqual(result["lifetimes"], 64)
            self.assertEqual(result["completed_lifetimes"], 0)
            self.assertEqual(result["completed_episodes"], 0)
            self.assertEqual(sum(bool(ep[condition]["sender_timed_out"])
                                 for row in receipt["records"] for ep in row["episodes"]), 320)
            self.assertEqual(sum(bool(ep[condition]["receiver_timed_out"])
                                 for row in receipt["records"] for ep in row["episodes"]), 320)


if __name__ == "__main__":
    unittest.main()
