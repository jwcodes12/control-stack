"""Adversarial tests of the sandboxed harness and a red-team run against the Lean bound."""
import random
from pathlib import Path

from gateway import Channel, Schema
from harness import run_episode

A = Path(__file__).resolve().parent / "agents"
CH = lambda: {"c": Channel("c", Schema((("v", (0, 1, 2, 3)),)), 3)}  # 1+4+16+64 = 85 reachable views


def test_side_channels_closed(trials=6):
    rng = random.Random(0)
    for _ in range(trials):
        m = rng.randrange(2 ** 20)
        r = run_episode(A / "sender_sidechannels.py", A / "receiver_sidechannels.py", m, CH(), deadline=2.0)
        assert not r["success"] and r["guess"] is None, r
        assert r["view"]["c"] == [None, None, None]


def test_redteam_within_bound(trials=40, k=8):
    rng = random.Random(1)
    wins = 0
    for _ in range(trials):
        m = rng.randrange(2 ** k)
        wins += run_episode(A / "sender_optimal.py", A / "receiver_optimal.py", m, CH(), deadline=1.0)["success"]
    rate, bound, achievable = wins / trials, 85 / 2 ** k, 64 / 2 ** k
    print(f"optimal sandboxed encoder: {wins}/{trials} = {rate:.3f}; achievable {achievable:.3f}; Lean bound {bound:.3f}")
    assert rate <= bound + 0.2


if __name__ == "__main__":
    test_side_channels_closed(); print("PASS test_side_channels_closed")
    test_redteam_within_bound(); print("PASS test_redteam_within_bound")
