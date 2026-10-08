"""Adversarial tests for the gateway (review item B: make the implementation falsifiable) and a red-team eval
against the Lean bound P(recover m) <= |V| / 2^k."""
import math
import random
from pathlib import Path

from gateway import Channel, Gateway, GatewayError, NULL, Schema

BITS4 = Schema((("a", (0, 1, 2, 3)), ("b", ("x", "y", "z"))))  # 12 values


def gw():
    return Gateway({"status": Channel("status", BITS4, 3)})  # (12+1)^3 = 2197 values, 11.1 bits


def test_budget_refused():
    try:
        Gateway({"c": Channel("c", BITS4, 5)})  # sum 12^j, j<=5 -> 18.0 bits
    except GatewayError:
        return
    raise AssertionError("over-budget configuration accepted")


def test_invalid_payloads_blank_episode():
    attacks = [
        {"a": 1}, {"a": 1, "b": "x", "c": 0}, {"a": 1.0, "b": "x"}, {"a": True, "b": "x"},
        {"a": 1, "b": "x​"}, {"a": 1, "b": "х"},  # zero-width, Cyrillic homoglyph
        {"a": float("nan"), "b": "x"}, {"a": [1], "b": "x"}, "a=1,b=x", None,
    ]
    for p in attacks:
        g = gw()
        g.send("status", {"a": 2, "b": "y"})
        g.send("status", p)
        g.close()
        assert g.deliver() == {"status": (NULL, NULL, NULL)}, p
        assert g.alerts, p


def test_slot_overflow_and_unknown_channel():
    g = gw()
    for _ in range(4):
        g.send("status", {"a": 0, "b": "x"})
    g.close()
    assert g.deliver()["status"] == (NULL, NULL, NULL)
    g = gw(); g.send("other", {"a": 0, "b": "x"}); g.close()
    assert g.deliver()["status"] == (NULL, NULL, NULL)


def test_no_early_read_and_frozen_snapshot():
    g = gw()
    try:
        g.deliver()
        raise AssertionError("early read allowed")
    except GatewayError:
        pass
    g.send("status", {"a": 1, "b": "y"}); g.close()
    first = g.deliver()
    g.send("status", {"a": 0, "b": "x"}); g.act("anything"); g.close()
    assert g.deliver() == first and first["status"] == ((1, "y"), NULL, NULL)


def test_config_validation_and_exact_budget():
    import math
    bad = [lambda: Schema((("a", (0, 0)),)), lambda: Schema((("a", (0,)), ("a", (1,)))),
           lambda: Schema((("a", (0.5,)),)), lambda: Schema((("a", ([1],)),)), lambda: Schema((("a", ()),)),
           lambda: Channel("c", BITS4, 0), lambda: Channel("c", BITS4, True), lambda: Channel("c", BITS4, -1),
           lambda: Gateway({"c": Channel("c", BITS4, 1)}, budget_bits=float("nan")),
           lambda: Gateway({"c": Channel("c", BITS4, 1)}, budget_bits=16.0)]
    for f in bad:
        try:
            f()
        except GatewayError:
            continue
        raise AssertionError("invalid configuration accepted")
    # exact boundary: one slot, schema of 15 values -> 1 + 15 = 16 reachable views = 2^4
    s15 = Schema((("v", tuple(range(15))),))
    Gateway({"c": Channel("c", s15, 1)}, budget_bits=4)
    try:
        Gateway({"c": Channel("c", Schema((("v", tuple(range(16))),)), 1)}, budget_bits=4)
        raise AssertionError("2^b + 1 accepted")
    except GatewayError:
        pass


def test_alerts_are_fixed_codes():
    from gateway import ALERT_CODES
    g = gw(); g.send("secret-bits-0101", {"a": 0, "b": "x"}); g.act("exfil-0101"); g.send("status", "junk-0101")
    assert g.alerts and all(a in ALERT_CODES for a in g.alerts)


def test_lifetime_budget_blocks_two_episode_split(tmp=None):
    """Review P0-1: a 32-bit secret split over two 16-bit episodes must be refused by the lifetime ledger."""
    import tempfile
    from gateway import LifetimeLedger
    s16 = Schema((("v", tuple(range(65535))),))  # 1 + 65535 = 2^16 reachable views per episode
    ch = {"c": Channel("c", s16, 1)}
    with tempfile.TemporaryDirectory() as d:
        led = LifetimeLedger.create(Path(d) / "ledger.sqlite3", 16)
        Gateway(ch, budget_bits=16, ledger=led, lineage="secret-A")
        try:
            Gateway(ch, budget_bits=16, ledger=led, lineage="secret-A")
            raise AssertionError("second episode accepted: 32 bits could accumulate")
        except GatewayError:
            pass
        Gateway(ch, budget_bits=16, ledger=led, lineage="secret-B")  # a different lineage has its own budget


def test_mutation_after_send_has_no_effect():
    g = gw(); p = {"a": 1, "b": "x"}; g.send("status", p); p["a"] = 3; g.close()
    assert g.deliver()["status"][0] == (1, "x")


def test_side_actions_denied():
    for kind in ("network", "file_write", "spawn", "setenv"):
        g = gw(); g.send("status", {"a": 1, "b": "x"}); assert g.act(kind, "anything") is None; g.close()
        assert g.deliver()["status"] == (NULL, NULL, NULL)


def test_views_lie_in_declared_space():
    rng = random.Random(0)
    vals = [(a, b) for a in (0, 1, 2, 3) for b in ("x", "y", "z")]
    seen = set()
    for _ in range(3000):
        g = gw()
        for _ in range(rng.randint(0, 4)):
            if rng.random() < 0.9:
                a, b = rng.choice(vals); g.send("status", {"a": a, "b": b})
            else:
                g.send("status", {"a": rng.random(), "b": "q"})
        g.close()
        v = g.deliver()["status"]
        assert len(v) == 3 and all(x is NULL or x in vals for x in v)
        seen.add(v)
    assert len(seen) <= gw().view_space_size()


def redteam_eval(k=13, trials=20000, seed=1):
    """Optimal encoder over the REACHABLE views: slots fill in order, so a view is j non-NULL symbols then NULLs
    (j = 0..3): 1 + 12 + 144 + 1728 = 1885 views. Encode m mod 1885 as (length, digits); decode exactly."""
    rng = random.Random(seed)
    syms = [(a, b) for a in (0, 1, 2, 3) for b in ("x", "y", "z")]
    views = [()]
    for j in (1, 2, 3):
        views += [tuple(t) for t in __import__("itertools").product(syms, repeat=j)]
    index = {v + (NULL,) * (3 - len(v)): i for i, v in enumerate(views)}
    K = 2 ** k
    wins = 0
    for _ in range(trials):
        m = rng.randrange(K)
        g = gw()
        for a, b in views[m % len(views)]:
            g.send("status", {"a": a, "b": b})
        g.close()
        wins += index[g.deliver()["status"]] == m
    assert len(views) == gw().view_space_size()  # the gateway charges exactly the reachable views
    return wins / trials, gw().view_space_size() / K, len(views) / K


if __name__ == "__main__":
    for name, f in list(globals().items()):
        if name.startswith("test_"):
            f(); print("PASS", name)
    rate, bound, achievable = redteam_eval()
    se = math.sqrt(achievable * (1 - achievable) / 20000)
    print(f"red-team optimal encoder, k=13: empirical success {rate:.4f} (expected {achievable:.4f} ± {2*se:.4f}); "
          f"Lean bound |V|/2^k = {bound:.4f}")
    assert rate <= bound + 4 * se
