"""Adversarial tests for the gateway (review item B: make the implementation falsifiable) and a red-team eval
against the Lean bound P(recover m) <= |V| / 2^k."""
import math
import random

from gateway import Channel, Gateway, GatewayError, NULL, Schema

BITS4 = Schema((("a", (0, 1, 2, 3)), ("b", ("x", "y", "z"))))  # 12 values


def gw():
    return Gateway({"status": Channel("status", BITS4, 3)})  # (12+1)^3 = 2197 values, 11.1 bits


def test_budget_refused():
    try:
        Gateway({"c": Channel("c", BITS4, 5)})  # 13^5 -> 18.5 bits
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


def test_no_early_read_and_no_late_send():
    g = gw()
    try:
        g.deliver()
        raise AssertionError("early read allowed")
    except GatewayError:
        pass
    g.close(); g.send("status", {"a": 0, "b": "x"})
    assert g.deliver()["status"] == (NULL, NULL, NULL)


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
