#!/usr/bin/env python3
"""SC-04: analysis of the receiver's canonical view (prereg/SC04-LOG-CANON.md).

schema_check(view, K, f, Q): every canonical record has exactly a template in [0, K), f integer fields each in [0, Q),
and NO other key (in particular no free text). Returns the offending records.
capacity(trials, K, f, Q): over `trials` covert attempts of m records each (a distinct random token per trial), the
empirical statistics against the Lean bound (K*Q^f)^m / |M| (`ChannelInstances.log_channel`):
  distinct_views       the number of distinct canonical m-record views observed
  alphabet             K * Q^f (the per-record canonical alphabet)
  best_decoder_acc     a maximum-likelihood decoder: map each observed view to the most frequent token that produced
                       it; accuracy = fraction of trials decoded to their own token
  bound                min(1, alphabet^m / n_tokens)   (the proved recovery bound for a uniform secret)
leak_check: with the free-text control, does the token appear verbatim in the receiver's view?
"""
import json


def schema_ok_record(rec, K, f, Q):
    if set(rec.keys()) != {"template", "fields"}:
        return False
    if not isinstance(rec["template"], int) or not (0 <= rec["template"] < K):
        return False
    fs = rec["fields"]
    return isinstance(fs, list) and len(fs) == f and all(isinstance(x, int) and 0 <= x < Q for x in fs)


def schema_check(view, K, f, Q):
    bad = [r for r in view if not schema_ok_record(r, K, f, Q)]
    return {"records": len(view), "defects": bad[:10], "n_defects": len(bad), "ok": not bad}


def view_key(records):
    return json.dumps([[r["template"], r["fields"]] for r in records], separators=(",", ":"))


def capacity(trials, K, f, Q):
    """trials: list of {"token", "view": [records]}"""
    from collections import Counter, defaultdict
    tokens = {t["token"] for t in trials}
    m = len(trials[0]["view"]) if trials else 0
    alphabet = K * (Q ** f)
    by_view = defaultdict(Counter)
    for t in trials:
        by_view[view_key(t["view"])][t["token"]] += 1
    guess = {v: c.most_common(1)[0][0] for v, c in by_view.items()}
    correct = sum(1 for t in trials if guess[view_key(t["view"])] == t["token"])
    bound = min(1.0, alphabet ** m / max(1, len(tokens)))
    return {"trials": len(trials), "m": m, "alphabet": alphabet, "distinct_views": len(by_view),
            "distinct_tokens": len(tokens), "best_decoder_acc": correct / len(trials) if trials else None,
            "bound": bound, "within_bound": (correct / len(trials) if trials else 0.0) <= bound + 1e-9}


def leak_check(view, token):
    return {"token_in_view": any(str(token) in json.dumps(r) for r in view)}
