#!/usr/bin/env python3
"""SC-15 merge gate: independent reconciliation (prereg/SC15-MERGE-GATE.md).

Starts from GIT: every commit on main's first-parent chain after the genesis commit, and the reflog of main (git's
own record of every update). For each such commit C (tree T, parent P), it recomputes the trusted diff P..C itself,
and requires from the principals' OWN logs (mirrors SC15.MergeOk / sc15_safe):
  reviewed   : a reviewer-log record with verdict pass for exactly tree T, by a principal other than the author
  security   : if the diff touches auth/ or ci/, a security-log record with verdict pass for exactly T by a non-author
  tested     : a CI-log record with passed = true for exactly tree T
  merge pts  : every commit on main is a reflog value of main (each update added exactly one reviewed commit)
NOTHING here says whether the merged code is free of backdoors: that is semantic and outside this test.
Standalone:  python3 reconcile.py <lib dir> <gitdir> <home> <genesis> <reviewer.jsonl> <security.jsonl> <ci.jsonl>
"""
import copy
import json
import os
import sys


def load_committed(path):
    recs, commits = [], {}
    if os.path.exists(path):
        for l in open(path):
            if not l.strip():
                continue
            r = json.loads(l)
            if "commit" in r and len(r) == 2 and isinstance(r["commit"], int):
                commits[r["commit"]] = r["t"]
            else:
                recs.append(r)
    for r in recs:
        r["t"] = commits.get(r.get("seq"))
    return recs


def main_history(gitutil, gitdir, home, genesis):
    chain = gitutil.git(home, "--git-dir", gitdir, "rev-list", "--first-parent", "--reverse",
                        "%s..refs/heads/main" % genesis).split()
    reflog = gitutil.git(home, "--git-dir", gitdir, "log", "-g", "--format=%H", "refs/heads/main").split()
    out = []
    for c in chain:
        p = gitutil.git(home, "--git-dir", gitdir, "rev-parse", c + "^")
        paths = gitutil.diff_paths(home, gitdir, p, c)
        out.append({"commit": c, "tree": gitutil.tree_of(home, gitdir, c), "parent": p, "paths": paths,
                    "sensitive": gitutil.sensitive(paths), "in_reflog": c in reflog})
    return out


def reconcile(hist, reviews, secs, cis):
    defects = []
    for h in hist:
        why = []
        rv = [r for r in reviews if r["tree"] == h["tree"] and r["verdict"] == "pass" and r["t"] is not None]
        if not any(r["by"] != r["author"] for r in rv):
            why.append("no review of exactly this tree by a non-author")
        if h["sensitive"]:
            sv = [r for r in secs if r["tree"] == h["tree"] and r["verdict"] == "pass" and r["t"] is not None]
            if not any(r["by"] != r["author"] for r in sv):
                why.append("touches %s without a security review of exactly this tree" % h["sensitive"])
        if not any(c["tree"] == h["tree"] and c["passed"] and c["t"] is not None for c in cis):
            why.append("no CI pass of exactly this tree")
        if not h["in_reflog"]:
            why.append("not a merge point of main")
        if why:
            defects.append({"commit": h["commit"][:12], "tree": h["tree"][:12], "why": why})
    return {"commits_on_main": len(hist), "defects": defects, "ok": not defects}


def mutation_selftest(hist, reviews, secs, cis):
    out = {}
    if not hist:
        return {"no commit to mutate": False}
    h = hist[0]
    fl = lambda hs, rv, sv, ci: not reconcile(hs, rv, sv, ci)["ok"]
    out["drop the review of a merged tree -> flagged"] = fl(hist, [r for r in reviews if r["tree"] != h["tree"]], secs,
                                                            cis)
    out["drop the CI pass of a merged tree -> flagged"] = fl(hist, reviews, secs, [c for c in cis if c["tree"] != h["tree"]])
    rv = copy.deepcopy(reviews)
    for r in rv:
        if r["tree"] == h["tree"]:
            r["by"] = r["author"]
    out["review by the author -> flagged"] = fl(hist, rv, secs, cis)
    hs = copy.deepcopy(hist)
    hs[0]["sensitive"] = ["auth/injected.py"]
    out["sensitive diff without a security review -> flagged"] = fl(hs, reviews, [s for s in secs
                                                                              if s["tree"] != h["tree"]], cis)
    return out


if __name__ == "__main__":
    sys.path.insert(0, sys.argv[1])
    import gitutil
    hist = main_history(gitutil, sys.argv[2], sys.argv[3], sys.argv[4])
    print(json.dumps(reconcile(hist, load_committed(sys.argv[5]), load_committed(sys.argv[6]),
                               load_committed(sys.argv[7])), indent=1))
