#!/usr/bin/env python3
"""SC-16 deploy admission: independent reconciliation (prereg/SC16-DEPLOY-ADMISSION.md).

Starts from the FILES actually present in the target directories, hashes each one, and checks it against the
reviewer's and approver's OWN logs (signatures re-verified with their public keys) and the registry's stager index.
The admission controller's deploy log is used only to attribute a file to an approval nonce. For every deployed
file f with SHA-256 h in target T, mirroring `SC16.DepOk` / `sc16_reviewed_content` / `SC16Disjoint`:
  logged      : the deploy log names f
  approved    : the approver log holds an approval with f's nonce, digest = h and target = T, whose signature
                verifies under the approver key
  reviewed    : the reviewer log holds a passing review of digest h for target T, signature valid under the
                reviewer key, by a reviewer who is not h's stager (registry index)
  one-use     : no nonce attributed to two files
Standalone:  python3 reconcile.py <stack dir> <reviewer pub> <approver pub>
"""
import copy
import hashlib
import json
import os
import subprocess
import sys
import tempfile

OPENSSL = "/usr/bin/openssl"


def load(path):
    recs, commits = [], {}
    if not os.path.exists(path):
        return []
    for line in open(path):
        line = line.strip()
        if not line:
            continue
        r = json.loads(line)
        if "commit" in r:
            commits[r["commit"]] = r["t"]
        else:
            recs.append(r)
    for r in recs:
        if "seq" in r:
            r["t"] = commits.get(r["seq"])
    return recs


def load_index(path):
    out = {}
    if os.path.exists(path):
        for line in open(path):
            r = json.loads(line)
            if r["ev"] == "put" and r["digest"] not in out:
                out[r["digest"]] = r["stager"]
    return out


class Verifier:
    def __init__(self, tmpdir):
        self.tmp, self.cache = tmpdir, {}

    def __call__(self, pub, msg, sig_hex):
        k = (pub, msg, sig_hex)
        if k not in self.cache:
            try:
                sig = bytes.fromhex(sig_hex or "")
            except ValueError:
                self.cache[k] = False
                return False
            with tempfile.NamedTemporaryFile(dir=self.tmp, delete=False) as m, \
                    tempfile.NamedTemporaryFile(dir=self.tmp, delete=False) as s:
                m.write(msg)
                s.write(sig)
            try:
                r = subprocess.run([OPENSSL, "pkeyutl", "-verify", "-pubin", "-inkey", pub, "-rawin", "-in", m.name,
                                    "-sigfile", s.name], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
                self.cache[k] = r.returncode == 0
            finally:
                os.unlink(m.name)
                os.unlink(s.name)
        return self.cache[k]


def scan_targets(targets):
    files = []
    for t in sorted(os.listdir(targets)):
        for n in sorted(os.listdir(os.path.join(targets, t))):
            if n.startswith("."):
                continue
            data = open(os.path.join(targets, t, n), "rb").read()
            files.append({"file": "%s/%s" % (t, n), "target": t, "sha": hashlib.sha256(data).hexdigest()})
    return files


def reconcile(files, deploys, reviews, approvals, stagers, rpub, apub, verify):
    by_file = {d["file"]: d for d in deploys}
    defects, nonce_use = [], {}
    for f in files:
        d = by_file.get(f["file"])
        bad = []
        if d is None:
            bad.append("unlogged")
        else:
            nonce_use.setdefault(d["nonce"], []).append(f["file"])
            ok_a = any(a.get("verdict") == "approved" and a["nonce"] == d["nonce"] and a["digest"] == f["sha"] and
                       a["target"] == f["target"] and
                       verify(apub, ("sc16-approval|%s|%s|%s|%s" % (a["nonce"], a["digest"], a["target"],
                                                                    a.get("tag") or "")).encode(), a.get("sig"))
                       for a in approvals)
            if not ok_a:
                bad.append("no approval of exactly this digest and target")
        stager = stagers.get(f["sha"])
        good_r = [r for r in reviews if r.get("verdict") == "pass" and r["digest"] == f["sha"] and
                  r["target"] == f["target"] and
                  verify(rpub, ("sc16-review|%s|%s" % (r["digest"], r["target"])).encode(), r.get("sig"))]
        if not good_r:
            bad.append("unreviewed")
        elif not any(r["reviewer"] != stager for r in good_r):
            bad.append("reviewed only by its stager")
        if bad:
            defects.append({"file": f["file"], "sha": f["sha"][:16], "defects": bad})
    reused = {n: fs for n, fs in nonce_use.items() if len(fs) > 1}
    for n, fs in reused.items():
        for x in fs:
            defects.append({"file": x, "defects": ["approval nonce used twice"]})
    return {"files": len(files), "deploy_records": len(deploys), "defects": defects,
            "flagged_files": sorted({x["file"] for x in defects}), "ok": not defects}


def mutation_selftest(files, deploys, reviews, approvals, stagers, rpub, apub, verify):
    out = {}
    if not files:
        return {"no deployed file to mutate": False}
    f = files[0]
    fl = lambda *args: f["file"] in reconcile(*args, rpub, apub, verify)["flagged_files"]
    out["drop the review -> flagged"] = fl(files, deploys, [r for r in reviews if r["digest"] != f["sha"]], approvals,
                                          stagers)
    fs = copy.deepcopy(files)
    fs[0]["sha"] = hashlib.sha256(b"different bytes").hexdigest()
    out["deployed bytes differ from the reviewed digest -> flagged"] = fl(fs, deploys, reviews, approvals, stagers)
    ap = copy.deepcopy(approvals)
    for a in ap:
        if a.get("digest") == f["sha"]:
            a["target"] = "prod" if f["target"] == "staging" else "staging"
    out["approval for another target -> flagged"] = fl(files, deploys, reviews, ap, stagers)
    rv = copy.deepcopy(reviews)
    for r in rv:
        if r.get("digest") == f["sha"]:
            r["sig"] = "00" * 64
    out["corrupted review signature -> flagged"] = fl(files, deploys, rv, approvals, stagers)
    st = dict(stagers)
    st[f["sha"]] = next((r["reviewer"] for r in reviews if r.get("digest") == f["sha"]), "reviewer-1")
    out["reviewer is the stager -> flagged"] = fl(files, deploys, reviews, approvals, st)
    dep = copy.deepcopy(deploys)
    d0 = [d for d in dep if d["file"] == f["file"]][0]
    dup = dict(d0, file=f["file"] + ".copy")
    fs2 = copy.deepcopy(files) + [dict(f, file=f["file"] + ".copy")]
    out["one approval nonce on two files -> flagged"] = fl(fs2, dep + [dup], reviews, approvals, stagers)
    return out


if __name__ == "__main__":
    stack, rpub, apub = sys.argv[1], sys.argv[2], sys.argv[3]
    with tempfile.TemporaryDirectory() as td:
        v = Verifier(td)
        r = reconcile(scan_targets(os.path.join(stack, "targets")), load(os.path.join(stack, "deploys.jsonl")),
                      load(os.path.join(stack, "reviewer.jsonl")), load(os.path.join(stack, "approver.jsonl")),
                      load_index(os.path.join(stack, "registry-index.jsonl")), rpub, apub, v)
    print(json.dumps(r, indent=1))
    sys.exit(0 if r["ok"] else 1)
