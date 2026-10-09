#!/usr/bin/env python3
"""SC-08 application allowlisting: independent reconciliation (prereg/SC08-EXEC-ALLOWLIST.md).

Two independent records of what ran:
  sentinel  every benign program appends {"name", "self_sha256"} to the sentinel file, hashing ITS OWN code as it
            was loaded (the file the interpreter actually ran) - written by the program, not by the launcher
  launcher  the launcher's own log of executions (program and script digests it hashed)
Rules (mirrors SC08.RunOk / safe_of_sound): every sentinel digest is on the script allowlist; every execution in the
launcher log ran an allowlisted interpreter WITH a script whose digest is allowlisted; and the number of sentinel
records equals the number of executions with a script (each benign program writes exactly one).
"""
import copy
import json
import os


def load_jsonl(path):
    return [json.loads(l) for l in open(path) if l.strip()] if os.path.exists(path) else []


def reconcile(allow, launcher, sentinel):
    defects = []
    for s in sentinel:
        if s["self_sha256"] not in allow["scripts"]:
            defects.append({"source": "sentinel", "name": s.get("name"), "why": "code that is not allowlisted ran",
                            "digest": s["self_sha256"][:16]})
    execs = [r for r in launcher if r.get("decision") == "executed"]
    for r in execs:
        why = []
        if r.get("script") is None:
            why.append("interpreter ran without a script")
        elif "script_digest" in r and r["script_digest"] not in allow["scripts"]:
            why.append("launcher executed a script whose digest is not allowlisted")
        if "program_digest" in r and r["program_digest"] not in allow["interpreters"]:
            why.append("launcher executed a program whose digest is not allowlisted")
        if why:
            defects.append({"source": "launcher", "seq": r["seq"], "why": why})
    with_script = sum(1 for r in execs if r.get("script") is not None and r.get("rc") == 0)
    consistent = with_script == len(sentinel)
    return {"executions": len(execs), "sentinel_records": len(sentinel), "consistent": consistent,
            "defects": defects, "ok": not defects and consistent}


def mutation_selftest(allow, launcher, sentinel):
    out = {}
    if sentinel:
        s = copy.deepcopy(sentinel)
        s[0]["self_sha256"] = "f" * 64
        out["a sentinel digest not on the allowlist -> flagged"] = not reconcile(allow, launcher, s)["ok"]
    ex = [r for r in launcher if r.get("decision") == "executed"]
    if ex:
        l = copy.deepcopy(launcher)
        for r in l:
            if r["seq"] == ex[0]["seq"]:
                r["script_digest"] = "e" * 64
        out["an executed script digest not on the allowlist -> flagged"] = not reconcile(allow, l, sentinel)["ok"]
        l = copy.deepcopy(launcher) + [dict(ex[0], seq=10 ** 6, script=None)]
        out["an interpreter run without a script -> flagged"] = not reconcile(allow, l, sentinel)["ok"]
        out["an execution without its sentinel -> flagged"] = not reconcile(allow, launcher, sentinel[1:])["ok"]
    return out
