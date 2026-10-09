#!/usr/bin/env python3
"""stackmap: map F1-F8 primitives and SC-01..SC-28 scenarios onto frontier-lab stack components.

Loads stack/components.json, validates it fail-closed, joins it with scenarios/SC-*/manifest.json and prints:

  (default)               component x family matrix, then per-component scenarios with manifest status and
                          blocking assumptions
  --matrix                only the component x family matrix
  --scenarios             only the per-component scenario join
  --gaps                  components with premises that no repo artifact discharges, by priority score
  --researcher ID         an actionable checklist for one component
  --json                  machine-readable output for any of the above
  --validate              validate only

Static only: standard library, no Lean, no subprocess, no network. Recorded evidence outcomes are NOT re-run.
Nothing printed here is a deployment or assurance claim.

Premise state (derived from the cited evidence, strongest first):
  REFUTED        some cited evidence (any kind) has outcome FAIL
  TESTED         some runtime evidence (harness/test/receipt) has outcome PASS or PARTIAL
  BUILT_NOT_RUN  runtime evidence exists but is recorded NOT_RUN
  MODELLED       only model evidence (lean/model_test) with PASS or PARTIAL
  GAP            no evidence at all (docs listed under `related` never count)

Component status is DERIVED and must equal the declared status (fail-closed):
  REFERENCE_TESTED  some premise has runtime evidence with outcome PASS, PARTIAL or FAIL
  MODEL_ONLY        otherwise, if the component cites a Lean model or any premise is MODELLED/BUILT_NOT_RUN
  NOT_STARTED       otherwise

Gap priority score (documented, deliberately simple; NOT a risk ranking):
  weight(premise) = 2 for GAP or REFUTED, 1 for MODELLED or BUILT_NOT_RUN, 0 for TESTED
  score = sum(weights) * (number of linked scenarios) / tier_cost(decisive_tier)
  tier_cost: commodity 1, gpu 3, datacenter 9
It favours open premises that block many scenarios and can be tested cheaply. Ties break by component id.

Exit codes: 0 ok; 1 invalid data (message on stderr); 2 usage error or unknown component.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parent.parent
FAMILIES = tuple(f"F{i}" for i in range(1, 9))
STATUSES = ("MODEL_ONLY", "REFERENCE_TESTED", "NOT_STARTED")
TIER_COST = {"commodity": 1, "gpu": 3, "datacenter": 9}
LAYERS = {"research", "host", "build_deploy", "identity", "cloud", "cluster", "accelerator", "data", "network",
          "oversight", "response"}
ROLES = {"gate", "meter", "monitor", "attester", "approver", "halt", "verifier"}
MODEL_KINDS = {"lean", "model_test"}
RUNTIME_KINDS = {"harness", "test", "receipt"}
OUTCOMES = {"PASS", "FAIL", "PARTIAL", "NOT_RUN"}
WEIGHT = {"GAP": 2, "REFUTED": 2, "MODELLED": 1, "BUILT_NOT_RUN": 1, "TESTED": 0}
ID_RE = re.compile(r"[a-z][a-z0-9_]*\Z")
SC_RE = re.compile(r"SC-\d{2}\Z")
DECL_NAME = re.compile(r"[A-Za-z_][\w.']*\Z")

TOP_KEYS = {"schema_version", "note", "components"}
COMPONENT_KEYS = {"id", "name", "layer", "examples", "families", "scenarios", "trusted_component", "trusted_role",
                  "model", "premises", "related", "practical", "decisive_tier", "literature", "status",
                  "status_note", "researcher"}
PREMISE_KEYS = {"id", "text", "evidence", "necessity"}
EVIDENCE_KEYS = {"path", "kind", "outcome", "note"}
MODEL_KEYS = {"path", "decls", "note"}
NECESSITY_KEYS = {"path", "decls"}
PRACTICAL_KEYS = {"commodity", "gpu", "datacenter"}
RESEARCHER_KEYS = {"use_for", "provide", "run"}
# manifest axes that count as "not blocking"
CLEAR = {"proof": {"THEOREM_VERIFIED", "NOT_APPLICABLE"}, "evidence": {"RUNTIME_VALIDATED", "NOT_APPLICABLE"},
         "applicability": {"ESTABLISHED"}, "usefulness": {"MET_RECORDED", "NOT_APPLICABLE"}}
REFUTING = {"OBSERVED_FAILURE", "REFUTED"}


class Invalid(ValueError):
    pass


def need(ok, reason):
    if not ok:
        raise Invalid(reason)


def _unique_pairs(pairs):
    out = {}
    for k, v in pairs:
        need(k not in out, f"duplicate JSON key: {k}")
        out[k] = v
    return out


def load_json(path: Path):
    try:
        text = path.read_text(encoding="utf-8")
    except OSError as e:
        raise Invalid(f"cannot read {path}: {e}") from None
    try:
        return json.loads(text, object_pairs_hook=_unique_pairs)
    except json.JSONDecodeError as e:
        raise Invalid(f"invalid JSON in {path}: {e}") from None


def safe_path(root: Path, name, where, allow_dir=False) -> Path:
    need(isinstance(name, str) and name.strip() == name and name, f"{where}: empty or invalid path")
    p = PurePosixPath(name)
    need(not p.is_absolute() and ".." not in p.parts and "\\" not in name, f"{where}: unsafe path {name!r}")
    f = (root / p).resolve()
    rr = root.resolve()
    need(f == rr or rr in f.parents, f"{where}: path escapes repo: {name!r}")
    ok = f.is_file() or (allow_dir and f.is_dir())
    need(ok, f"{where}: cited path does not exist in repo: {name!r}")
    return f


def keys_exact(obj, required, where, optional=frozenset()):
    need(isinstance(obj, dict), f"{where}: expected object")
    missing = required - optional - obj.keys()
    extra = obj.keys() - required
    need(not missing, f"{where}: missing keys {sorted(missing)}")
    need(not extra, f"{where}: unknown keys {sorted(extra)}")


def nonempty_str(v, where):
    need(isinstance(v, str) and v.strip(), f"{where}: expected non-empty string")


def str_list(v, where, nonempty=True):
    need(isinstance(v, list), f"{where}: expected list")
    need(not nonempty or v, f"{where}: must be non-empty")
    for i, s in enumerate(v):
        nonempty_str(s, f"{where}[{i}]")
    need(len(set(v)) == len(v), f"{where}: duplicate entries")


def check_decls(root, path, decls, where):
    need(isinstance(decls, list), f"{where}.decls: expected list")
    if not decls:
        return
    need(path.endswith(".lean"), f"{where}: decls given for a non-Lean file {path!r}")
    src = (root / path).read_text(encoding="utf-8", errors="replace")
    for d in decls:
        need(isinstance(d, str) and DECL_NAME.match(d), f"{where}: invalid declaration name {d!r}")
        pat = (r"^[ \t]*(?:@\[[^\]]*\][ \t]*)?(?:(?:private|protected|noncomputable|nonrec)[ \t]+)*"
               r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|class)[ \t]+(?:[\w.']*\.)?"
               + re.escape(d) + r"(?![\w.'])")
        need(re.search(pat, src, re.M), f"{where}: declaration {d!r} not found in {path}")


def load_manifest(root: Path, sid: str, cache: dict) -> dict:
    if sid in cache:
        return cache[sid]
    need(SC_RE.match(sid), f"invalid scenario id {sid!r}")
    mpath = root / "scenarios" / sid / "manifest.json"
    need(mpath.is_file(), f"scenario {sid} has no scenarios/{sid}/manifest.json")
    m = load_json(mpath)
    need(isinstance(m, dict), f"{sid}: manifest is not an object")
    need(m.get("id") == sid, f"{sid}: manifest id {m.get('id')!r} does not match folder")
    need(isinstance(m.get("status"), str) and m["status"], f"{sid}: manifest status missing")
    need(isinstance(m.get("assumptions"), list), f"{sid}: manifest assumptions missing")
    for a in m["assumptions"]:
        need(isinstance(a, dict) and isinstance(a.get("id"), str), f"{sid}: malformed assumption")
        for axis in CLEAR:
            need(isinstance(a.get(axis), str), f"{sid}: assumption {a.get('id')} lacks axis {axis}")
    cache[sid] = m
    return m


def premise_state(p: dict) -> str:
    ev = p["evidence"]
    if any(e["outcome"] == "FAIL" for e in ev):
        return "REFUTED"
    if any(e["kind"] in RUNTIME_KINDS and e["outcome"] in ("PASS", "PARTIAL") for e in ev):
        return "TESTED"
    if any(e["kind"] in RUNTIME_KINDS for e in ev):
        return "BUILT_NOT_RUN"
    if any(e["kind"] in MODEL_KINDS and e["outcome"] in ("PASS", "PARTIAL") for e in ev):
        return "MODELLED"
    return "GAP"


def derived_status(c: dict) -> str:
    if any(e["kind"] in RUNTIME_KINDS and e["outcome"] in ("PASS", "PARTIAL", "FAIL")
           for p in c["premises"] for e in p["evidence"]):
        return "REFERENCE_TESTED"
    if c["model"] or any(premise_state(p) in ("MODELLED", "BUILT_NOT_RUN") for p in c["premises"]):
        return "MODEL_ONLY"
    return "NOT_STARTED"


CMD_PATH = re.compile(r"^[A-Za-z_.][\w.\-]*(?:/[\w.\-]+)+/?$")  # repo-relative path tokens; skips 1/20, /tmp/x


def validate_component(root, c, i, manifests):
    where = f"components[{i}]"
    keys_exact(c, COMPONENT_KEYS, where)
    cid = c["id"]
    need(isinstance(cid, str) and ID_RE.match(cid), f"{where}: invalid id {cid!r}")
    where = f"component {cid}"
    for k in ("name", "trusted_component", "status_note"):
        nonempty_str(c[k], f"{where}.{k}")
    need(c["layer"] in LAYERS, f"{where}: unknown layer {c['layer']!r}")
    str_list(c["examples"], f"{where}.examples")
    str_list(c["literature"], f"{where}.literature")
    str_list(c["families"], f"{where}.families")
    for f in c["families"]:
        need(f in FAMILIES, f"{where}: unknown family {f!r}")
    str_list(c["scenarios"], f"{where}.scenarios")
    for s in c["scenarios"]:
        need(SC_RE.match(s), f"{where}: invalid scenario id {s!r}")
        load_manifest(root, s, manifests)
    str_list(c["trusted_role"], f"{where}.trusted_role")
    for r in c["trusted_role"]:
        need(r in ROLES, f"{where}: unknown trusted role {r!r}")
    need(c["decisive_tier"] in TIER_COST, f"{where}: unknown decisive_tier {c['decisive_tier']!r}")
    need(c["status"] in STATUSES, f"{where}: status {c['status']!r} not in {STATUSES}")

    need(isinstance(c["model"], list), f"{where}.model: expected list")
    for j, m in enumerate(c["model"]):
        w = f"{where}.model[{j}]"
        keys_exact(m, MODEL_KEYS, w, optional={"note"})
        safe_path(root, m["path"], w)
        need(m["path"].endswith(".lean"), f"{w}: model must be a Lean file")
        check_decls(root, m["path"], m["decls"], w)

    need(isinstance(c["premises"], list) and c["premises"], f"{where}.premises: must be a non-empty list")
    pids = set()
    for j, p in enumerate(c["premises"]):
        w = f"{where}.premises[{j}]"
        keys_exact(p, PREMISE_KEYS, w)
        need(isinstance(p["id"], str) and ID_RE.match(p["id"]), f"{w}: invalid premise id {p['id']!r}")
        need(p["id"] not in pids, f"{where}: duplicate premise id {p['id']!r}")
        pids.add(p["id"])
        nonempty_str(p["text"], f"{w}.text")
        need(isinstance(p["evidence"], list), f"{w}.evidence: expected list")
        for k, e in enumerate(p["evidence"]):
            we = f"{w}.evidence[{k}]"
            keys_exact(e, EVIDENCE_KEYS, we, optional={"note"})
            safe_path(root, e["path"], we)
            need(e["kind"] in MODEL_KINDS | RUNTIME_KINDS, f"{we}: unknown kind {e['kind']!r}")
            need(e["outcome"] in OUTCOMES, f"{we}: unknown outcome {e['outcome']!r}")
            if e["kind"] == "lean":
                need(e["path"].endswith(".lean"), f"{we}: kind lean on a non-Lean file")
            if "note" in e:
                nonempty_str(e["note"], f"{we}.note")
        need(isinstance(p["necessity"], list), f"{w}.necessity: expected list")
        for k, n in enumerate(p["necessity"]):
            wn = f"{w}.necessity[{k}]"
            keys_exact(n, NECESSITY_KEYS, wn)
            safe_path(root, n["path"], wn)
            need(n["decls"], f"{wn}: a necessity witness must name a declaration")
            check_decls(root, n["path"], n["decls"], wn)

    str_list(c["related"], f"{where}.related", nonempty=False)
    for r in c["related"]:
        safe_path(root, r, f"{where}.related")

    keys_exact(c["practical"], PRACTICAL_KEYS, f"{where}.practical")
    nonempty_str(c["practical"]["commodity"], f"{where}.practical.commodity")
    for k in ("gpu", "datacenter"):
        v = c["practical"][k]
        need(v is None or (isinstance(v, str) and v.strip()), f"{where}.practical.{k}: string or null")
    need(c["practical"][c["decisive_tier"]] is not None,
         f"{where}: decisive_tier {c['decisive_tier']} has no practical test described")

    keys_exact(c["researcher"], RESEARCHER_KEYS, f"{where}.researcher")
    nonempty_str(c["researcher"]["use_for"], f"{where}.researcher.use_for")
    str_list(c["researcher"]["provide"], f"{where}.researcher.provide")
    str_list(c["researcher"]["run"], f"{where}.researcher.run")
    for cmd in c["researcher"]["run"]:
        for tok in cmd.split():
            tok = tok.strip("'\"")
            if CMD_PATH.match(tok):
                safe_path(root, tok, f"{where}.researcher.run", allow_dir=True)

    d = derived_status(c)
    need(d == c["status"], f"{where}: declared status {c['status']} but cited evidence supports {d}")


def load(root: Path, components_path: Path | None = None):
    """Validate everything; return (components, manifests). Raises Invalid (fail-closed)."""
    root = Path(root)
    cpath = components_path or root / "stack" / "components.json"
    data = load_json(cpath)
    need(isinstance(data, dict), "components file: expected object")
    keys_exact(data, TOP_KEYS, "components file", optional={"note"})
    need(data["schema_version"] == 1, f"unsupported schema_version {data['schema_version']!r}")
    comps = data["components"]
    need(isinstance(comps, list) and comps, "components: must be a non-empty list")
    manifests: dict = {}
    seen = set()
    for i, c in enumerate(comps):
        validate_component(root, c, i, manifests)
        need(c["id"] not in seen, f"duplicate component id {c['id']!r}")
        seen.add(c["id"])
    return comps, manifests


# ---------------------------------------------------------------- derived views

def blocking(a: dict) -> dict:
    return {axis: a[axis] for axis in CLEAR if a[axis] not in CLEAR[axis]}


def scenario_rows(c, manifests):
    rows = []
    for sid in c["scenarios"]:
        m = manifests[sid]
        blocks = []
        for a in m["assumptions"]:
            b = blocking(a)
            if b:
                blocks.append({"id": a["id"], "axes": b, "refuted": any(v in REFUTING for v in b.values())})
        rows.append({"id": sid, "title": m.get("title", ""), "status": m["status"],
                     "families": m.get("families", []), "blocking": blocks})
    return rows


def score(c) -> float:
    w = sum(WEIGHT[premise_state(p)] for p in c["premises"])
    return round(w * len(c["scenarios"]) / TIER_COST[c["decisive_tier"]], 2)


def gaps(comps):
    out = []
    for c in comps:
        states = {p["id"]: premise_state(p) for p in c["premises"]}
        open_ = [pid for pid, s in states.items() if s in ("GAP", "REFUTED")]
        if open_:
            out.append({"id": c["id"], "name": c["name"], "score": score(c), "decisive_tier": c["decisive_tier"],
                        "status": c["status"], "scenarios": c["scenarios"],
                        "gap_premises": [pid for pid in open_ if states[pid] == "GAP"],
                        "refuted_premises": [pid for pid in open_ if states[pid] == "REFUTED"],
                        "partial_premises": [pid for pid, s in states.items() if s in ("MODELLED", "BUILT_NOT_RUN")]})
    out.sort(key=lambda g: (-g["score"], g["id"]))
    return out


def matrix(comps):
    return [{"id": c["id"], "families": {f: f in c["families"] for f in FAMILIES}, "status": c["status"],
             "decisive_tier": c["decisive_tier"]} for c in comps]


def researcher(c, manifests):
    prem = []
    for p in c["premises"]:
        s = premise_state(p)
        if s == "TESTED":
            todo = "reference-tested only: re-run against YOUR component and record a new receipt"
        elif s == "REFUTED":
            todo = "refuted in the cited setting: change the configuration or narrow the claim, then re-measure"
        elif s == "BUILT_NOT_RUN":
            todo = "harness exists but no receipt: run it in a disposable host and record the receipt"
        elif s == "MODELLED":
            todo = "model-level only: build a runtime test with an independent observer"
        else:
            todo = "nothing in the repo: you must provide runtime evidence (harness + independent observer + receipt)"
        prem.append({"id": p["id"], "state": s, "text": p["text"], "todo": todo,
                     "evidence": p["evidence"], "necessity": p["necessity"]})
    return {"id": c["id"], "name": c["name"], "status": c["status"], "use_for": c["researcher"]["use_for"],
            "families": c["families"], "trusted_component": c["trusted_component"],
            "trusted_role": c["trusted_role"], "model": c["model"], "premises": prem,
            "provide": c["researcher"]["provide"], "run": c["researcher"]["run"], "practical": c["practical"],
            "decisive_tier": c["decisive_tier"], "literature": c["literature"],
            "scenarios": [{"id": r["id"], "status": r["status"]} for r in scenario_rows(c, manifests)]}


# ---------------------------------------------------------------- text rendering

def render_matrix(comps):
    w = max(len(c["id"]) for c in comps)
    lines = ["COMPONENT x FAMILY (x = primitive family used; status derived from cited evidence)",
             f"{'component':<{w}}  " + " ".join(FAMILIES) + "  status            tier"]
    for row in matrix(comps):
        cells = " ".join(" x" if row["families"][f] else " ." for f in FAMILIES)
        lines.append(f"{row['id']:<{w}} {cells}   {row['status']:<17} {row['decisive_tier']}")
    counts = {s: sum(c["status"] == s for c in comps) for s in STATUSES}
    lines.append("totals: " + ", ".join(f"{k}={v}" for k, v in counts.items()))
    return "\n".join(lines)


def render_scenarios(comps, manifests):
    lines = ["PER-COMPONENT SCENARIOS (manifest status; blocking assumptions as axis=value; ! = refuted/failed)"]
    for c in comps:
        lines.append(f"\n{c['id']}  [{c['status']}]  trusted: {c['trusted_component']}")
        for r in scenario_rows(c, manifests):
            lines.append(f"  {r['id']} {r['status']:<11} {r['title']}")
            all_open = [b["id"] for b in r["blocking"] if len(b["axes"]) == len(CLEAR) and not b["refuted"]]
            if all_open:
                lines.append(f"      - all four axes open: {', '.join(all_open)}")
            for b in r["blocking"]:
                if b["id"] in all_open:
                    continue
                ax = ", ".join(f"{k}={v}" for k, v in b["axes"].items())
                lines.append(f"      {'!' if b['refuted'] else '-'} {b['id']}: {ax}")
            if not r["blocking"]:
                lines.append("      (no blocking assumption recorded)")
    return "\n".join(lines)


def render_gaps(comps):
    lines = ["GAPS: premises with no discharging repo artifact (docs never count)",
             "score = (2*GAP + 2*REFUTED + 1*(MODELLED|BUILT_NOT_RUN)) * #scenarios / tier_cost"
             " [commodity 1, gpu 3, datacenter 9]; not a risk ranking"]
    for n, g in enumerate(gaps(comps), 1):
        lines.append(f"{n:>2}. {g['id']:<26} score {g['score']:>6}  tier {g['decisive_tier']:<10} "
                     f"{g['status']}  scenarios {' '.join(g['scenarios'])}")
        if g["refuted_premises"]:
            lines.append(f"      REFUTED: {', '.join(g['refuted_premises'])}")
        if g["gap_premises"]:
            lines.append(f"      GAP:     {', '.join(g['gap_premises'])}")
        if g["partial_premises"]:
            lines.append(f"      partial: {', '.join(g['partial_premises'])}")
    return "\n".join(lines)


def render_researcher(r):
    L = [f"RESEARCHER CHECKLIST: {r['name']} ({r['id']}) [{r['status']}]",
         f"To use {', '.join(r['families'])} for {r['use_for']}:",
         "  scenarios: " + ", ".join(f"{s['id']} ({s['status']})" for s in r["scenarios"]),
         f"1. Stand up the trusted component ({', '.join(r['trusted_role'])}): {r['trusted_component']}",
         "2. Instantiate the formal model (its premises are hypotheses, not facts):"]
    for m in r["model"] or [{"path": "(none in repo: write one under ControlStack/Scenarios/)", "decls": []}]:
        L.append(f"     {m['path']}" + (f"  [{', '.join(m['decls'])}]" if m["decls"] else ""))
    L.append("3. Discharge every premise (this tool cannot):")
    for p in r["premises"]:
        L.append(f"   [{p['state']}] {p['id']}: {p['text']}")
        for e in p["evidence"]:
            L.append(f"        evidence: {e['path']} ({e['kind']}, {e['outcome']})" +
                     (f" - {e['note']}" if e.get("note") else ""))
        for n in p["necessity"]:
            L.append(f"        load-bearing (necessity witness): {n['path']} [{', '.join(n['decls'])}]")
        L.append(f"        -> {p['todo']}")
    L.append("4. You must provide:")
    L += [f"   - {x}" for x in r["provide"]]
    L.append("5. Run:")
    L += [f"   $ {x}" for x in r["run"]]
    L.append(f"6. Practical test (decisive tier: {r['decisive_tier']}):")
    for k in ("commodity", "gpu", "datacenter"):
        if r["practical"][k]:
            L.append(f"   {k}: {r['practical'][k]}")
    L.append("7. Known attack/failure classes: " + "; ".join(r["literature"]))
    L.append("8. Record: preregister under prereg/, write a NEW non-overwriting receipt, update the scenario "
             "manifest from grounded evidence only, run python3 tools/check_scenarios.py. Nothing here promotes "
             "any status.")
    return "\n".join(L)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", type=Path, default=ROOT, help="repo root (default: this checkout)")
    ap.add_argument("--components", type=Path, help="components file (default: <root>/stack/components.json)")
    mode = ap.add_mutually_exclusive_group()
    mode.add_argument("--matrix", action="store_true")
    mode.add_argument("--scenarios", action="store_true")
    mode.add_argument("--gaps", action="store_true")
    mode.add_argument("--researcher", metavar="COMPONENT")
    mode.add_argument("--validate", action="store_true")
    ap.add_argument("--json", action="store_true")
    a = ap.parse_args(argv)
    try:
        comps, manifests = load(a.root, a.components)
    except Invalid as e:
        print(f"INVALID: {e}", file=sys.stderr)
        return 1
    if a.researcher is not None:
        match = [c for c in comps if c["id"] == a.researcher]
        if not match:
            print(f"unknown component {a.researcher!r}; known: {', '.join(c['id'] for c in comps)}",
                  file=sys.stderr)
            return 2
        r = researcher(match[0], manifests)
        print(json.dumps(r, indent=1) if a.json else render_researcher(r))
        return 0
    if a.validate:
        print(json.dumps({"valid": True, "components": len(comps)}) if a.json
              else f"OK: {len(comps)} components, {len(manifests)} scenarios joined")
        return 0
    if a.gaps:
        print(json.dumps(gaps(comps), indent=1) if a.json else render_gaps(comps))
        return 0
    if a.json:
        out = {}
        if not a.scenarios:
            out["matrix"] = matrix(comps)
        if not a.matrix:
            out["scenarios"] = {c["id"]: scenario_rows(c, manifests) for c in comps}
        print(json.dumps(out, indent=1))
        return 0
    parts = []
    if not a.scenarios:
        parts.append(render_matrix(comps))
    if not a.matrix:
        parts.append(render_scenarios(comps, manifests))
    print("\n\n".join(parts))
    return 0


if __name__ == "__main__":
    sys.exit(main())
