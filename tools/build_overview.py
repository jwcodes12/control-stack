#!/usr/bin/env python3
"""Generate OVERVIEW.md, the landing page for someone opening the repository cold, ONLY from repository data.

    python3 tools/build_overview.py            # (re)write OVERVIEW.md
    python3 tools/build_overview.py --check    # write nothing; exit 1 if OVERVIEW.md would change (drift)
    python3 tools/build_overview.py --stdout   # print the page
    python3 tools/build_overview.py --lean-roots
                                               # also evaluate the trust roots in Lean (lake env lean, needs a built
                                               # ControlStack.Core.Cert) and fail if they differ from the text table

Sources (nothing is typed by hand except the fixed caveats and the commands in FIXED below):
- scenarios/*/manifest.json: titles, statuses, theorems, evidence entries, scope texts;
- Lean sources: theorem docstrings (tools/build_results.find_decl);
- recorded evidence JSON: prereg id and verdict (tools/build_results.summarise_json);
- tools/portfolio_ledger.build(): normalised premises, leverage, per-scenario open premises;
- ControlStack/Core/TrustRoot.lean: the generated `scenario_roots_table` (re-checked by `decide` whenever TrustRoot
  builds; `--lean-roots` re-evaluates it in Lean);
- tools/measured.py: exact one-sided Clopper-Pearson bounds of the recorded rates.

Choice rules (documented on the page):
- strongest formal result: the first manifest theorem matching, in order, (1) `*_safe_authenticated` (the
  credential premise discharged through the authenticated log), (2) a refinement (`concrete_*` or a path containing
  `Refinement`), (3) a name ending in `_safe` or containing `_safe_`, (4) the first listed theorem;
- top open premise: among the scenario's normalised premises, those without runtime evidence IN THIS scenario first,
  then the highest portfolio leverage, then the id;
- refinement theorems: `concrete_*` names or `Refinement` paths; liveness theorems: names matching LIVENESS_RE.
"""
import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "OVERVIEW.md"
TRUST_ROOT = ROOT / "ControlStack" / "Core" / "TrustRoot.lean"
sys.dont_write_bytecode = True
sys.path.insert(0, str(ROOT / "tools"))
import build_results as BR  # noqa: E402
import measured as MS  # noqa: E402
import portfolio_ledger as PL  # noqa: E402

LIVENESS_RE = re.compile(r"(progress|liveness|_completes\b|completes_|terminat)", re.I)
TOP_PREMISES = 10
DOC_MAX = 110
FIXED_CAVEATS = [
    "**No scenario is deployment-assured.** Every status is CONDITIONAL on stated premises; independent human review "
    "of statements and premises is open (AI reviews only so far).",
    "**Single host.** Runtime evidence comes from preregistered runs on one OCI ARM64 host, except where a page says "
    "otherwise.",
    "**Benign workloads unless noted.** Harnesses use scripted, benign, bounded workloads; LLM evaluations are "
    "sandboxed toy tasks.",
    "**Classical mathematics.** The Lean results are engineering formalisations of classical arguments (union bounds, "
    "binomial tails, total variation, invariants); no mathematical novelty is claimed.",
    "**Measured rates are population rates**, not per-history guarantees (docs/MEASUREMENT.md).",
]
VERIFY = [
    ("python3 tools/cstack.py check --fast", "generated pages, ledgers, manifests and unit tests (no Lean)"),
    ("python3 tools/cstack.py check --full", "adds `lake build ControlStack`, every scenario claim with its axioms, and "
                                             "the SC-26 case checker"),
    ("python3 tools/check_sc26_case.py", "independent recheck of the SC-26 case (Lean + recorded evidence)"),
    ("python3 tools/cstack.py evidence SC-XX", "a scenario's preregistrations and every evidence run's pinned hashes, "
                                               "verified against the pinned commit"),
    ("python3 tools/cstack.py status SC-XX", "one scenario in detail: theorems, evidence, open premises, done criteria"),
    ("python3 tools/measured.py", "exact one-sided bounds of every recorded rate, with caveats"),
    ("python3 tools/build_overview.py --check", "this page has not drifted from the data"),
]


def esc(s):
    return str(s).replace("|", "\\|").replace("\n", " ")


def manifests():
    out = {}
    for f in sorted((ROOT / "scenarios").glob("SC-*/manifest.json")):
        m = json.loads(f.read_text(encoding="utf-8"))
        out[m["id"]] = m
    return out


def short_name(name):
    return name.split(".")[-1]


def is_refinement(t):
    return short_name(t["name"]).startswith("concrete_") or "Refinement" in t["path"]


def strongest(m):
    ts = m["theorems"]
    rules = [lambda t: short_name(t["name"]).endswith("_safe_authenticated"), is_refinement,
             lambda t: short_name(t["name"]).endswith("_safe") or "_safe_" in short_name(t["name"])]
    for rule in rules:
        for t in ts:
            if rule(t):
                return t
    return ts[0] if ts else None


def doc_of(t):
    _, doc = BR.find_decl(t["name"], t["path"])
    if not doc:
        return "(no docstring)"
    return doc if len(doc) <= DOC_MAX else doc[:DOC_MAX - 3].rstrip() + "..."


def runtime_evidence(m):
    """[(prereg id, run label, verdict)] from the manifest's evidence entries under */evidence/run-*"""
    runs = {}                  # run dir -> (prereg id, label, verdict); an entry with a prereg id wins
    for e in m["evidence"]:
        p = e["path"]
        mt = re.search(r"(.*/evidence/(run-[^/]+))/", p)
        if not mt or not p.endswith(".json"):
            continue
        s = BR.summarise_json(p)
        pid = s[0] if s and s[0] else None
        verdict = (s[1] if s and s[1] else None) or e.get("outcome") or "?"
        label = mt.group(2) if mt.group(1).startswith("scenarios/%s/evidence" % m["id"]) else \
            mt.group(1).replace("scenarios/%s/" % m["id"], "")
        if mt.group(1) not in runs or (runs[mt.group(1)][0] == "?" and pid):
            runs[mt.group(1)] = (pid or "?", label, verdict)
    return list(runs.values())


def recorded_failures(m):
    """manifest evidence entries with outcome FAIL that are not preregistered run directories (e.g. SC-01's
    historical receipts): [(path, purpose, binding)]"""
    return [(e["path"], e.get("purpose", ""), e.get("binding")) for e in m["evidence"]
            if e.get("outcome") == "FAIL" and not re.search(r"/evidence/run-[^/]+/", e["path"])]


def evidence_cell(m):
    parts = ["%s %s %s" % r for r in runtime_evidence(m)]
    for path, purpose, binding in recorded_failures(m):
        pur = purpose if len(purpose) <= 70 else purpose[:67].rstrip() + "..."
        parts.append("recorded FAIL: %s%s (%s)" % (path, ", %s" % binding.lower() if binding else "", pur))
    return "; ".join(parts) or "— (Lean only)"


def open_premise(sid, rows):
    mine = [r for r in rows if sid in r["scenarios"]]
    if not mine:
        return None
    mine.sort(key=lambda r: (sid in r["tested_in"], -r["leverage"], r["id"]))
    return mine[0]


# ---------------------------------------------------------------- trust roots

def root_names(text):
    m = re.search(r"def Root\.name : Root → String\n((?:\s+\|.*\n)+)", text)
    return dict(re.findall(r'\|\s*\.(\w+)\s*=>\s*"([^"]+)"', m.group(1))) if m else {}


def roots_from_text(text):
    """scenario number -> [Root ctor] from the generated `scenario_roots_table` statement"""
    i = text.find("theorem scenario_roots_table")
    j = text.find(":=", i) if i >= 0 else -1
    if i < 0 or j < 0:
        return {}
    return {int(sc): re.findall(r"\.(\w+)", rs)
            for sc, rs in re.findall(r"\((\d+),\s*\[([^\]]*)\]\)", text[i:j])}


def trust_roots(lean=False):
    if not TRUST_ROOT.is_file():
        return {}, {}, "unavailable (ControlStack/Core/TrustRoot.lean missing)"
    text = TRUST_ROOT.read_text(encoding="utf-8")
    roots, names = roots_from_text(text), root_names(text)
    source = ("`scenario_roots_table` in ControlStack/Core/TrustRoot.lean (generated by tools/gen_trust_root.py; "
              "re-checked by `decide` whenever TrustRoot builds)")
    if lean:
        import gen_trust_root as GT
        probed, _ = GT.run_lean_probe(text, ROOT)
        if probed != roots:
            raise SystemExit("--lean-roots: Lean evaluation differs from the scenario_roots_table text")
    return roots, names, source


def fmt_roots(ctors, names):
    out = []
    for c in ctors:
        n = names.get(c, c)
        out.append(n.replace(" (residual)", "*"))
    return ", ".join(out) or "—"


# ---------------------------------------------------------------- scope

def scope_limits(ms):
    """deduplicated 'Not:' and 'Semantic' exclusions from manifest scope texts -> [(text, [sids])]"""
    items = {}
    for sid, m in ms.items():
        for mt in re.finditer(r"\b(Not|Semantic(?:, unformalised)?):\s*(.*?)(?:\.\s|\.$|$)", m.get("scope", "")):
            for part in re.split(r",\s*|;\s*", mt.group(2)):
                part = part.strip().strip(".").strip()
                if len(part) < 4:
                    continue
                key = re.sub(r"\s+", " ", part.lower())
                items.setdefault(key, [part, []])[1].append(sid)
    return sorted(((t, sorted(set(s))) for t, s in items.values()), key=lambda x: (-len(x[1]), x[0].lower()))


# ---------------------------------------------------------------- render

def render(lean_roots=False):
    ms = manifests()
    rows = PL.build(ROOT)
    roots, rnames, rsource = trust_roots(lean_roots)
    status = {}
    for m in ms.values():
        status[m["status"]] = status.get(m["status"], 0) + 1
    with_runs = [sid for sid, m in ms.items() if runtime_evidence(m)]
    thms = {(t["name"], t["path"]) for m in ms.values() for t in m["theorems"]}
    refine = sorted({sid for sid, m in ms.items() if any(is_refinement(t) for t in m["theorems"])})
    live = sorted({short_name(n) for n, p in thms if LIVENESS_RE.search(short_name(n))})
    live_sc = sorted({sid for sid, m in ms.items() if any(LIVENESS_RE.search(short_name(t["name"]))
                                                          for t in m["theorems"])})
    fails = sorted({sid for sid, m in ms.items() for e in m["evidence"] if e.get("outcome") == "FAIL"})
    unresolved_review = sorted(sid for sid, m in ms.items()
                               if (m.get("scope_axes") or {}).get("independent_review", {}).get("status") != "ESTABLISHED")
    L = ["# Control stack: overview",
         "",
         "<!-- generated by tools/build_overview.py from manifests, Lean sources, recorded evidence, the portfolio "
         "ledger, TrustRoot.lean and tools/measured.py; do not edit by hand; check with --check -->",
         "",
         "## Status",
         "",
         ("%d scenarios: %s. %d have preregistered runtime evidence (%s)%s. %d distinct theorems are cited by "
          "manifests; %d scenarios have a refinement result (%s) and %d have liveness/progress theorems (%s: %s). "
          "**No scenario is deployment-assured; independent human review is open** (%d of %d scenarios lack an "
          "established independent review).") % (
             len(ms), ", ".join("%s %d" % (k, status.get(k, 0)) for k in ("CONDITIONAL", "DRAFT", "FAILED")) +
             "".join(", %s %d" % (k, v) for k, v in sorted(status.items()) if k not in ("CONDITIONAL", "DRAFT", "FAILED")),
             len(with_runs), ", ".join(with_runs) or "none",
             ("; recorded FAIL outcomes in %s" % ", ".join(fails)) if fails else "",
             len(thms), len(refine), ", ".join(refine) or "none", len(live_sc), ", ".join(live_sc) or "none",
             ", ".join("`%s`" % n for n in live) or "none", len(unresolved_review), len(ms)),
         "",
         "## Scenarios",
         "",
         "Strongest result: the first manifest theorem that is `*_safe_authenticated`, else a refinement (`concrete_*` "
         "or a `Refinement` file), else `*_safe`, else the first listed. Top open premise: the scenario's normalised "
         "premise without runtime evidence in this scenario and with the highest portfolio leverage. Trust roots "
         "(`*` = residual root) from %s." % rsource,
         "",
         "| id | title | strongest formal result | runtime evidence | top open premise | trust roots |",
         "|---|---|---|---|---|---|"]
    for sid, m in ms.items():
        t = strongest(m)
        thm = "`%s`: %s" % (short_name(t["name"]), doc_of(t)) if t else "—"
        ev = evidence_cell(m)
        op = open_premise(sid, rows)
        opt = "`%s` (%s, leverage %d)" % (op["id"], op["kind"], op["leverage"]) if op else "—"
        rr = fmt_roots(roots.get(int(sid.split("-")[1]), []), rnames)
        L.append("| %s | %s | %s | %s | %s | %s |" % (sid, esc(m["title"]), esc(thm), esc(ev), esc(opt), esc(rr)))
    L += ["", "## Top premises by leverage", "",
          "From tools/portfolio_ledger.py (leverage = scenarios depending on the premise × 2 if none has runtime "
          "evidence). Full ledger: ASSURANCE-LEDGER.md.", "",
          "| premise | kind | scenarios | best evidence | tested in | leverage |", "|---|---|---|---|---|---|"]
    for r in rows[:TOP_PREMISES]:
        L.append("| `%s` | %s | %d | %s | %s | %d |" % (r["id"], r["kind"], len(r["scenarios"]), r["best_evidence"],
                                                       ", ".join(r["tested_in"]) or "—", r["leverage"]))
    mrows, notes = MS.collect(0.05, MS.read_ledger())
    L += ["", "## Measured bounds (δ = 0.05)", "",
          "From tools/measured.py: k/n of the good event and the exact one-sided Clopper–Pearson lower bound r_low "
          "(`Measured.cp_threshold`). `member` = the scenario is a ledger member of that premise. Every bound "
          "carries its caveat; see docs/MEASUREMENT.md for the per-history pitfall.", "",
          "| premise | scenario | member | measured (good event) | k/n | r_low | caveat |", "|---|---|---|---|---|---|---|"]
    for r in mrows:
        L.append("| `%s` | %s | %s | %s | %d/%d | %.4f | %s |" % (
            r["premise"], r["scenario"], "yes" if r["ledger_member"] else "no", esc(r["label"]), r["k"], r["n"],
            r["r_low"], esc(r["caveat"])))
    L += [""] + ["- %s" % n for n in notes]
    L += ["", "## How to verify", ""]
    L += ["- `%s` — %s" % (c, d) for c, d in VERIFY]
    L += ["", "## Honest limits", ""] + ["- %s" % c for c in FIXED_CAVEATS]
    L += ["", "Exclusions stated in the manifests' scope texts (deduplicated; scenarios in brackets):", ""]
    for text, sids in scope_limits(ms):
        L.append("- %s (%s)" % (text, ", ".join(sids)))
    return "\n".join(L).rstrip() + "\n"


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    g = ap.add_mutually_exclusive_group()
    g.add_argument("--check", action="store_true")
    g.add_argument("--stdout", action="store_true")
    ap.add_argument("--lean-roots", action="store_true")
    a = ap.parse_args(argv)
    page = render(a.lean_roots)
    if a.stdout:
        sys.stdout.write(page)
        return 0
    if a.check:
        cur = OUT.read_text(encoding="utf-8") if OUT.exists() else None
        if cur != page:
            print("OVERVIEW.md is out of date; run: python3 tools/build_overview.py", file=sys.stderr)
            return 1
        print("OVERVIEW.md up to date")
        return 0
    OUT.write_text(page, encoding="utf-8")
    print("wrote %s (%d lines)" % (OUT.name, page.count("\n")))
    return 0


if __name__ == "__main__":
    sys.exit(main())
