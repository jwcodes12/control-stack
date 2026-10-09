#!/usr/bin/env python3
"""Tests for tools/build_results.py: parsing, rendering, honesty invariants, markers, drift check."""
import json
import re
import sys
import tempfile
import unittest
from pathlib import Path

sys.dont_write_bytecode = True
REPO = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO))
from tools import build_results as BR  # noqa: E402

LEAN = '''/-- **Main safety.** After any trace, every effect is approved. More detail here. -/
theorem sc99_safe : True := trivial

/-- 1. Windows needed. At least two windows are required for anything. -/
theorem windows_needed : True := trivial

/-- without the check, a bad effect happens -/
theorem no_check_breaks : True := trivial

theorem undocumented : True := trivial
'''

PREREG = '''# Prereg
**ID:** `PREREG-SC99-TEST-v1`. **Written:** today.
**H1 Attacks.** something
### H2 Usefulness of the thing (`sc99_safe`)
'''


def manifest(evidence=True, axes_status="ASSUMED", usefulness="NOT_RUN"):
    return {
        "id": "SC-99", "title": "Test scenario", "status": "CONDITIONAL", "bad_event": "A bad thing happens.",
        "adversary": "Any trace.", "scope": "Single host. Not: everything else.", "refutation": "A trace.",
        "families": ["F1"],
        "theorems": [{"name": "ControlStack.SC99.sc99_safe", "path": "ControlStack/SC99.lean"},
                     {"name": "ControlStack.SC99.windows_needed", "path": "ControlStack/SC99.lean"}],
        "evidence": ([{"path": "scenarios/SC-99/evidence/run-1/verdicts.json", "outcome": "PASS", "purpose": "run-1"},
                      {"path": "prereg/SC99.md", "outcome": "PASS", "purpose": "Frozen preregistration"}]
                     if evidence else []),
        "assumptions": [{"id": "honest_usefulness", "text": "Honest task completes.", "proof": "NOT_PROVED",
                         "evidence": "TESTED_NOT_PROVED" if evidence else "NOT_RUN", "applicability": "UNRESOLVED",
                         "usefulness": usefulness}],
        "scope_axes": {k: {"status": axes_status, "note": "n"} for k in
                       ("threat_coverage", "runtime_correspondence", "environment_boundary",
                        "lifetime_and_composition", "usefulness", "independent_review")},
    }


class Fixture(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        root = Path(self.tmp.name)
        (root / "ControlStack").mkdir()
        (root / "ControlStack/SC99.lean").write_text(LEAN)
        (root / "prereg").mkdir()
        (root / "prereg/SC99.md").write_text(PREREG)
        (root / "tools").mkdir()
        d = root / "scenarios/SC-99"
        (d / "evidence/run-1").mkdir(parents=True)
        (d / "tests").mkdir()
        (d / "evidence/run-1/verdicts.json").write_text(json.dumps({
            "prereg_id": "PREREG-SC99-TEST-v1", "overall": "PASS",
            "per_hypothesis": {"H1": {"verdict": "PASS", "passed": 5, "reps": 5},
                               "H2": {"verdict": "PASS", "passed": 5, "reps": 5, "negative_control": True}}}))
        (d / "claim.lean").write_text("-- claim")
        (d / "threat.md").write_text("# SC-99: catalog draft\n\nold\n")
        (d / "manifest.json").write_text(json.dumps(manifest()))
        self.root, self.d = root, d
        self.saved = (BR.ROOT, BR.SCEN)
        BR.ROOT, BR.SCEN = root, root / "scenarios"
        BR.lean_decls.__defaults__[0].clear()
        BR.prereg_index.__defaults__[0].clear()

    def tearDown(self):
        BR.ROOT, BR.SCEN = self.saved
        BR.lean_decls.__defaults__[0].clear()
        BR.prereg_index.__defaults__[0].clear()


class Parsing(Fixture):
    def test_docstrings(self):
        d = BR.lean_decls("ControlStack/SC99.lean")
        self.assertEqual(d["sc99_safe"], "Main safety. After any trace, every effect is approved.")
        self.assertEqual(d["windows_needed"], "Windows needed. At least two windows are required for anything.")
        self.assertIsNone(d["undocumented"])
        self.assertEqual(BR.find_decl("ControlStack.SC99.sc99_safe", "ControlStack/SC99.lean")[0], "sc99_safe")

    def test_evidence_summary_and_prereg_titles(self):
        pid, overall, rows = BR.summarise_json("scenarios/SC-99/evidence/run-1/verdicts.json")
        self.assertEqual((pid, overall), ("PREREG-SC99-TEST-v1", "PASS"))
        self.assertIn("negative control", rows[1][2])
        titles = BR.hyp_titles(self.root / "prereg/SC99.md")
        self.assertEqual(titles["H1"], "Attacks")
        self.assertEqual(titles["H2"], "Usefulness of the thing")

    def test_other_evidence_shapes(self):
        p = self.d / "evidence/run-1/receipt.json"
        p.write_text(json.dumps({"verdict": "PASS", "phases": {"attacks": {"verdict": "PASS", "check_trace": "PASS"},
                                                               "usefulness": {"verdict": "PASS", "success": 64, "n": 64}}}))
        _, overall, rows = BR.summarise_json("scenarios/SC-99/evidence/run-1/receipt.json")
        self.assertEqual(overall, "PASS")
        self.assertIn("64/64 succeeded", rows[1][2])
        p.write_text(json.dumps({"prereg": "X", "overall": "PASS", "R1": {"rule": "0/16", "observed": "0/16",
                                                                          "verdict": "PASS"}}))
        self.assertEqual(BR.summarise_json("scenarios/SC-99/evidence/run-1/receipt.json")[2][0][0], "R1")


class Honesty(Fixture):
    def test_never_met_and_criterion5_open(self):
        for m in (manifest(), manifest(evidence=False), manifest(axes_status="REFUTED", usefulness="OBSERVED_FAILURE")):
            summaries = {e["path"]: BR.summarise_json(e["path"]) for e in m["evidence"] if e["path"].endswith(".json")}
            crit = BR.done_criteria(m, summaries)
            self.assertEqual(len(crit), 6)
            self.assertTrue(all(s in ("OPEN", "ASSUMED", "PARTIAL", "RECORDED", "REFUTED") for _, s, _ in crit))
            self.assertEqual(crit[4][1], "OPEN")

    def test_model_only_has_no_recorded_runtime(self):
        crit = BR.done_criteria(manifest(evidence=False), {})
        self.assertEqual([c[1] for c in crit][0:2] + [crit[5][1]], ["OPEN", "OPEN", "OPEN"])

    def test_page_content(self):
        page = BR.render_result(manifest(), BR.path_refs([manifest()]))
        self.assertIn(BR.GEN_MARKER, page)
        self.assertIn("not deployment assurance", page)
        self.assertIn("`PREREG-SC99-TEST-v1`", page)
        self.assertIn("| H2 | Usefulness of the thing | PASS |", page)
        self.assertIn("no_check_breaks", page)  # witness found in the scenario's own file
        self.assertNotIn("| MET |", page)


class Driver(Fixture):
    def test_generate_check_markers_notes(self):
        self.assertEqual(BR.main(["--check"]), 1)  # drift before generation
        self.assertEqual(BR.main([]), 0)
        self.assertEqual(BR.main(["--check"]), 0)
        threat = (self.d / "threat.md").read_text()
        self.assertIn("_Generated from manifest.json._", threat)
        # notes preserved verbatim across regeneration
        rp = self.d / "result.md"
        text = rp.read_text().replace(BR.GEN_MARKER, BR.GEN_MARKER + "\n<!-- notes:begin -->\nKEEP ME\n<!-- notes:end -->", 1)
        rp.write_text(text)
        self.assertEqual(BR.main([]), 0)
        self.assertIn("KEEP ME", rp.read_text())
        self.assertEqual(BR.main(["--check"]), 0)
        # hand-written files are never touched
        rp.write_text("# mine\n<!-- hand-written -->\n")
        BR.main([])
        self.assertEqual(rp.read_text(), "# mine\n<!-- hand-written -->\n")

    def test_handwritten_threat_untouched(self):
        (self.d / "threat.md").write_text("# SC-99: a careful hand-written threat model\n")
        BR.main([])
        self.assertEqual((self.d / "threat.md").read_text(), "# SC-99: a careful hand-written threat model\n")


class RealRepo(unittest.TestCase):
    def test_repo_consistent_and_honest(self):
        self.assertEqual(BR.main(["--check"]), 0)
        for p in sorted((REPO / "scenarios").glob("SC-*/result.md")):
            t = p.read_text()
            if BR.HAND_MARKER in t:
                continue
            self.assertIn("not deployment assurance", t, p)
            self.assertNotIn("| MET |", t, p)
            self.assertRegex(t, r"\| 5 \| [^|]+\| OPEN \|", p)
            self.assertNotIn("DRAFT, UNTESTED, UNPROVED", t, p)


if __name__ == "__main__":
    unittest.main()
