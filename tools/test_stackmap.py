#!/usr/bin/env python3
"""Tests for tools/stackmap.py: fail-closed validation on synthetic repos, and output on the real data.
Static only: no Lean, VMs, network or subprocess."""
import contextlib
import copy
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from tools import stackmap
from tools.stackmap import Invalid, load, main

REAL = Path(__file__).resolve().parent.parent


def run_cli(*args):
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        try:
            rc = main(list(args))
        except SystemExit as e:  # argparse usage errors
            rc = e.code
    return rc, out.getvalue(), err.getvalue()


def manifest(sid, status="DRAFT", axes=None):
    a = axes or {"proof": "NOT_PROVED", "evidence": "NOT_RUN", "applicability": "UNRESOLVED",
                 "usefulness": "NOT_RUN"}
    return {"id": sid, "title": f"title {sid}", "status": status, "families": ["F1"],
            "assumptions": [dict(id="correspondence", text="t", **a)]}


def component(**over):
    c = {
        "id": "box", "name": "Box", "layer": "host", "examples": ["e"], "families": ["F1", "F3"],
        "scenarios": ["SC-01"], "trusted_component": "gate", "trusted_role": ["gate"],
        "model": [{"path": "M.lean", "decls": ["foo_safe"], "note": "n"}],
        "premises": [
            {"id": "mediation", "text": "all effects pass", "evidence": [
                {"path": "test_x.py", "kind": "test", "outcome": "PASS", "note": "n"}],
             "necessity": [{"path": "M.lean", "decls": ["Ns.bar_breaks"]}]},
            {"id": "open_one", "text": "nobody did this", "evidence": [], "necessity": []}],
        "related": ["doc.md"],
        "practical": {"commodity": "do it", "gpu": None, "datacenter": None},
        "decisive_tier": "commodity", "literature": ["generic"], "status": "REFERENCE_TESTED",
        "status_note": "n",
        "researcher": {"use_for": "x", "provide": ["y"], "run": ["python3 test_x.py", "python3 tools/x.py 1/20"]},
    }
    c.update(over)
    return c


class Synthetic(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        for sid in ("SC-01", "SC-02"):
            d = self.root / "scenarios" / sid
            d.mkdir(parents=True)
            (d / "manifest.json").write_text(json.dumps(manifest(sid)))
        (self.root / "M.lean").write_text("theorem foo_safe : True := trivial\ntheorem Ns.bar_breaks : True := trivial\n")
        (self.root / "test_x.py").write_text("")
        (self.root / "doc.md").write_text("")
        (self.root / "tools").mkdir()
        (self.root / "tools" / "x.py").write_text("")
        (self.root / "stack").mkdir()
        self.data = {"schema_version": 1, "note": "n", "components": [component()]}

    def write(self, data=None, raw=None):
        p = self.root / "stack" / "components.json"
        p.write_text(raw if raw is not None else json.dumps(data or self.data))
        return p

    def invalid(self, pattern):
        self.write()
        with self.assertRaisesRegex(Invalid, pattern):
            load(self.root)
        rc, _, err = run_cli("--root", str(self.root), "--validate")
        self.assertEqual(rc, 1)
        self.assertIn("INVALID", err)

    def test_minimal_valid(self):
        self.write()
        comps, manifests = load(self.root)
        self.assertEqual([c["id"] for c in comps], ["box"])
        self.assertEqual(set(manifests), {"SC-01"})
        rc, out, _ = run_cli("--root", str(self.root), "--validate")
        self.assertEqual((rc, out.strip()), (0, "OK: 1 components, 1 scenarios joined"))

    def test_unknown_scenario(self):
        self.data["components"][0]["scenarios"] = ["SC-99"]
        self.invalid("SC-99 has no scenarios/SC-99/manifest.json")

    def test_malformed_scenario_id(self):
        self.data["components"][0]["scenarios"] = ["SC-1"]
        self.invalid("invalid scenario id")

    def test_manifest_id_mismatch(self):
        (self.root / "scenarios" / "SC-01" / "manifest.json").write_text(json.dumps(manifest("SC-02")))
        self.invalid("does not match folder")

    def test_manifest_missing_axis(self):
        m = manifest("SC-01")
        del m["assumptions"][0]["usefulness"]
        (self.root / "scenarios" / "SC-01" / "manifest.json").write_text(json.dumps(m))
        self.invalid("lacks axis usefulness")

    def test_missing_cited_paths(self):
        for mutate in (lambda c: c["premises"][0]["evidence"][0].update(path="nope.py"),
                       lambda c: c["model"][0].update(path="Nope.lean"),
                       lambda c: c["related"].append("missing.md"),
                       lambda c: c["premises"][0]["necessity"][0].update(path="X.lean")):
            with self.subTest(mutate=mutate):
                self.data["components"][0] = component()
                mutate(self.data["components"][0])
                self.invalid("does not exist in repo")

    def test_unsafe_paths(self):
        for bad in ("../outside.py", "/etc/passwd"):
            with self.subTest(bad=bad):
                self.data["components"][0] = component()
                self.data["components"][0]["premises"][0]["evidence"][0]["path"] = bad
                self.invalid("unsafe path")

    def test_run_command_cites_missing_file(self):
        self.data["components"][0]["researcher"]["run"] = ["python3 tools/missing.py --x 1/20"]
        self.invalid("researcher.run: cited path does not exist")

    def test_bad_status_value(self):
        self.data["components"][0]["status"] = "DEPLOYED"
        self.invalid("status 'DEPLOYED' not in")

    def test_status_must_match_evidence(self):
        self.data["components"][0]["status"] = "MODEL_ONLY"
        self.invalid("declared status MODEL_ONLY but cited evidence supports REFERENCE_TESTED")
        c = component(status="REFERENCE_TESTED")
        c["premises"][0]["evidence"][0].update(outcome="NOT_RUN")
        self.data["components"][0] = c
        self.invalid("supports MODEL_ONLY")
        c = component(status="MODEL_ONLY", model=[])
        c["premises"][0]["evidence"] = []
        self.data["components"][0] = c
        self.invalid("supports NOT_STARTED")

    def test_unknown_family_role_tier_layer(self):
        for key, val, pat in (("families", ["F9"], "unknown family"), ("trusted_role", ["god"], "unknown trusted role"),
                              ("decisive_tier", "moon", "unknown decisive_tier"), ("layer", "x", "unknown layer")):
            with self.subTest(key=key):
                self.data["components"][0] = component(**{key: val})
                self.invalid(pat)

    def test_bad_evidence_kind_and_outcome(self):
        self.data["components"][0]["premises"][0]["evidence"][0]["kind"] = "vibes"
        self.invalid("unknown kind")
        self.data["components"][0] = component()
        self.data["components"][0]["premises"][0]["evidence"][0]["outcome"] = "GREAT"
        self.invalid("unknown outcome")

    def test_missing_declaration(self):
        self.data["components"][0]["model"][0]["decls"] = ["not_there"]
        self.invalid("declaration 'not_there' not found")

    def test_decl_prefix_does_not_match(self):
        self.data["components"][0]["model"][0]["decls"] = ["foo"]
        self.invalid("declaration 'foo' not found")

    def test_necessity_needs_declaration(self):
        self.data["components"][0]["premises"][0]["necessity"][0]["decls"] = []
        self.invalid("must name a declaration")

    def test_duplicate_component_and_premise_ids(self):
        self.data["components"].append(component())
        self.invalid("duplicate component id")
        self.data["components"] = [component()]
        self.data["components"][0]["premises"][1]["id"] = "mediation"
        self.invalid("duplicate premise id")

    def test_unknown_and_missing_keys(self):
        self.data["components"][0]["extra"] = 1
        self.invalid("unknown keys")
        self.data["components"][0] = component()
        del self.data["components"][0]["literature"]
        self.invalid("missing keys")

    def test_duplicate_json_key(self):
        text = json.dumps(self.data)
        text = text.replace('"schema_version": 1', '"schema_version": 1, "schema_version": 1', 1)
        self.write(raw=text)
        with self.assertRaisesRegex(Invalid, "duplicate JSON key"):
            load(self.root)

    def test_empty_premises_and_components(self):
        self.data["components"][0]["premises"] = []
        self.invalid("premises: must be a non-empty list")
        self.data["components"] = []
        self.invalid("components: must be a non-empty list")

    def test_decisive_tier_needs_practical_text(self):
        self.data["components"][0]["decisive_tier"] = "gpu"
        self.invalid("has no practical test described")

    def test_premise_states_and_score(self):
        c = component(scenarios=["SC-01", "SC-02"])
        c["premises"].append({"id": "refuted", "text": "t", "necessity": [],
                              "evidence": [{"path": "test_x.py", "kind": "receipt", "outcome": "FAIL"}]})
        c["premises"].append({"id": "modelled", "text": "t", "necessity": [],
                              "evidence": [{"path": "M.lean", "kind": "lean", "outcome": "PASS"}]})
        self.data["components"] = [c]
        self.write()
        comps, _ = load(self.root)
        states = {p["id"]: stackmap.premise_state(p) for p in comps[0]["premises"]}
        self.assertEqual(states, {"mediation": "TESTED", "open_one": "GAP", "refuted": "REFUTED",
                                  "modelled": "MODELLED"})
        # (2 GAP + 2 REFUTED + 1 MODELLED) * 2 scenarios / commodity 1
        self.assertEqual(stackmap.score(comps[0]), 10.0)
        g = stackmap.gaps(comps)[0]
        self.assertEqual((g["gap_premises"], g["refuted_premises"]), (["open_one"], ["refuted"]))

    def test_gap_ordering(self):
        cheap = component(id="cheap")
        dear = component(id="dear", decisive_tier="datacenter",
                         practical={"commodity": "x", "gpu": None, "datacenter": "y"})
        self.data["components"] = [dear, cheap]
        self.write()
        rc, out, _ = run_cli("--root", str(self.root), "--gaps", "--json")
        self.assertEqual(rc, 0)
        self.assertEqual([g["id"] for g in json.loads(out)], ["cheap", "dear"])

    def test_blocking_join_marks_refuted(self):
        (self.root / "scenarios" / "SC-01" / "manifest.json").write_text(json.dumps(manifest(
            "SC-01", "CONDITIONAL", {"proof": "THEOREM_VERIFIED", "evidence": "OBSERVED_FAILURE",
                                     "applicability": "ESTABLISHED", "usefulness": "MET_RECORDED"})))
        self.write()
        comps, manifests = load(self.root)
        row = stackmap.scenario_rows(comps[0], manifests)[0]
        self.assertEqual(row["status"], "CONDITIONAL")
        self.assertEqual(row["blocking"], [{"id": "correspondence", "axes": {"evidence": "OBSERVED_FAILURE"},
                                            "refuted": True}])


class RealData(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.comps, cls.manifests = load(REAL)
        cls.by_id = {c["id"]: c for c in cls.comps}

    def test_real_data_validates(self):
        rc, out, err = run_cli("--validate")
        self.assertEqual(rc, 0, err)
        self.assertTrue(out.startswith("OK:"))

    def test_required_components_present(self):
        need = {"researcher_workstation", "agent_sandbox", "code_review_cicd", "secrets_kms", "cloud_control_plane",
                "job_scheduler", "gpu_multitenancy", "gpu_interconnect", "gpu_telemetry_meter",
                "gpu_physical_side_channels", "confidential_computing", "weight_storage", "network_egress",
                "logging_pipeline", "trusted_monitor_audit", "human_approval", "incident_halt"}
        self.assertEqual(need, set(self.by_id))

    def test_every_scenario_and_family_is_mapped(self):
        sids = {d.name for d in (REAL / "scenarios").iterdir() if d.name.startswith("SC-")}
        mapped = {s for c in self.comps for s in c["scenarios"]}
        self.assertEqual(sids, mapped)
        self.assertEqual({f for c in self.comps for f in c["families"]}, set(stackmap.FAMILIES))

    def test_no_component_claims_more_than_reference(self):
        self.assertTrue(all(c["status"] in stackmap.STATUSES for c in self.comps))
        for gid in ("gpu_multitenancy", "gpu_interconnect", "gpu_telemetry_meter", "gpu_physical_side_channels",
                    "confidential_computing"):
            self.assertEqual(self.by_id[gid]["status"], "MODEL_ONLY", gid)

    def test_matrix_output(self):
        rc, out, _ = run_cli("--matrix")
        self.assertEqual(rc, 0)
        for c in self.comps:
            self.assertIn(c["id"], out)
        rc, js, _ = run_cli("--matrix", "--json")
        m = json.loads(js)["matrix"]
        self.assertEqual(len(m), len(self.comps))
        row = next(r for r in m if r["id"] == "trusted_monitor_audit")
        self.assertTrue(row["families"]["F6"])

    def test_scenario_join_uses_manifest_status(self):
        rc, js, _ = run_cli("--scenarios", "--json")
        self.assertEqual(rc, 0)
        rows = json.loads(js)["scenarios"]
        sc01 = next(r for r in rows["gpu_multitenancy"] if r["id"] == "SC-01")
        self.assertEqual(sc01["status"], self.manifests["SC-01"]["status"])
        self.assertTrue(any(b["refuted"] for b in sc01["blocking"]))  # recorded side-kernel / VM failures

    def test_gaps_sorted_and_nonempty(self):
        rc, js, _ = run_cli("--gaps", "--json")
        self.assertEqual(rc, 0)
        g = json.loads(js)
        self.assertTrue(g)
        scores = [x["score"] for x in g]
        self.assertEqual(scores, sorted(scores, reverse=True))
        self.assertTrue(all(x["gap_premises"] or x["refuted_premises"] for x in g))

    def test_researcher_checklist(self):
        rc, out, _ = run_cli("--researcher", "agent_sandbox")
        self.assertEqual(rc, 0)
        for s in ("RESEARCHER CHECKLIST", "[GAP]", "[REFUTED]", "You must provide", "Run:", "Nothing here promotes"):
            self.assertIn(s, out)
        rc, js, _ = run_cli("--researcher", "incident_halt", "--json")
        r = json.loads(js)
        self.assertEqual(r["id"], "incident_halt")
        self.assertIn("halt", r["trusted_role"])

    def test_unknown_researcher_component(self):
        rc, _, err = run_cli("--researcher", "nonexistent")
        self.assertEqual(rc, 2)
        self.assertIn("unknown component", err)

    def test_real_file_mutation_fails_closed(self):
        data = json.loads((REAL / "stack" / "components.json").read_text())
        bad = copy.deepcopy(data)
        bad["components"][0]["scenarios"].append("SC-77")
        with tempfile.TemporaryDirectory() as t:
            p = Path(t) / "c.json"
            p.write_text(json.dumps(bad))
            rc, _, err = run_cli("--components", str(p), "--validate")
        self.assertEqual(rc, 1)
        self.assertIn("SC-77", err)


if __name__ == "__main__":
    unittest.main()
