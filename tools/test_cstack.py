#!/usr/bin/env python3
"""Tests for tools/cstack.py. Fast: subprocesses are mocked or tiny (git on a temporary repo); no Lean except the
optional full-suite smoke test, which runs only with CSTACK_FULL=1."""
import io
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parent))
import cstack  # noqa: E402

ROOT = cstack.ROOT


def run_main(argv, **kw):
    out, err = io.StringIO(), io.StringIO()
    with redirect_stdout(out), redirect_stderr(err):
        rc = cstack.main(argv, **kw)
    return rc, out.getvalue(), err.getvalue()


class Recorder:
    """stands in for subprocess.call / subprocess.run and records argv"""

    def __init__(self, rc=0, fail=None, text=""):
        self.calls, self.rc, self.fail, self.text = [], rc, fail or (), text

    def __call__(self, argv, **kw):
        self.calls.append(list(argv))
        rc = 1 if any(f in " ".join(argv) for f in self.fail) else self.rc
        if "capture_output" in kw:
            return SimpleNamespace(returncode=rc, stdout=self.text, stderr="boom" if rc else "")
        return rc


class FailClosed(unittest.TestCase):
    def test_unknown_scenario_status(self):
        rc, _, err = run_main(["status", "SC-99"])
        self.assertEqual(rc, 2)
        self.assertIn("unknown scenario SC-99", err)

    def test_unknown_scenario_evidence(self):
        rc, _, err = run_main(["evidence", "SC-99"])
        self.assertEqual(rc, 2)
        self.assertIn("unknown scenario", err)

    def test_malformed_id(self):
        for bad in ("sc-26", "SC-2", "SC-026", "../SC-26", "SC-26/x"):
            rc, _, err = run_main(["status", bad])
            self.assertEqual(rc, 2, bad)
            self.assertIn("not a scenario id", err)

    def test_new_refuses_existing_and_malformed(self):
        rec = Recorder()
        self.assertEqual(run_main(["new", "SC-26", "spec.json"], runner=rec)[0], 2)
        self.assertEqual(run_main(["new", "SC-9", "spec.json"], runner=rec)[0], 2)
        self.assertEqual(rec.calls, [])

    def test_unknown_extra_args_rejected(self):
        with self.assertRaises(SystemExit):
            run_main(["status", "SC-26", "--bogus"])


class Status(unittest.TestCase):
    def test_portfolio_lists_every_scenario(self):
        rc, out, _ = run_main(["status"])
        self.assertEqual(rc, 0)
        for sid in cstack.manifests():
            self.assertIn(f"| {sid} |", out)

    def test_scenario_detail(self):
        rc, out, _ = run_main(["status", "SC-26"])
        self.assertEqual(rc, 0)
        m = cstack.manifests()["SC-26"]
        for t in m["theorems"]:
            self.assertIn(t["name"], out)
        self.assertIn("scenarios/SC-26/evidence/run-1: PASS", out)
        self.assertIn("open premises", out)
        self.assertIn("done criteria", out)
        for a in m["assumptions"]:
            if a.get("applicability") != "ESTABLISHED":
                self.assertIn(a["id"], out)


class Check(unittest.TestCase):
    def test_all_pass(self):
        rec, out = Recorder(), io.StringIO()
        self.assertEqual(cstack.run_check(runner=rec, out=out), 0)
        names = [s[0] for s in cstack.check_steps()]
        self.assertEqual(len(rec.calls), len(names))
        self.assertIn(f"{len(names)}/{len(names)} passed (fast suite)", out.getvalue())
        self.assertNotIn("FAIL", out.getvalue())

    def test_one_failure_is_nonzero_and_shown(self):
        rec, out = Recorder(fail=["build_registry.py"]), io.StringIO()
        self.assertEqual(cstack.run_check(runner=rec, out=out), 1)
        line = next(l for l in out.getvalue().splitlines() if l.startswith("registry --check"))
        self.assertIn("FAIL", line)
        self.assertIn("--- registry --check (last lines) ---", out.getvalue())

    def test_runner_exception_is_failure(self):
        def boom(argv, **kw):
            raise subprocess.TimeoutExpired(argv, 1)
        self.assertEqual(cstack.run_check(only="stackmap", runner=boom, out=io.StringIO()), 1)

    def test_fast_has_no_lean_and_covers_suite(self):
        steps = cstack.check_steps()
        argvs = [" ".join(a) for _, a, _ in steps]
        self.assertFalse(any("lake" in a for a in argvs))
        for want in ("build_registry.py --check", "build_status.py --check", "build_statement_catalog.py --check",
                     "build_results.py --check", "portfolio_ledger.py --check --no-lean", "stackmap.py --validate",
                     "check_scenarios.py", "unittest tools.test_check_scenarios", "check_sc26_case.py --skip-lean",
                     "test_stackmap.py", "test_cstack.py", "gen_trust_root.py --check --no-lean"):
            self.assertTrue(any(want in a for a in argvs), want)
        self.assertFalse(any("test_trusted_stack_broker" in a for a in argvs))

    def test_full_adds_lean(self):
        names = [s[0] for s in cstack.check_steps(full=True)]
        self.assertIn("lake build ControlStack", names)
        self.assertIn("claim SC-26", names)
        self.assertIn("check_sc26_case", names)
        self.assertTrue(any(n.startswith("assurance ledger --check") and "no Lean" not in n for n in names))
        self.assertTrue(any(n.startswith("trust-root table --check") and "no Lean" not in n for n in names))

    def test_claim_axiom_scan(self):
        good = "'X.t' depends on axioms: [propext, Quot.sound]\n"
        self.assertTrue(cstack.axioms_ok(good))
        self.assertTrue(cstack.axioms_ok("'X.t' does not depend on any axioms\n"))
        self.assertFalse(cstack.axioms_ok("'X.t' depends on axioms: [propext, X.myAxiom]\n"))
        self.assertFalse(cstack.axioms_ok(good + "error: oops"))
        self.assertFalse(cstack.axioms_ok("'X.t' depends on axioms: [sorryAx]\n"))
        self.assertFalse(cstack.axioms_ok(""))
        rec = Recorder(text="'X.t' depends on axioms: [Classical.choice, bad]\n")
        with mock.patch.object(cstack, "check_steps", return_value=[("claim SC-01", ["lake"], {0})]):
            self.assertEqual(cstack.run_check(full=True, runner=rec, out=io.StringIO()), 1)

    def test_list_and_only(self):
        rc, out, _ = run_main(["check", "--list"])
        self.assertEqual(rc, 0)
        self.assertIn("registry --check", out)
        self.assertEqual(run_main(["check", "--only", "no-such-step"])[0], 2)


class Dispatch(unittest.TestCase):
    def test_map(self):
        rec = Recorder()
        run_main(["map", "--gaps"], runner=rec)
        run_main(["map", "--researcher", "secrets_kms", "--json"], runner=rec)
        run_main(["map"], runner=rec)
        self.assertEqual([c[1:] for c in rec.calls], [["tools/stackmap.py", "--gaps"],
                                                      ["tools/stackmap.py", "--researcher", "secrets_kms", "--json"],
                                                      ["tools/stackmap.py"]])

    def test_map_passes_return_code(self):
        self.assertEqual(run_main(["map", "--researcher", "nope"], runner=Recorder(rc=2))[0], 2)

    def test_ledgers(self):
        rec = Recorder()
        run_main(["ledger", "--stack"], runner=rec)
        run_main(["ledger", "--lab", "--json"], runner=rec)
        run_main(["ledger", "--portfolio", "--json", "--no-lean"], runner=rec)
        self.assertEqual(rec.calls[0][1:], ["tools/cert_ledger.py"])
        self.assertEqual(rec.calls[1][1:], ["tools/cert_ledger.py", "--import", "ControlStack.Scenarios.LabStack",
                                            "--ledger", "ControlStack.LabStack.labLedger", "--json"])
        self.assertEqual(rec.calls[2][1:], ["tools/portfolio_ledger.py", "--json", "--no-lean"])

    def test_portfolio_never_regenerates_file(self):
        rec = Recorder()
        self.assertEqual(run_main(["ledger", "--no-lean"], runner=rec)[0], 2)
        self.assertEqual(rec.calls, [])

    def test_portfolio_table_in_process(self):
        rc, out, _ = run_main(["ledger"], runner=Recorder())
        self.assertEqual(rc, 0)
        self.assertIn("| credential_separation |", out)

    def test_new(self):
        rec = Recorder()
        rc, _, _ = run_main(["new", "SC-90", "spec.json", "--dry-run"], runner=rec)
        self.assertEqual(rc, 0)
        self.assertEqual(rec.calls[0][1:], ["tools/new_scenario.py", "SC-90", "spec.json", "--dry-run"])


def git(repo, *args):
    subprocess.run(["git", *args], cwd=repo, check=True, capture_output=True)


class EvidencePins(unittest.TestCase):
    """pin verification on a throwaway git repository with one scenario and one meta.json-style run"""

    def setUp(self):
        self.root = Path(tempfile.mkdtemp())
        r = self.root
        (r / "scenarios/SC-50/harness").mkdir(parents=True)
        (r / "prereg").mkdir()
        (r / "scenarios/SC-50/harness/run_x.py").write_text("print('x')\n")
        (r / "prereg/SC50-X.md").write_text("# p\n\n**ID:** `PREREG-SC50-X-v1`. **Freeze:** rule\n")
        m = {"id": "SC-50", "title": "t", "status": "CONDITIONAL", "bad_event": "b", "theorems": [],
             "evidence": [], "assumptions": []}
        (r / "scenarios/SC-50/manifest.json").write_text(json.dumps(m))
        git(r, "init", "-q")
        git(r, "-c", "user.email=t@t", "-c", "user.name=t", "add", ".")
        git(r, "-c", "user.email=t@t", "-c", "user.name=t", "commit", "-qm", "pin")
        self.commit = subprocess.run(["git", "rev-parse", "HEAD"], cwd=r, capture_output=True,
                                     text=True).stdout.strip()
        self.run_dir = r / "scenarios/SC-50/evidence/run-1"
        self.run_dir.mkdir(parents=True)
        self.write_meta({p: cstack.sha(r / p) for p in ("scenarios/SC-50/harness/run_x.py", "prereg/SC50-X.md")})
        (self.run_dir / "verdicts.json").write_text(json.dumps({"overall": "PASS"}))

    def tearDown(self):
        shutil.rmtree(self.root)

    def write_meta(self, pins, commit=None):
        pins = dict(pins, **{"<workdir>/out.jsonl": "0" * 64})
        (self.run_dir / "meta.json").write_text(json.dumps({
            "git_commit": commit or self.commit, "git_status_harness_and_prereg": "",
            "prereg_id": "PREREG-SC50-X-v1", "sha256": pins}))

    def evidence(self):
        out = io.StringIO()
        return cstack.evidence("SC-50", root=self.root, out=out), out.getvalue()

    def test_pins_ok(self):
        rc, out = self.evidence()
        self.assertEqual(rc, 0, out)
        self.assertIn("verdict=PASS  pins=OK", out)
        self.assertIn("recorded by run-1 (unchanged since)", out)
        self.assertNotIn("<workdir>", out)

    def test_evolved_file_is_informational(self):
        (self.root / "scenarios/SC-50/harness/run_x.py").write_text("print('later')\n")
        rc, out = self.evidence()
        self.assertEqual(rc, 0)
        self.assertIn("(working tree: evolved)", out)

    def test_tampered_hash_fails(self):
        self.write_meta({"scenarios/SC-50/harness/run_x.py": "f" * 64})
        rc, out = self.evidence()
        self.assertEqual(rc, 1)
        self.assertIn("MISMATCH", out)

    def test_missing_path_fails(self):
        self.write_meta({"scenarios/SC-50/harness/gone.py": "f" * 64})
        rc, out = self.evidence()
        self.assertEqual(rc, 1)
        self.assertIn("MISSING_AT_COMMIT", out)

    def test_unknown_commit_fails(self):
        self.write_meta({"prereg/SC50-X.md": cstack.sha(self.root / "prereg/SC50-X.md")}, commit="a" * 40)
        rc, out = self.evidence()
        self.assertEqual(rc, 1)
        self.assertIn("UNVERIFIABLE", out)

    def test_no_metadata_fails(self):
        (self.run_dir / "meta.json").unlink()
        rc, out = self.evidence()
        self.assertEqual(rc, 1)
        self.assertIn("UNVERIFIABLE", out)


class EvidenceReal(unittest.TestCase):
    def test_sc28_pins_verify(self):
        out = io.StringIO()
        rc = cstack.evidence("SC-28", out=out)
        self.assertEqual(rc, 0, out.getvalue())
        self.assertIn("PREREG-SC28-CGMETER-v1", out.getvalue())
        self.assertIn("recheck:", out.getvalue())

    def test_sc26_receipts_and_pin_tables(self):
        out = io.StringIO()
        rc = cstack.evidence("SC-26", out=out)
        text = out.getvalue()
        self.assertEqual(rc, 0, text)
        self.assertIn("[prereg/SC26-TRANSACTION-GATE-v2.md pin table] commit ef419bf2", text)
        self.assertIn("python3 tools/check_sc26_case.py --run run-2", text)
        self.assertNotIn("MISMATCH", text)

    def test_prereg_status(self):
        info = cstack.prereg_info()
        self.assertEqual(info[ROOT / "prereg/SC14-MULTI-RESOURCE.md"][1], "FROZEN (declared)")
        self.assertEqual(info[ROOT / "prereg/SC01-LIFETIME-INDEPENDENCE-DRAFT.md"][1], "DRAFT")


@unittest.skipUnless(os.environ.get("CSTACK_FULL") == "1", "set CSTACK_FULL=1 to run the full (Lean) smoke test")
class FullSmoke(unittest.TestCase):
    def test_full_claim_compile(self):
        out = io.StringIO()
        self.assertEqual(cstack.run_check(full=True, only="claim SC-26", out=out), 0, out.getvalue())


if __name__ == "__main__":
    unittest.main()
