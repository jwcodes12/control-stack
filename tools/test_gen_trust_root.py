#!/usr/bin/env python3
"""Tests for tools/gen_trust_root.py. No Lean: the Lean probe is replaced by a canned runner."""
import io
import re
import shutil
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from types import SimpleNamespace

sys.path.insert(0, str(Path(__file__).resolve().parent))
import gen_trust_root as g  # noqa: E402

ROOT = g.ROOT
TEXT = (ROOT / g.TR).read_text(encoding="utf-8")


def quiet(fn, *a, **kw):
    with redirect_stdout(io.StringIO()), redirect_stderr(io.StringIO()) as err:
        rc = fn(*a, **kw)
    return rc, err.getvalue()


class Blocks(unittest.TestCase):
    def test_markers_present_once(self):
        for name in ("scenarios", "root tables", "summary"):
            g.block_span(TEXT, name)

    def test_missing_marker_fails(self):
        with self.assertRaises(g.GenError):
            g.block_span(TEXT.replace("-- END GENERATED: scenarios\n", ""), "scenarios")

    def test_repo_scenarios_block_up_to_date(self):
        self.assertEqual(g.get_block(TEXT, "scenarios"), g.scenarios_block(TEXT))
        self.assertEqual(quiet(g.main, ["--check", "--no-lean"])[0], 0)

    def test_every_manifest_scenario_has_a_row(self):
        block = g.scenarios_block(TEXT)
        for n in range(1, 29):
            self.assertIn(f"({n}, [", block)


class FailClosed(unittest.TestCase):
    def rows(self):
        return [dict(r) for r in g.portfolio_ledger.build(ROOT)]

    def test_unknown_premise(self):
        rows = self.rows() + [{"id": "brand_new_premise", "kind": "environment", "scenarios": ["SC-03"]}]
        with self.assertRaisesRegex(g.GenError, "brand_new_premise.*no `Prem` constructor"):
            g.scenarios_block(TEXT, rows=rows)

    def test_kind_mismatch(self):
        rows = self.rows()
        rows[0]["kind"] = "organisational" if rows[0]["kind"] != "organisational" else "environment"
        with self.assertRaisesRegex(g.GenError, "Prem.kind"):
            g.scenarios_block(TEXT, rows=rows)

    def test_premise_order_is_constructor_order(self):
        order, names, _ = g.prem_facts(TEXT)
        rank = {c: i for i, c in enumerate(order)}
        for line in g.scenarios_block(TEXT).splitlines()[2:]:
            ctors = re.findall(r"\.(\w+)", line.split("[", 1)[1])
            self.assertEqual(ctors, sorted(ctors, key=rank.get), line)


PROBE = "\n".join(
    [f"ROOTS {n}|ControlStack.TrustRoot.Root.kernelMediation,ControlStack.TrustRoot.Root.measuredRates"
     for n in (1, 2, 3)] +
    ["COUNT ControlStack.TrustRoot.Root.kernelMediation|3|true|kernel_mediation",
     "COUNT ControlStack.TrustRoot.Root.issuerAuthenticity|1|true|issuer_authenticity",
     "COUNT ControlStack.TrustRoot.Root.measuredRates|3|false|measured_rates (residual)",
     "COUNT ControlStack.TrustRoot.Root.keyCustody|0|true|key_custody"])


class Probe(unittest.TestCase):
    def test_probe_source_replaces_block_and_drops_prints(self):
        src = g.lean_probe_source(TEXT)
        self.assertIn("IO.println (\"ROOTS ", src)
        self.assertNotIn("theorem scenario_roots_table", src)
        self.assertNotIn("#print axioms", src)

    def test_tables_from_probe(self):
        roots, counts = g.parse_probe(PROBE)
        self.assertEqual(roots[2], ["kernelMediation", "measuredRates"])
        block = g.root_tables_block(roots, counts)
        self.assertIn("(1, [.kernelMediation, .measuredRates])", block)
        # keyCustody is unused: the portfolio list is literal, not `allRoots`
        self.assertIn("= [.kernelMediation, .issuerAuthenticity, .measuredRates] ∧", block)
        self.assertIn("(allRoots.filter Root.technical).length = 3", block)
        self.assertIn("Root.kernelMediation ∈ scenarioRoots s.1))).length = 3", block)
        self.assertIn(".length ≤ 3 := by", block)
        self.assertIn("technical `kernel_mediation` (3 of 3 scenarios)", block)
        doc = [l for l in block.splitlines() if "Root sharing" in l or l.startswith("technical")]
        self.assertTrue(doc and all(len(l) <= 120 for l in doc), doc)
        summary = g.summary_block(roots, counts)
        self.assertIn("rests on 3 of the 4 roots: 2 technical, 1 residual", summary)

    def test_probe_failure_is_an_error(self):
        def runner(argv, **kw):
            return SimpleNamespace(returncode=1, stdout="", stderr="x.lean:1:0: error: boom")
        with self.assertRaisesRegex(g.GenError, "Lean probe failed"):
            g.run_lean_probe(TEXT, runner=runner)

    def test_drift_detected_and_rewritten(self):
        d = Path(tempfile.mkdtemp())
        try:
            (d / g.TR).parent.mkdir(parents=True)
            shutil.copytree(ROOT / "scenarios", d / "scenarios",
                            ignore=shutil.ignore_patterns("evidence", "harness", "llm_*"))
            shutil.copytree(ROOT / "stack", d / "stack")
            row27 = re.search(r"\(27, \[[^\]]*\]\)", TEXT).group(0)
            stale = TEXT.replace(row27, "(27, [.independentAnchor])")
            self.assertNotEqual(stale, TEXT)
            (d / g.TR).write_text(stale, encoding="utf-8")

            def runner(argv, **kw):
                return SimpleNamespace(returncode=0, stdout=PROBE, stderr="")
            rc, err = quiet(g.main, ["--check", "--no-lean"], root=d, runner=runner)
            self.assertEqual(rc, 1)
            self.assertIn("drift", err)
            self.assertEqual(quiet(g.main, ["--no-lean"], root=d, runner=runner)[0], 0)
            fixed = (d / g.TR).read_text(encoding="utf-8")
            self.assertIn(row27, fixed)
            self.assertEqual(quiet(g.main, ["--check", "--no-lean"], root=d, runner=runner)[0], 0)
            # with the (canned) Lean probe the root tables are rewritten from its output
            self.assertEqual(quiet(g.main, [], root=d, runner=runner)[0], 0)
            self.assertIn("(3, [.kernelMediation, .measuredRates])] := by",
                          (d / g.TR).read_text(encoding="utf-8"))
        finally:
            shutil.rmtree(d)


if __name__ == "__main__":
    unittest.main()
