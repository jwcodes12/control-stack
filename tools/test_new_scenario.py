#!/usr/bin/env python3
"""Tests for tools/new_scenario.py. The generator runs into a temporary directory that contains only the folders it
needs; the generated Lean skeleton is compiled with the real repo's Lake environment from a scratch path, and the
generated Python skeletons are imported and exercised in fresh interpreters. Nothing is written into the repo."""
import contextlib
import copy
import hashlib
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
import textwrap
import unittest
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO))
from tools import new_scenario as NS  # noqa: E402

SCRATCH = Path(os.environ.get("NEW_SCENARIO_SCRATCH",
                              "/tmp/claude-1000/-home-opc-research-control-stack/"
                              "f2799fc2-92e0-4405-885c-9462334ce3b5/scratchpad"))
LEAN = "ControlStack/Scenarios/SC99Demo.lean"
HARNESS = "scenarios/SC-99/harness"
PREREG = "prereg/SC99-DRAFT.md"
ALL = [LEAN, f"{HARNESS}/model.py", f"{HARNESS}/check_trace.py", f"{HARNESS}/run_sc99.py", PREREG]


def cli(*args):
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        try:
            rc = NS.main([str(a) for a in args])
        except SystemExit as e:
            rc = e.code
    return rc, out.getvalue(), err.getvalue()


def py(code, cwd):
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    env.pop("SC99_PREREG_SHA256", None)
    return subprocess.run([sys.executable, "-c", textwrap.dedent(code)], cwd=str(cwd), env=env,
                          capture_output=True, text=True, timeout=120)


def strip_lean_comments(src):
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and src.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            i += 1
        elif src.startswith("--", i):
            j = src.find("\n", i)
            i = len(src) if j < 0 else j
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


class Base(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name) / "repo"
        for d in ("ControlStack/Scenarios", "scenarios", "prereg"):  # only what the generator needs
            (self.root / d).mkdir(parents=True)
        self.spec = copy.deepcopy(NS.EXAMPLE)
        self.spec_path = Path(self.tmp.name) / "spec.json"

    def gen(self, spec=None, *extra):
        self.spec_path.write_text(json.dumps(self.spec if spec is None else spec))
        return cli("SC-99", self.spec_path, "--root", self.root, *extra)

    def digest(self):
        return {p: hashlib.sha256((self.root / p).read_bytes()).hexdigest()
                for p in ALL if (self.root / p).exists()}


class Generation(Base):
    def test_writes_every_file(self):
        rc, out, err = self.gen()
        self.assertEqual(rc, 0, err)
        for p in ALL:
            self.assertTrue((self.root / p).is_file(), p)
        self.assertIn("no manifest.json", out)  # check_scenarios.py would otherwise fail silently later

    def test_refuses_overwrite_and_writes_nothing(self):
        self.assertEqual(self.gen()[0], 0)
        before = self.digest()
        rc, _, err = self.gen()
        self.assertEqual(rc, 1)
        self.assertIn("REFUSING", err)
        self.assertEqual(before, self.digest())

    def test_one_existing_target_blocks_all(self):
        (self.root / PREREG).write_text("mine")
        rc, _, err = self.gen()
        self.assertEqual(rc, 1)
        self.assertIn(f"exists: {PREREG}", err)
        self.assertEqual((self.root / PREREG).read_text(), "mine")
        self.assertFalse((self.root / LEAN).exists())

    def test_namespace_clash(self):
        (self.root / "ControlStack/Scenarios/SC99Other.lean").write_text("")
        rc, _, err = self.gen()
        self.assertEqual(rc, 1)
        self.assertIn("namespace clash", err)

    def test_dry_run_writes_nothing(self):
        rc, out, _ = self.gen(None, "--dry-run")
        self.assertEqual(rc, 0)
        self.assertIn("would write", out)
        self.assertEqual(self.digest(), {})

    def test_example_spec_cli(self):
        rc, out, _ = cli("--example-spec")
        self.assertEqual(rc, 0)
        self.assertEqual(json.loads(out)["id"], "SC-99")

    def test_halt_added_when_absent(self):
        v = NS.validate(self.spec, "SC-99")
        self.assertEqual(v["ops"][-1]["name"], "halt")
        self.assertEqual(v["ops"][-1]["args"], {"caller": "Nat"})

    def test_spec_validation_fails_closed(self):
        def mut(f):
            s = copy.deepcopy(NS.EXAMPLE)
            f(s)
            return s
        cases = {
            "lean keyword op": (mut(lambda s: s["ops"][0].update(name="match")), "reserved"),
            "model name op": (mut(lambda s: s["ops"][0].update(name="guard")), "reserved"),
            "bad CamelCase name": (mut(lambda s: s.update(name="demo")), "CamelCase"),
            "duplicate finding": (mut(lambda s: s["checks"][1].update(finding="c2")), "OWN specific finding"),
            "rule reuses finding": (mut(lambda s: s["rules"].append({"id": "c1", "doc": "x"})), "already used"),
            "no admins": (mut(lambda s: s.update(roles=["agents", "approvers"])), "admins"),
            "role named gate": (mut(lambda s: s["roles"].append("gate")), "gate"),
            "id mismatch": (mut(lambda s: s.update(id="SC-98")), "does not match"),
            "unknown key": (mut(lambda s: s.update(extra=1)), "unknown keys"),
            "bad arg type": (mut(lambda s: s["ops"][0]["args"].update(x="String")), "type must be"),
            "payload field key": (mut(lambda s: s["effect"]["payload"].update(key="Nat")), "reserved"),
            "namedtuple field": (mut(lambda s: s["checks"][0].update(name="count")), "reserved"),
            "comment delimiter": (mut(lambda s: s.update(title="x -/ y")), "comment delimiters"),
            "no checks": (mut(lambda s: s.update(checks=[])), "checks"),
            "bad halt": (mut(lambda s: s["ops"].append({"name": "halt", "doc": "h", "args": {}})), "halt"),
        }
        for name, (spec, pat) in cases.items():
            with self.subTest(name):
                with self.assertRaisesRegex(NS.SpecError, pat):
                    NS.validate(spec, "SC-99")
                rc, _, err = self.gen(spec)
                self.assertEqual(rc, 1)
                self.assertIn("INVALID SPEC", err)
                self.assertEqual(self.digest(), {})

    def test_bad_scenario_id(self):
        self.spec_path.write_text(json.dumps(self.spec))
        rc, _, err = cli("SC-9", self.spec_path, "--root", self.root)
        self.assertEqual(rc, 1)
        self.assertIn("invalid scenario id", err)

    def test_prereg_has_every_sc26_section_and_lessons(self):
        self.assertEqual(self.gen()[0], 0)
        got = (self.root / PREREG).read_text()
        ref = (REPO / "prereg/SC26-TRANSACTION-GATE-v2.md").read_text()
        for h in re.findall(r"^## (\d+\. .+)$", ref, re.M):
            self.assertIn(f"## {h}", got, h)  # same numbered section titles, including 7. Pinned artifacts
        for lesson in ("Pin hashes in the prereg", "Controls must fire their specific finding",
                       "Dev runs are labelled dry", "Every reconciliation rule can fire", "every crash window",
                       "HALT claim matches the model", "necessity witness per check"):
            self.assertIn(lesson.lower(), got.lower(), lesson)
        for c in NS.EXAMPLE["checks"]:  # H5 table: each disabled check -> its specific finding
            self.assertIn(f"| {c['name']} | {c['finding']}:", got)
        self.assertIn(f"| `{LEAN}` | `PENDING` |", got)

    def test_lean_skeleton_shape(self):
        self.assertEqual(self.gen()[0], 0)
        src = (self.root / LEAN).read_text()
        code = strip_lean_comments(src)
        self.assertNotIn("sorry", code)  # placeholders compile without sorry; TODO blocks are comments
        for decl in ("structure Checks", "def full", "structure Sound", "theorem sound_full", "structure St",
                     "inductive Op", "def init", "def step", "def run", "def legal", "def sys", "namespace "
                     "ControlStack.SC99"):
            self.assertIn(decl, code)
        for todo in ("structure Inv", "def Good", "theorem sc99_safe", "theorem halt_freezes", "def spec",
                     "theorem honest_trace_effects", "theorem no_payload_breaks", "theorem no_auth_breaks"):
            self.assertIn(todo, src)
            self.assertNotIn(todo, code)


class GeneratedPython(Base):
    def setUp(self):
        super().setUp()
        rc, _, err = self.gen()
        self.assertEqual(rc, 0, err)
        self.h = self.root / HARNESS

    def test_model_mirrors_spec(self):
        r = py("""
            import sys; sys.path.insert(0, '.')
            import model as M
            assert M.OPS == ('request', 'approve', 'deliver', 'directCall', 'halt'), M.OPS
            assert all(M.FULL) and M.Checks._fields == ('payload', 'distinct', 'haltCheck', 'auth')
            assert M.sound(M.FULL) and not M.sound(M.FULL._replace(payload=False))
            assert M.sound(M.FULL._replace(haltCheck=False))  # not in Sound
            ops = [M.request(1, (5, 10)), M.approve(2, 0, (5, 10)), M.deliver(0), M.directCall(1, 0, (5, 10)),
                   M.halt(3)]
            R = M.Roles((1,), (2,), (3,), 9)
            assert M.run(R, M.FULL, M.INIT, ops) == M.INIT  # placeholder step = identity, as in Lean
            assert M.op_from_row('approve', {'caller': 2, 'id': 0, 'p': {'dest': 5, 'amount': 10}}) == ops[1]
            for f in (lambda: M.guard(R, M.FULL, M.INIT, ops[0]), lambda: M.inv(R, M.INIT),
                      lambda: M.good(R, M.INIT)):
                try:
                    f(); raise SystemExit('unwritten part did not raise')
                except NotImplementedError:
                    pass
            print(M.to_lean(ops))
        """, self.h)
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn("Op.directCall 1 0 ⟨5, 10⟩", r.stdout)

    def test_check_trace_fail_closed(self):
        r = py("""
            import sys, json; sys.path.insert(0, '.')
            import check_trace as T
            assert sorted(T.RULES) == ['c1', 'c2', 'c3', 'c4', 'c5'], sorted(T.RULES)
            assert T.CONTROL_RULE == {'payload': 'c2', 'distinct': 'c3', 'haltCheck': 'c4', 'auth': 'c1'}
            cfg = {'agents': [1], 'approvers': [2], 'admins': [3], 'gate_uid': 9}
            empty = T.check({'config': cfg, 'trace': [], 'effects': []})
            assert empty['verdict'] == 'INCOMPLETE', empty  # unwritten rules never PASS
            row = {'seq': 0, 'op': 'request', 'args': {'caller': 1, 'p': {'dest': 5, 'amount': 10}}, 'accepted': 1}
            one = T.check({'config': cfg, 'trace': [row], 'effects': [{'key': 0, 'dest': 5, 'amount': 10}]})
            assert one['verdict'] == 'FAIL' and one['b_world'], one  # the world has an effect the model lacks
            print(json.dumps(empty['not_implemented']))
        """, self.h)
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn("(c) c1", r.stdout)

    def test_runner_conventions(self):
        ev = self.root / "scenarios/SC-99/evidence/run-1"
        r = py(f"""
            import sys, os, hashlib, json
            from pathlib import Path
            sys.path.insert(0, '.')
            import run_sc99 as RN
            assert RN.SCENARIO == 'SC-99' and RN.CONTROLS == ['payload', 'distinct', 'haltCheck', 'auth']
            # 1. a DRAFT prereg refuses the evidence label
            try:
                RN.main(['--label', 'evidence', '--out', {str(ev)!r}]); raise SystemExit('not refused')
            except SystemExit as e:
                assert 'DRAFT' in str(e), e
            assert not Path({str(ev)!r}).exists()
            # 2. a frozen prereg: env sha, out dir, pinned hashes and git cleanliness are each required
            frozen = RN.REPO / 'prereg/SC99-DEMO-v1.md'
            m = RN.HERE / 'model.py'
            frozen.write_text('| `scenarios/SC-99/harness/model.py` | `' + '0' * 64 + '` |\\n')
            RN.PREREG = frozen
            reasons = [RN.evidence_refusal(Path({str(ev)!r}))]
            os.environ['SC99_PREREG_SHA256'] = RN.sha(frozen)
            reasons.append(RN.evidence_refusal(Path('/tmp/elsewhere')))
            reasons.append(RN.evidence_refusal(Path({str(ev)!r})))
            frozen.write_text('| `scenarios/SC-99/harness/model.py` | `' + RN.sha(m) + '` |\\n')
            os.environ['SC99_PREREG_SHA256'] = RN.sha(frozen)
            reasons.append(RN.evidence_refusal(Path({str(ev)!r})))  # not a git repo -> refused
            print(json.dumps(reasons))
        """, self.h)
        self.assertEqual(r.returncode, 0, r.stderr + r.stdout)
        reasons = json.loads(r.stdout.strip().splitlines()[-1])
        self.assertIn("SC99_PREREG_SHA256", reasons[0])
        self.assertIn("evidence", reasons[1])
        self.assertIn("pinned artifacts do not match", reasons[2])
        self.assertIn("committed and unmodified", reasons[3])

    def test_dry_run_receipt_and_no_overwrite(self):
        out = Path(self.tmp.name) / "dry1"
        code = f"""
            import sys; sys.path.insert(0, '.')
            import run_sc99 as RN
            sys.exit(RN.main(['--out', {str(out)!r}]))
        """
        r = py(code, self.h)
        self.assertEqual(r.returncode, 1, r.stderr)  # nothing implemented -> FAIL, never PASS
        rec = json.loads((out / "receipt.json").read_text())
        self.assertEqual((rec["label"], rec["verdict"]), ("dry-run", "FAIL"))
        self.assertTrue(all(p["verdict"] == "ERROR" for p in rec["phases"].values()))
        self.assertIn("model.py", rec["harness_sha256"])
        r = py(code, self.h)
        self.assertNotEqual(r.returncode, 0)
        self.assertIn("refusing to overwrite", r.stderr)


@unittest.skipUnless(shutil.which("lake") and (REPO / "lakefile.lean").exists(), "lake not available")
class LeanCompile(Base):
    def compile_with_eval(self, lean_rel, harness, ns, py_ops, py_roles):
        """append a Python-rendered `#eval run ... == init` to the generated file; compile it from a scratch path"""
        r = py(f"""
            import sys; sys.path.insert(0, '.')
            import model as M
            ops = {py_ops}
            R = {py_roles}
            print(f"#eval (run {{M.roles_to_lean(R)}} {{M.checks_to_lean(M.FULL)}} init {{M.to_lean(ops)}}) == init")
        """, harness)
        self.assertEqual(r.returncode, 0, r.stderr)
        SCRATCH.mkdir(parents=True, exist_ok=True)
        d = Path(tempfile.mkdtemp(prefix="newscen-", dir=str(SCRATCH)))
        self.addCleanup(shutil.rmtree, d, True)
        f = d / Path(lean_rel).name
        f.write_text((self.root / lean_rel).read_text() + f"\nopen {ns} in\n" + r.stdout)
        p = subprocess.run(["lake", "env", "lean", str(f)], cwd=str(REPO), capture_output=True, text=True,
                           timeout=900)
        self.assertEqual(p.returncode, 0, p.stdout + p.stderr)
        self.assertEqual(p.stdout.strip(), "true")  # Python's rendering parses in Lean; placeholder step = identity
        self.assertNotIn("sorry", p.stdout + p.stderr)
        self.assertNotIn("warning", p.stdout + p.stderr)

    def test_generated_skeleton_compiles_and_matches_python_rendering(self):
        self.assertEqual(self.gen()[0], 0)
        self.compile_with_eval(
            LEAN, self.root / HARNESS, "ControlStack.SC99",
            "[M.request(1, (5, 10)), M.approve(2, 0, (5, 10)), M.deliver(0), M.directCall(1, 0, (5, 10)), M.halt(3)]",
            "M.Roles((1,), (2,), (3,), 9)")

    def test_edge_case_spec_compiles(self):
        """Bool payload, a zero-argument op, a Bool argument, no check in Sound, one role"""
        spec = {"name": "Edge", "title": "edge case", "bad_event": "x", "roles": ["admins"],
                "effect": {"name": "log", "doc": "d", "payload": {"flag": "Bool"}},
                "ops": [{"name": "tick", "doc": "no args", "args": {}},
                        {"name": "setFlag", "doc": "bool arg", "args": {"b": "Bool", "p": "Payload"}}],
                "checks": [{"name": "guardOn", "doc": "g", "sound": False, "finding": "c1", "finding_doc": "f"}]}
        self.spec_path.write_text(json.dumps(spec))
        rc, _, err = cli("SC-98", self.spec_path, "--root", self.root)
        self.assertEqual(rc, 0, err)
        self.compile_with_eval("ControlStack/Scenarios/SC98Edge.lean", self.root / "scenarios/SC-98/harness",
                               "ControlStack.SC98", "[M.tick(), M.setFlag(True, (False,)), M.halt(1)]",
                               "M.Roles((1,), 9)")


if __name__ == "__main__":
    unittest.main()
