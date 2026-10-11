#!/usr/bin/env python3
"""T8.4 stable outputs: JSON schemas, documented exit codes and golden-output regression."""
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from deployment.schema_check import validate
from deployment.demo import render
from extractors.compose import sha
from deployment.plan import build_plan
from security_ir.verifier import verify,report
GOLDEN=ROOT/'deployment/golden';EXAMPLES=HARDENED=ROOT/'examples/compose-two-agent-hardened'
def schema(name):return json.loads((ROOT/'deployment/schemas'/(name+'-v0.1.json')).read_text())
def cstack(*args):return subprocess.run([sys.executable,str(ROOT/'tools/cstack.py'),*map(str,args)],cwd=ROOT,capture_output=True,text=True)

class Release(unittest.TestCase):
    def test_golden_bundles_reports_and_schema(self):
        for name,fixtures in (('clean','fixtures'),('writable-sink-mount','fixtures'),('trusted-role-uid-collision','fixtures'),('hardened-clean','fixtures-hardened')):
            with self.subTest(name=name):
                bundle=verify(json.loads((ROOT/'security_ir'/fixtures/(name.removeprefix('hardened-')+'.json')).read_text()))
                validate(bundle,schema('bundle'))
                self.assertEqual(bundle,json.loads((GOLDEN/(name+'.bundle.json')).read_text()))
                self.assertEqual(report(bundle),(GOLDEN/(name+'.report.md')).read_text())
    def test_golden_plans_and_schema(self):
        for name in ('writable-sink-mount','trusted-role-uid-collision'):
            with self.subTest(name=name):
                c=HARDENED/(name+'.compose.json');r=HARDENED/(name+'.runtime.json')
                plan=build_plan(json.loads(c.read_text()),json.loads(r.read_text()),json.loads((ROOT/'security_ir/fixtures-hardened'/(name+'.json')).read_text()),sha(c))
                validate(plan,schema('plan'))
                self.assertEqual(plan,json.loads((GOLDEN/(name+'.plan.json')).read_text()))
    def test_schema_rejects_assured_and_unknown_status(self):
        bundle=json.loads((GOLDEN/'clean.bundle.json').read_text())
        for mutate in (lambda b:b.update(verdict='ASSURED'),lambda b:b['obligations'][0].update(status='DENIED'),lambda b:b.update(extra=1)):
            b=json.loads(json.dumps(bundle));mutate(b)
            with self.assertRaises(ValueError):validate(b,schema('bundle'))
    def test_documented_exit_codes(self):
        with tempfile.TemporaryDirectory() as tmp:
            tmp=Path(tmp)
            # verify: 0 CONDITIONAL, 1 UNASSURED (including skipped Lean), 2 invalid input
            self.assertEqual(cstack('verify','security_ir/fixtures/clean.json','--output',tmp/'a.json').returncode,1)
            self.assertEqual(json.loads((tmp/'a.json').read_text())['verdict'],'UNASSURED')
            self.assertEqual(cstack('verify','security_ir/fixtures/writable-sink-mount.json','--output',tmp/'b.json').returncode,1)
            (tmp/'bad.json').write_text('{"version":"0.1"}')
            p=cstack('verify',tmp/'bad.json','--output',tmp/'c.json');self.assertEqual(p.returncode,2);self.assertIn('cstack:',p.stderr)
            # report: 0 rendered, 2 invalid bundle
            self.assertEqual(cstack('report',GOLDEN/'clean.bundle.json','--output',tmp/'r.md').returncode,0)
            self.assertEqual((tmp/'r.md').read_text(),(GOLDEN/'clean.report.md').read_text())
            b=json.loads((GOLDEN/'clean.bundle.json').read_text());b['verdict']='ASSURED';(tmp/'assured.json').write_text(json.dumps(b))
            self.assertEqual(cstack('report',tmp/'assured.json','--output',tmp/'x.md').returncode,2)
            # plan: 0 proposal, 2 output overwriting an input
            n='writable-sink-mount';args=[EXAMPLES/(n+'.compose.json'),'--runtime',EXAMPLES/(n+'.runtime.json'),'--ir',ROOT/'security_ir/fixtures-hardened'/(n+'.json')]
            self.assertEqual(cstack('plan',*args,'--output',tmp/'p.json').returncode,0)
            self.assertEqual(json.loads((tmp/'p.json').read_text()),json.loads((GOLDEN/(n+'.plan.json')).read_text()))
            self.assertEqual(cstack('plan',*args,'--output',ROOT/'security_ir/fixtures-hardened'/(n+'.json')).returncode,2)
            # demo: 2 when the output directory already exists
            self.assertEqual(cstack('demo','--output',tmp).returncode,2)
    def test_demo_summary_schema_and_archived_run(self):
        stages=[{'stage':s,'status':'SKIPPED','detail':'x','seconds':0} for s in 'abcd']
        validate({'result':'SKIPPED','exit':3,'stages':stages,'scope':'s'},schema('demo'))
        self.assertIn('SKIPPED',render({'result':'SKIPPED','exit':3,'stages':stages,'scope':'s'}))
        with self.assertRaises(ValueError):validate({'result':'PASS','exit':3,'stages':stages[:2],'scope':'s'},schema('demo'))
        for path in sorted((ROOT/'deployment/runs/tier8').glob('*/demo.json')):
            with self.subTest(path=str(path.relative_to(ROOT))):
                summary=json.loads(path.read_text());validate(summary,schema('demo'))
                statuses={s['status'] for s in summary['stages']}
                self.assertEqual(summary['result'],'FAIL' if 'FAIL' in statuses else 'SKIPPED' if 'SKIPPED' in statuses else 'PASS')

    def test_sink_audit_over_archives(self):
        from deployment.sink_audit import audit,clean
        finals=sorted(f for f in (ROOT/'deployment/runs').rglob('final') if (f/'database.sqlite').is_file())
        self.assertGreaterEqual(len(finals),30)
        for f in finals:
            with self.subTest(case=str(f.relative_to(ROOT))):
                result=audit(f);self.assertEqual((result['delegations'],result['delegated_releases'],result['non_body_files']),(0,0,[]))
                # Negative control: the archived writable-sink bypass left exactly one unattributed file.
                self.assertEqual(result['unattributed_files'],['2.body'] if f.parent.name=='writable-sink-mount' and 'remediated' not in f.parts else [])
                self.assertEqual(clean(result),not result['unattributed_files'])

if __name__=='__main__':
    unittest.main()
