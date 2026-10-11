#!/usr/bin/env python3
"""Every static bypass is repaired in the finite model or has an exact residual.
Prospective inventories are DECLARED unit hypotheses, never container observations.
"""
import copy
import json
import sys
import subprocess
import tempfile
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from deployment.plan import build_plan,apply_patch
from extractors.compose import collect,sha
from security_ir.verifier import verify
from tools.check_deployment_subset_differential import configuration_accepted


def proposed_inventory(c,original_c,observed):
    r={'services':{name:{'uid':int(s['user']),'image':s['image'],'mounts':sorted([{k:v for k,v in m.items() if k!='bind'} for m in s['volumes']],key=lambda m:(m['source'],m['target'])),'networks':s['networks'],'env_names':sorted(s['environment'])} for name,s in c['services'].items()}}
    for key,value in observed.items():
        if key!='services':r[key]=copy.deepcopy(value)
    for name,data in observed['services'].items():
        if name not in r['services']:continue
        for key,value in data.items():
            if key not in {'uid','image','mounts','networks','env_names'}:r['services'][name][key]=copy.deepcopy(value)
        # An unchanged UID declaration cannot erase a measured UID mismatch.
        if data['uid']!=int(original_c['services'][name]['user']) and c['services'][name]['user']==original_c['services'][name]['user']:r['services'][name]['uid']=data['uid']
    return r

HARDENING_OPS=4

def matrix():
    base=ROOT/'examples/compose-two-agent';rows=[];irs=[]
    with tempfile.TemporaryDirectory(prefix='cstack-r2-plan-',dir=ROOT/'.git') as tmp:
        cp=Path(tmp)/'compose.json';rp=Path(tmp)/'runtime.json'
        for source in sorted(base.glob('*.compose.json')):
            name=source.name.removesuffix('.compose.json');c=json.loads(source.read_text());runtime=base/(name+'.runtime.json');r=json.loads(runtime.read_text());ir=collect(source,runtime,sha(source))
            plan=build_plan(c,r,ir,sha(source));candidate=apply_patch(c,plan['patch'])
            cp.write_text(json.dumps(candidate));rp.write_text(json.dumps(proposed_inventory(candidate,c,r)))
            proposed=collect(cp,rp,sha(cp),replay=True)  # the legacy corpus is frozen at the vaulted r2-v0 broker/receiver pins
            for p in proposed['sources']+[n['provenance'] for n in proposed['nodes']+proposed['edges']]:
                if p['sha256']==sha(rp):p['kind']='DECLARED'
            accepted=configuration_accepted(proposed);bad=[o for o in verify(proposed)['obligations'] if o['status'] in {'REFUTED','UNASSESSED'} and o['premise']!='Lean-contract-instances']
            if not accepted:
                assert plan['residuals'],name
                for o in bad:
                    if o['premise'].startswith('runtime-snapshot:'):
                        assert any(o['premise'].split(':',1)[1] in p['path'] for p in plan['residuals']),(name,o)
                    elif 'read_only' in o['detail']:assert any('read_only' in p['path'] for p in plan['residuals']),(name,o)
                    else:assert any(p['path'].startswith('/runtime/') for p in plan['residuals']),(name,o)
            # Since T9.4 the planner also adds no-new-privileges and cap_drop ALL to the two agents (4 operations).
            hardening=[op for op in plan['patch'] if {'security_opt','cap_drop'}&set(op['path'].split('/'))]
            assert len(hardening)==HARDENING_OPS,(name,len(hardening))
            if name=='clean':assert plan['patch']==hardening
            if name in {'writable-sink-mount','trusted-role-uid-collision'}:assert len(plan['patch'])==1+HARDENING_OPS
            rows.append({'case':name,'patch_ops':len(plan['patch']),'prospective_model_accepted':accepted,'remaining_model_causes':bad,'residuals':plan['residuals'],'basis':'synthetic declared selected facts; not runtime evidence'})
            irs.append(proposed)
    return rows,irs

class PlanTests(unittest.TestCase):
    def test_every_fixture_and_exact_residual(self):
        rows,_=matrix();self.assertEqual(len(rows),44);self.assertGreaterEqual(sum(r['prospective_model_accepted'] for r in rows),35)
    def test_cli_is_read_only_and_redacts_removed_values(self):
        base=ROOT/'examples/compose-two-agent';paths=[base/'credential-password.compose.json',base/'credential-password.runtime.json',ROOT/'security_ir/fixtures/credential-password.json'];before=[p.read_bytes() for p in paths]
        with tempfile.TemporaryDirectory(prefix='cstack-r2-plan-cli-',dir=ROOT/'.git') as tmp:
            out=Path(tmp)/'plan.json';p=subprocess.run([sys.executable,str(ROOT/'tools/cstack.py'),'plan',str(paths[0]),'--runtime',str(paths[1]),'--ir',str(paths[2]),'--output',str(out)],capture_output=True,text=True)
            self.assertEqual(p.returncode,0,p.stderr);plan=json.loads(out.read_text());self.assertNotIn('dummy-only',out.read_text());self.assertTrue(any(op['path'].endswith('/PASSWORD') for op in plan['patch']))
        self.assertEqual(before,[p.read_bytes() for p in paths])
    def test_pointer_escaping_and_input_pin(self):
        c={'services':{'a/b~c':{'PASSWORD':'x'}}};ops=[{'op':'remove','path':'/services/a~1b~0c/PASSWORD'}]
        self.assertEqual(apply_patch(c,ops),{'services':{'a/b~c':{}}});self.assertEqual(c['services']['a/b~c']['PASSWORD'],'x')
        base=ROOT/'examples/compose-two-agent'
        with tempfile.TemporaryDirectory(prefix='cstack-r2-plan-pin-',dir=ROOT/'.git') as tmp:
            wrong=Path(tmp)/'wrong.json';wrong.write_text('{}');out=Path(tmp)/'plan.json'
            p=subprocess.run([sys.executable,str(ROOT/'tools/cstack.py'),'plan',str(wrong),'--runtime',str(base/'clean.runtime.json'),'--ir',str(ROOT/'security_ir/fixtures/clean.json'),'--output',str(out)],capture_output=True,text=True)
            self.assertEqual(p.returncode,2);self.assertFalse(out.exists())
    def test_missing_source_pin_is_named_and_not_invented(self):
        base=ROOT/'examples/compose-two-agent';c=json.loads((base/'clean.compose.json').read_text());r=json.loads((base/'clean.runtime.json').read_text())
        ir=json.loads((ROOT/'security_ir/fixtures/clean.json').read_text());del c['x-cstack']['broker_sha256']
        result=build_plan(c,r,ir,'unit-test-pin')
        self.assertTrue(any(item['path']=='/x-cstack/broker_sha256' for item in result['residuals']))
        self.assertFalse(any(operation['path']=='/x-cstack/broker_sha256' for operation in result['patch']))

    def test_missing_trusted_service_never_proposes_root_ownership(self):
        base=ROOT/'examples/compose-two-agent';c=json.loads((base/'clean.compose.json').read_text());r=json.loads((base/'clean.runtime.json').read_text())
        ir=json.loads((ROOT/'security_ir/fixtures/clean.json').read_text());del c['services']['receiver']
        path=c['x-cstack']['sink_source'];host={'resolutions':{path:{'status':'OBSERVED','type':'directory','realpath':path,'uid':23700,'mode':'0o777'}},'images':{}}
        result=build_plan(c,r,ir,'unit-test-pin',host)
        self.assertFalse(any(action['path']==path for action in result['host_actions']))
        self.assertTrue(any(item['path']=='/x-cstack/sink_source' and 'missing trusted principal' in item['reason'] for item in result['residuals']))

    def test_relocated_archive_cli_preserves_pins(self):
        import shutil
        source=ROOT/'deployment/runs/tier3/containers-final/writable-sink-mount'
        with tempfile.TemporaryDirectory(prefix='cstack-r2-plan-relocate-',dir=ROOT/'.git') as tmp:
            archive=Path(tmp)/'archive';shutil.copytree(source,archive);out=Path(tmp)/'plan.json'
            # Make archived source labels unusable without changing any observation.
            ir_path=archive/'ir.json';ir=json.loads(ir_path.read_text())
            for p in ir['sources']+[item['provenance'] for item in ir['nodes']+ir['edges']]:p['source']='/unavailable-original/'+Path(p['source']).name
            ir_path.write_text(json.dumps(ir))
            argv=[sys.executable,str(ROOT/'tools/cstack.py'),'plan',str(archive/'compose.json'),'--runtime',str(archive/'runtime.json'),'--ir',str(ir_path),'--output',str(out)]
            result=subprocess.run(argv,capture_output=True,text=True);self.assertEqual(result.returncode,0,result.stderr)
            self.assertEqual(len(json.loads(out.read_text())['patch']),1+HARDENING_OPS)
            facts_path=archive/'fresh-inputs/host-observations.json';saved=facts_path.read_bytes()
            overwrite=argv[:-1]+[str(facts_path)]
            refused=subprocess.run(overwrite,capture_output=True,text=True);self.assertEqual(refused.returncode,2);self.assertEqual(saved,facts_path.read_bytes())
            out.unlink();facts=archive/'fresh-inputs/host-observations.json';facts.write_text(facts.read_text()+' ')
            result=subprocess.run(argv,capture_output=True,text=True);self.assertEqual(result.returncode,2);self.assertFalse(out.exists())

    def test_fresh_archive_names_host_custody_and_runtime_changes(self):
        case=ROOT/'deployment/runs/tier3/containers-final/writable-sink-mount'
        paths=[case/'compose.json',case/'runtime.json',case/'ir.json'];before=[p.read_bytes() for p in paths]
        with tempfile.TemporaryDirectory(prefix='cstack-r2-plan-fresh-',dir=ROOT/'.git') as tmp:
            out=Path(tmp)/'plan.json';p=subprocess.run([sys.executable,str(ROOT/'tools/cstack.py'),'plan',str(paths[0]),'--runtime',str(paths[1]),'--ir',str(paths[2]),'--output',str(out)],capture_output=True,text=True)
            self.assertEqual(p.returncode,0,p.stderr);result=json.loads(out.read_text())
            self.assertEqual(len(result['patch']),1+HARDENING_OPS);self.assertEqual(result['host_actions'][0]['mode'],'0o700');self.assertTrue(any(r['path'].endswith('/mounts') for r in result['residuals']))
        self.assertEqual(before,[p.read_bytes() for p in paths])
if __name__=='__main__':unittest.main()
