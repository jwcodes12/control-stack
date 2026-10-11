#!/usr/bin/env python3
"""Fresh-scan structural tests; injected image facts are not runtime evidence."""
import copy
import shutil
import json
import os
import sys
import subprocess
import tempfile
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from deployment.scan import scan
from extractors.compose import sha
from security_ir import validate,InvalidIR
from security_ir.migrate import to_v01
from security_ir.verifier import verify
from tools.check_deployment_subset_differential import configuration_accepted

def image_fixture(image):
    return {'status':'OBSERVED','image':image,'image_user':'','entrypoint':['/usr/bin/python3','/slice/entry.py'],'command':None,'setid_paths':[],'mode_inventory_sha256':'0'*64,'source_sha256':{'slice/entry.py':sha(ROOT/'tools/deployment_container_entry.py'),**{'slice/trusted_stack/'+f.name:sha(f) for f in (ROOT/'trusted_stack').glob('*.py')}},'principal_policy':{'agent':[23701,23702],'reviewer':[23703],'approver':[23704],'admin':[23700]},'basis':'injected unit fixture; no actual image assessment'}

class ScannerTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(prefix='cstack-r2-scan-test-',dir=ROOT/'.git');self.addCleanup(self.tmp.cleanup);self.base=Path(self.tmp.name)
        self.cp=self.base/'compose.json';self.rp=self.base/'runtime.json';self.out=self.base/'output'
        self.c=json.loads((ROOT/'examples/compose-two-agent/clean.compose.json').read_text());old=self.c['x-cstack']['sink_source'].rsplit('/',1)[0]
        owner=23700
        state=self.base/'state';state.mkdir()
        for name in ('db','sink','channel'):(state/name).mkdir(mode=0o755 if name=='channel' else 0o700)
        self.state=state
        subprocess.run(['sudo','-n','chown','23700:23700',*[str(state/n) for n in ('db','sink','channel')]],check=True)
        self.addCleanup(lambda:subprocess.run(['sudo','-n','chown','-R',str(os.getuid()),str(state)],check=True))
        for key in ('sink_source','database_source','channel_source'):self.c['x-cstack'][key]=str(state)+self.c['x-cstack'][key][len(old):]
        for name,s in self.c['services'].items():
            delta={'broker':0,'receiver':0,'agent-a':1,'agent-b':2,'reviewer':3,'approver':4}[name];s['user']=str(owner+delta)
            for m in s['volumes']:m['source']=str(state)+m['source'][len(old):]
        self.refresh_runtime()
    def refresh_runtime(self):
        self.r={'services':{name:{'uid':int(s['user']),'image':s['image'],'mounts':sorted([{k:v for k,v in m.items() if k!='bind'} for m in s['volumes']],key=lambda m:(m['source'],m['target'])),'networks':s['networks'],'env_names':sorted(s['environment'])} for name,s in self.c['services'].items()}}
    def run_scan(self,observer=image_fixture):
        self.cp.write_text(json.dumps(self.c));self.rp.write_text(json.dumps(self.r));return scan(self.cp,self.rp,sha(self.cp),self.out,observer)
    def test_positive_fixture_and_canonical_bytes(self):
        a=self.run_scan();self.assertTrue(configuration_accepted(a));self.assertEqual(a['version'],'0.1')
        self.cp.write_text(json.dumps(self.c,sort_keys=True,indent=4));self.rp.write_text(json.dumps(self.r,sort_keys=True,indent=4))
        b=scan(self.cp,self.rp,sha(self.cp),self.out,image_fixture)
        self.assertEqual(json.dumps(a,sort_keys=True),json.dumps(b,sort_keys=True));self.assertEqual(verify(a),verify(b))
    def test_actual_yaml_requires_explicit_role_map(self):
        lines=['services:']
        for name,service in self.c['services'].items():
            lines.append('  '+name+':')
            for key,value in service.items():
                if key!='x-cstack-role':lines.append('    '+key+': '+json.dumps(value))
        claim=copy.deepcopy(self.c['x-cstack']);claim['roles']={name:s['x-cstack-role'] for name,s in self.c['services'].items()}
        lines+=['networks: '+json.dumps(self.c['networks']),'x-cstack: '+json.dumps(claim)]
        self.cp.write_text('\n'.join(lines)+'\n');self.rp.write_text(json.dumps(self.r))
        self.assertTrue(configuration_accepted(scan(self.cp,self.rp,sha(self.cp),self.out,image_fixture)))
        claim.pop('roles');lines[-1]='x-cstack: '+json.dumps(claim);self.cp.write_text('\n'.join(lines)+'\n')
        self.assertFalse(configuration_accepted(scan(self.cp,self.rp,sha(self.cp),self.out,image_fixture)))
    def test_alias_to_protected_sink_is_refuted(self):
        alias=self.state/'alias';alias.symlink_to(self.state/'sink',target_is_directory=True)
        m=self.c['services']['agent-a']['volumes'][0];m['source']=str(alias);m['read_only']=False;self.refresh_runtime()
        ir=self.run_scan();self.assertFalse(configuration_accepted(ir));self.assertTrue(any(e['from']=='agent-a' and e['to']=='sink' and e['reachability']=='PRESENT' for e in ir['edges']))
    def test_benign_alias_and_unresolved_source(self):
        alias=self.state/'alias';alias.symlink_to(self.state/'channel',target_is_directory=True)
        self.c['services']['agent-a']['volumes'][0]['source']=str(alias);self.refresh_runtime();self.assertTrue(configuration_accepted(self.run_scan()))
        alias.unlink();ir=self.run_scan();self.assertFalse(configuration_accepted(ir));self.assertIn('unresolved-mount-source',json.dumps(ir))
    def test_unknown_setid_and_entrypoint_images(self):
        for kind in ('unknown','setid','entrypoint','code'):
            def observer(image):
                if kind=='unknown':return {'status':'UNKNOWN','reason':'unit unavailable image'}
                d=image_fixture(image)
                if kind=='setid':d['setid_paths']=['usr/bin/setuid-helper']
                elif kind=='entrypoint':d['entrypoint']=['unknown-entry']
                else:d['source_sha256']={}
                return d
            self.assertFalse(configuration_accepted(self.run_scan(observer)),kind)
    def test_declared_roles_cannot_override_baked_admin_policy(self):
        self.c['services']['broker']['user']='23800';self.c['services']['receiver']['user']='23800'
        self.c['services']['agent-a']['user']='23700'
        subprocess.run(['sudo','-n','chown','23800:23800',*[str(self.state/n) for n in ('db','sink','channel')]],check=True)
        self.refresh_runtime();ir=self.run_scan();self.assertFalse(configuration_accepted(ir));self.assertIn('image-principal-policy-mismatch-UNKNOWN',json.dumps(ir))
    def test_nonprivate_custody_is_unknown(self):
        subprocess.run(['sudo','-n','chmod','777',str(self.state/'sink')],check=True);ir=self.run_scan();self.assertIn('private-store-custody-UNKNOWN',json.dumps(ir));self.assertFalse(configuration_accepted(ir))
    def test_migration_does_not_invent_observations_or_accept_unknown_fields(self):
        old=json.loads((ROOT/'security_ir/fixtures/clean.json').read_text());new=to_v01(old)
        self.assertEqual(new['version'],'0.1');self.assertEqual(new['nodes'],old['nodes']);self.assertEqual(new['edges'],old['edges']);validate(new)
        new['unknown_field']=True
        with self.assertRaises(InvalidIR):validate(new)
        old['version']=False
        with self.assertRaises(InvalidIR):validate(old)
    def test_actual_fresh_archive_replay_and_tampering(self):
        from deployment.check_container_run import check
        archive=ROOT/'deployment/runs/tier3/containers-final'
        check(archive)
        with tempfile.TemporaryDirectory(prefix='cstack-r2-archive-',dir=ROOT/'.git') as tmp:
            relocated=Path(tmp)/'archive';shutil.copytree(archive,relocated);check(relocated)
            body=relocated/'crash-retry/after-crash/sink/1.body';original=body.read_bytes();body.write_bytes(b'changed sink bytes')
            with self.assertRaises(AssertionError):check(relocated)
            body.write_bytes(original)
            facts=relocated/'clean/fresh-inputs/host-observations.json';d=json.loads(facts.read_text())
            next(iter(d['images'].values()))['principal_policy']['admin']=[999]
            facts.write_text(json.dumps(d))
            with self.assertRaises(AssertionError):check(relocated)
if __name__=='__main__':unittest.main()
