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
from extractors.compose import declared_hardening,sha
from deployment.scan import capability_paths,slice_tree,slice_tree_problems,startup_hooks
from security_ir import validate,InvalidIR
from security_ir.migrate import to_v01
from security_ir.verifier import verify
from tools.check_deployment_subset_differential import configuration_accepted

def reference_tree(source_names):
    return [['slice','5',0o755,0],['slice/trusted_stack','5',0o755,0],*[[name,'0',0o644,0] for name in sorted(source_names)]]

def image_fixture(image):
    names=['slice/entry.py',*['slice/trusted_stack/'+f.name for f in (ROOT/'trusted_stack').glob('*.py')]]
    return {'status':'OBSERVED','slice_tree':sorted(reference_tree(names)),'startup_hooks':[],'image':image,'image_user':'','entrypoint':['/usr/bin/python3','/slice/entry.py'],'command':None,'setid_paths':[],'file_capability_paths':[],'mode_inventory_sha256':'0'*64,'source_sha256':{'slice/entry.py':sha(ROOT/'tools/deployment_container_entry.py'),**{'slice/trusted_stack/'+f.name:sha(f) for f in (ROOT/'trusted_stack').glob('*.py')}},'principal_policy':{'agent':[23701,23702],'reviewer':[23703],'approver':[23704],'admin':[23700]},'basis':'injected unit fixture; no actual image assessment'}

class ScannerTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory(prefix='cstack-r2-scan-test-',dir=ROOT/'.git');self.addCleanup(self.tmp.cleanup);self.base=Path(self.tmp.name)
        self.cp=self.base/'compose.json';self.rp=self.base/'runtime.json';self.out=self.base/'output'
        self.c=json.loads((ROOT/'examples/compose-two-agent-hardened/clean.compose.json').read_text());old=self.c['x-cstack']['sink_source'].rsplit('/',1)[0]
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
        self.r={'services':{name:{'uid':int(s['user']),'image':s['image'],'mounts':sorted([{k:v for k,v in m.items() if k!='bind'} for m in s['volumes']],key=lambda m:(m['source'],m['target'])),'networks':s['networks'],'env_names':sorted(s['environment']),'hardening':declared_hardening(s)} for name,s in self.c['services'].items()}}
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
    def test_agents_must_not_be_able_to_regain_capabilities(self):
        # T9.4 (review M3): no-new-privileges and cap_drop ALL are required of agents and must be observed at runtime.
        for label,edit in (('no nnp',lambda c:c['services']['agent-a'].pop('security_opt')),('no cap_drop',lambda c:c['services']['agent-b'].pop('cap_drop')),
                           ('partial cap_drop',lambda c:c['services']['agent-a'].update(cap_drop=['NET_RAW'])),('seccomp instead',lambda c:c['services']['agent-a'].update(security_opt=['seccomp=unconfined']))):
            with self.subTest(label):
                self.setUp();edit(self.c);self.refresh_runtime()
                ir=self.run_scan();self.assertFalse(configuration_accepted(ir));self.assertIn('not-established' if label in {'no nnp','no cap_drop'} else 'unknown-feature',json.dumps(ir))
        self.setUp();self.r['services']['agent-a']['hardening']['no_new_privileges']=False   # declared hardened, daemon reports otherwise
        self.assertFalse(configuration_accepted(self.run_scan()))
    def test_fresh_scan_refuses_an_inventory_that_does_not_report_hardening(self):
        for service in self.r['services'].values():service.pop('hardening')
        ir=self.run_scan();self.assertFalse(configuration_accepted(ir));self.assertIn('runtime-inventory-lacks-hardening-facts-UNKNOWN',json.dumps(ir))
    def test_file_capabilities_in_the_image_are_unknown_or_refuted(self):
        def with_caps(image):d=image_fixture(image);d['file_capability_paths']=['usr/bin/ping'];return d
        def without_inventory(image):d=image_fixture(image);del d['file_capability_paths'];return d
        ir=self.run_scan(with_caps);self.assertFalse(configuration_accepted(ir));self.assertIn('image-file-capabilities',json.dumps(ir))
        ir=self.run_scan(without_inventory);self.assertFalse(configuration_accepted(ir));self.assertIn('image-file-capability-inventory-UNKNOWN',json.dumps(ir))
    def test_the_whole_slice_tree_must_match_the_reference(self):
        # Open item 4: the image scan used to hash only the named .py files; anything else under /slice went unseen.
        base=image_fixture('x')
        def with_tree(edit):
            def observer(image):d=image_fixture(image);edit(d['slice_tree']);return d
            return observer
        cases={'stray pyc':lambda t:t.append(['slice/trusted_stack/server.pyc','0',0o644,0]),
               'extra module shadowing the stdlib':lambda t:t.append(['slice/json.py','0',0o644,0]),
               'pycache dir':lambda t:t.append(['slice/trusted_stack/__pycache__','5',0o755,0]),
               'symlink replaces a module':lambda t:t[-1].__setitem__(1,'2'),
               'writable module':lambda t:t[-1].__setitem__(2,0o666),
               'module owned by an agent UID':lambda t:t[-1].__setitem__(3,23701),
               'missing module':lambda t:t.pop()}
        for label,edit in cases.items():
            with self.subTest(label):
                self.setUp();ir=self.run_scan(with_tree(edit));self.assertFalse(configuration_accepted(ir));self.assertIn('image-slice-tree-differs-from-reference-UNKNOWN',json.dumps(ir))
        self.setUp();self.assertTrue(configuration_accepted(self.run_scan()))
        for key,reason in (('slice_tree','image-slice-tree-inventory-UNKNOWN'),('startup_hooks','image-startup-hook-inventory-UNKNOWN')):
            def without(image,key=key):d=image_fixture(image);del d[key];return d
            self.setUp();ir=self.run_scan(without);self.assertFalse(configuration_accepted(ir));self.assertIn(reason,json.dumps(ir))
        def hooked(image):d=image_fixture(image);d['startup_hooks']=['usr/lib/python3.14/site-packages/x.pth'];return d
        self.setUp();ir=self.run_scan(hooked);self.assertFalse(configuration_accepted(ir));self.assertIn('image-python-startup-hooks',json.dumps(ir))
    def test_slice_tree_and_startup_hooks_read_the_export(self):
        import io,tarfile
        buffer=io.BytesIO()
        with tarfile.open(fileobj=buffer,mode='w') as tar:
            for name,kind,mode in (('slice/',tarfile.DIRTYPE,0o755),('slice/entry.py',tarfile.REGTYPE,0o644),('./slice/trusted_stack/a.py',tarfile.REGTYPE,0o644),('usr/lib/python3/sitecustomize.py',tarfile.REGTYPE,0o644),('usr/lib/python3/x.pth',tarfile.REGTYPE,0o644),('usr/bin/python3',tarfile.REGTYPE,0o755),('slicer/x',tarfile.REGTYPE,0o644)):
                info=tarfile.TarInfo(name);info.type=kind;info.mode=mode;tar.addfile(info)
        buffer.seek(0)
        with tarfile.open(fileobj=buffer) as tar:
            members=tar.getmembers();tree=slice_tree(members)
            self.assertEqual([e[0] for e in tree],['slice','slice/entry.py','slice/trusted_stack/a.py'])   # 'slicer' is not under slice/
            self.assertEqual(startup_hooks(members),['usr/lib/python3/sitecustomize.py','usr/lib/python3/x.pth'])
        self.assertEqual(slice_tree_problems(tree,['slice/entry.py','slice/trusted_stack/a.py']),['missing slice/trusted_stack'])
    def test_plan_accepts_a_fresh_scans_own_ir_even_with_fresh_only_unknown_reasons(self):
        # Open item 6: the planner replayed under replay rules, so a fresh IR carrying fresh-only UNKNOWN reasons was rejected.
        for service in self.r['services'].values():service.pop('hardening')
        ir=self.run_scan();self.assertIn('runtime-inventory-lacks-hardening-facts-UNKNOWN',json.dumps(ir))
        ir_path=self.base/'fresh.ir.json';ir_path.write_text(json.dumps(ir));plan=self.base/'fresh.plan.json'
        p=subprocess.run([sys.executable,str(ROOT/'tools/cstack.py'),'plan',str(self.cp),'--runtime',str(self.rp),'--ir',str(ir_path),'--inputs',str(self.out),'--output',str(plan)],cwd=ROOT,capture_output=True,text=True)
        self.assertEqual(p.returncode,0,p.stderr);self.assertTrue(any('hardening' in r.get('path','') for r in json.loads(plan.read_text())['residuals']))
        # An IR that neither rule set reproduces from the same inputs is still refused.
        forged=json.loads(json.dumps(ir));forged['edges'][0]['reachability']='ABSENT' if forged['edges'][0]['reachability']!='ABSENT' else 'PRESENT'
        ir_path.write_text(json.dumps(forged));plan.unlink()
        p=subprocess.run([sys.executable,str(ROOT/'tools/cstack.py'),'plan',str(self.cp),'--runtime',str(self.rp),'--ir',str(ir_path),'--inputs',str(self.out),'--output',str(plan)],cwd=ROOT,capture_output=True,text=True)
        self.assertEqual(p.returncode,2);self.assertIn('differ',p.stderr)
    def test_capability_paths_reads_the_pax_xattr_header(self):
        import io,tarfile
        buffer=io.BytesIO()
        with tarfile.open(fileobj=buffer,mode='w',format=tarfile.PAX_FORMAT) as tar:
            for name,headers in (('usr/bin/ping',{'SCHILY.xattr.security.capability':'x'}),('usr/bin/plain',{}),('etc/other',{'SCHILY.xattr.user.comment':'x'})):
                info=tarfile.TarInfo(name);info.pax_headers=headers;tar.addfile(info)
        buffer.seek(0)
        with tarfile.open(fileobj=buffer) as tar:self.assertEqual(capability_paths(tar.getmembers()),['usr/bin/ping'])
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
