#!/usr/bin/env python3
"""Release-blocking planted-bypass and unknown/contradictory input regressions."""
import copy
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from security_ir import validate, InvalidIR
from security_ir.verifier import verify
from extractors.compose import collect, sha

class DeploymentTests(unittest.TestCase):
    def setUp(self):
        self.clean=json.loads((ROOT/'security_ir/fixtures/clean.json').read_text())
    def test_matrix(self):
        expected=json.loads((ROOT/'examples/compose-two-agent/expected.json').read_text())
        for name, exp in expected.items():
            with self.subTest(name=name):
                d=json.loads((ROOT/'security_ir/fixtures'/f'{name}.json').read_text())
                bundle=verify(d)
                self.assertEqual(bundle['verdict'],'UNASSURED')
                self.assertEqual(any(o['status'] in {'REFUTED','UNASSESSED'} and o['premise']!='Lean-contract-instances' for o in bundle['obligations']), name!='clean')
                if exp['bypass']:
                    self.assertIn(exp['bypass'],json.dumps(bundle))
    def test_deterministic_and_golden(self):
        p=Path('examples/compose-two-agent/clean.compose.json')
        r=Path('examples/compose-two-agent/clean.runtime.json')
        a=collect(p,r,sha(p)); b=collect(p,r,sha(p))
        self.assertEqual(a,b)
        # Collector absolute trusted sources are normalized only for portable golden comparison.
        for item in a['sources']+[x['provenance'] for x in a['nodes']+a['edges']]:
            if item['source'].startswith(str(ROOT)+'/'):
                item['source']=str(Path(item['source']).relative_to(ROOT))
        self.assertEqual(a,self.clean)
        self.assertTrue(all(e['authorization']=='PERMITTED' for e in a['edges'] if e['to']=='broker' and e['capability']=='call'))
    def test_deputy_has_real_file_sink_authority_and_opaque_names_are_unknown(self):
        d=json.loads((ROOT/'security_ir/fixtures/alternate-deputy-sink-credentials.json').read_text())
        f=next(n['facts'] for n in d['nodes'] if n['id']=='deputy')
        owner=next(n['facts']['uid'] for n in d['nodes'] if n['id']=='receiver')
        self.assertEqual(f['uid'],owner)
        self.assertTrue(any(e['from']=='deputy' and e['to']=='sink' and e['capability']=='write' and e['reachability']=='PRESENT' for e in d['edges']))
        self.assertTrue(any(e['from']=='deputy' and e['capability']=='credential' and e['reachability']=='UNKNOWN' and e['provenance']['kind']=='UNKNOWN' for e in d['edges']))

    def test_sensitive_bind_sources_and_credentials(self):
        p=ROOT/'examples/compose-two-agent/clean.compose.json'
        original=json.loads(p.read_text())
        sources=['/run','/var/run','/var/run/docker.sock','/run/containerd.sock','/run/podman.sock','/','/proc','/sys','/dev','/etc','/var/lib/docker','/slice/trusted_stack','/slice/entry.py','/slice',str(ROOT/'trusted_stack'),str(ROOT/'tools/deployment_container_entry.py'),str(ROOT)]
        with tempfile.TemporaryDirectory() as tmp:
            cp=Path(tmp)/'compose.json';rp=Path(tmp)/'runtime.json'
            for source in sources:
                c=copy.deepcopy(original);c['services']['agent-a']['volumes'].append({'type':'bind','source':source,'target':'/attack','read_only':True})
                cp.write_text(json.dumps(c))
                r={'services':{k:{'uid':int(v['user']),'image':v['image'],'mounts':sorted(v['volumes'],key=lambda m:(m['source'],m['target'])),'networks':v['networks'],'env_names':sorted(v['environment'])} for k,v in c['services'].items()}}
                rp.write_text(json.dumps(r));ir=collect(cp,rp,sha(cp))
                self.assertTrue(any(e['from']=='agent-a' and e['capability']=='escape' and e['reachability']=='PRESENT' for e in ir['edges']),source)
            for key in ('PASSWORD','PASS','PASSWD','AUTH','COOKIE','PRIVATE'):
                c=copy.deepcopy(original);c['services']['agent-a']['environment'][key]='dummy-never-emit';cp.write_text(json.dumps(c))
                ir=collect(cp,rp,sha(cp))
                self.assertTrue(any(e['capability']=='credential' and e['reachability']=='UNKNOWN' and key in e['reason'] for e in ir['edges']))
                self.assertNotIn('dummy-never-emit',json.dumps(ir))

    def test_missing_and_contradictory_data(self):
        for key in self.clean:
            bad=copy.deepcopy(self.clean); del bad[key]
            with self.assertRaises(InvalidIR): validate(bad)
        for section in ('nodes','edges'):
            bad=copy.deepcopy(self.clean); bad[section].append(copy.deepcopy(bad[section][0]))
            with self.assertRaises(InvalidIR): validate(bad)
        bad=copy.deepcopy(self.clean); bad['edges'][0]['provenance']['kind']='UNKNOWN'; bad['edges'][0]['reachability']='ABSENT'
        with self.assertRaises(InvalidIR): validate(bad)
        bad=copy.deepcopy(self.clean); bad['nodes'][0]['provenance']['sha256']='0'*64
        with self.assertRaises(InvalidIR): validate(bad)
    def test_unknown_and_policy_denial_never_close_paths(self):
        bad=copy.deepcopy(self.clean)
        e=copy.deepcopy(bad['edges'][0]); e.update({'from':'agent-a','to':'sink','capability':'write','authorization':'FORBIDDEN'})
        bad['edges'].append(e)
        self.assertEqual(verify(bad)['verdict'],'UNASSURED')
        e['reachability']='UNKNOWN'; e['provenance']['kind']='UNKNOWN'
        self.assertEqual(verify(bad)['verdict'],'UNASSURED')
    def test_missing_socket_mount_is_unknown_not_a_role_based_path(self):
        p=ROOT/'examples/compose-two-agent/clean.compose.json'; r=p.with_name('clean.runtime.json')
        c=json.loads(p.read_text()); c['services']['agent-a']['volumes']=[]
        with tempfile.TemporaryDirectory() as tmp:
            cp=Path(tmp)/'compose.json';cp.write_text(json.dumps(c))
            ir=collect(cp,r,sha(cp))
            channel=next(e for e in ir['edges'] if e['from']=='agent-a' and e['to']=='broker')
            self.assertEqual(channel['reachability'],'UNKNOWN')
            self.assertEqual(channel['provenance']['kind'],'UNKNOWN')
            self.assertEqual(verify(ir)['verdict'],'UNASSURED')

    def test_runtime_types_do_not_coerce_into_observed_identity(self):
        p=ROOT/'examples/compose-two-agent/clean.compose.json'
        r=json.loads(p.with_name('clean.runtime.json').read_text())
        r['services']['agent-a']['uid']=23701.0
        with tempfile.TemporaryDirectory() as tmp:
            rp=Path(tmp)/'runtime.json';rp.write_text(json.dumps(r))
            ir=collect(p,rp,sha(p))
            self.assertEqual(next(n['facts']['runtime_match'] for n in ir['nodes'] if n['id']=='agent-a'),'DRIFT')

    def test_source_conflict_and_missing_runtime(self):
        bad=copy.deepcopy(self.clean)
        bad['sources'].append(dict(bad['sources'][0],sha256='0'*64))
        with self.assertRaises(InvalidIR): validate(bad)
        bad=copy.deepcopy(self.clean)
        bad['nodes'][3]['facts']['runtime_match']='MISSING'
        self.assertEqual(verify(bad)['verdict'],'UNASSURED')

    def test_mount_ancestor_and_unsupported_network(self):
        p=ROOT/'examples/compose-two-agent/clean.compose.json'; r=p.with_name('clean.runtime.json')
        c=json.loads(p.read_text())
        c['services']['agent-a']['volumes']=[{'type':'bind','source':str(Path(c['x-cstack']['sink_source']).parent),'target':'/all','read_only':False}]
        with tempfile.TemporaryDirectory() as tmp:
            cp=Path(tmp)/'compose.json';cp.write_text(json.dumps(c))
            ir=collect(cp,r,sha(cp))
            self.assertEqual(verify(ir)['verdict'],'UNASSURED')
            self.assertEqual({e['to'] for e in ir['edges'] if e['from']=='agent-a' and e['capability']=='write'},{'sink','database'})
            c['services']['agent-a']['network_mode']='service:receiver';cp.write_text(json.dumps(c))
            ir=collect(cp,r,sha(cp))
            self.assertTrue(any(e['reachability']=='UNKNOWN' for e in ir['edges']))

    def test_transitive_deputy_path(self):
        bad=copy.deepcopy(self.clean)
        e=copy.deepcopy(bad['edges'][0]); e.update({'from':'agent-a','to':'sink','capability':'call','authorization':'FORBIDDEN'})
        bad['edges'].append(e)
        self.assertEqual(verify(bad)['verdict'],'UNASSURED')
    def test_cli_and_exit_codes(self):
        with tempfile.TemporaryDirectory() as tmp:
            out=Path(tmp)
            def call(*args): return subprocess.run([sys.executable,str(ROOT/'tools/cstack.py'),*map(str,args)],cwd=ROOT,capture_output=True,text=True)
            p=ROOT/'examples/compose-two-agent/clean.compose.json'; r=p.with_name('clean.runtime.json')
            self.assertEqual(call('scan',p,'--runtime',r,'--sha256',sha(p),'--output',out/'ir.json').returncode,0)
            self.assertEqual(call('scan',p,'--runtime',r,'--sha256','0'*64,'--output',out/'bad.json').returncode,2)
            self.assertEqual(call('verify',out/'ir.json','--output',out/'bundle.json').returncode,1)
            self.assertEqual(call('report',out/'bundle.json','--output',out/'report.md').returncode,0)
            self.assertIn('UNASSURED',(out/'report.md').read_text())
            self.assertIn('strict subset',(out/'report.md').read_text())
            self.assertEqual(call('verify',ROOT/'security_ir/fixtures/writable-sink-mount.json','--output',out/'bad.json').returncode,1)
    def test_runtime_drift_and_env_value_redaction(self):
        p=ROOT/'examples/compose-two-agent/clean.compose.json'; r=p.with_name('clean.runtime.json')
        c=json.loads(p.read_text()); c['services']['agent-a']['environment']={'HARMLESS_NAME':'secret-value-never-emit'}
        with tempfile.TemporaryDirectory() as tmp:
            cp=Path(tmp)/'compose.json'; cp.write_text(json.dumps(c))
            ir=collect(cp,r,sha(cp))
            self.assertNotIn('secret-value-never-emit',json.dumps(ir))
            self.assertEqual(verify(ir)['verdict'],'UNASSURED')
if __name__=='__main__': unittest.main()
