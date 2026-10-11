#!/usr/bin/env python3
"""T9.1 versioned trusted-source pins: archives stay checkable across trusted_stack changes; fresh work needs the current tree."""
import json
import shutil
import sys
import tempfile
import unittest
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from deployment import pins
from extractors.compose import collect,sha
EXAMPLES=ROOT/'examples/compose-two-agent'

class PinTests(unittest.TestCase):
    def setUp(self):
        self.tmp=Path(tempfile.mkdtemp());self.addCleanup(shutil.rmtree,self.tmp,True)
        self.vault=pins.VAULT;self.addCleanup(setattr,pins,'VAULT',self.vault)
    def fake_generation(self):
        """A vault holding one historical-looking controller that differs from the current one."""
        pins.VAULT=self.tmp/'vault';dest=pins.VAULT/'old'/'trusted_stack';dest.mkdir(parents=True)
        old=(ROOT/'trusted_stack/controller.py').read_bytes()+b'\n# an earlier generation\n';(dest/'controller.py.pysrc').write_bytes(old)
        return pins.sha(dest/'controller.py.pysrc')
    def pinned_example(self,digest):
        c=json.loads((EXAMPLES/'clean.compose.json').read_text());c['x-cstack']['broker_sha256']=digest
        path=self.tmp/'compose.json';path.write_text(json.dumps(c));return path
    def unknown_drift(self,ir):return any('hash drift' in e.get('reason','') for e in ir['edges'])

    def test_every_archived_pin_is_satisfied(self):
        checked=0
        for f in sorted((ROOT/'deployment').rglob('*.json')):
            if 'pinned-sources' in f.parts:continue
            try:document=json.loads(f.read_text())
            except ValueError:continue
            stack=[document]
            while stack:
                item=stack.pop()
                if isinstance(item,dict):
                    sources=item.get('source_sha256')
                    if isinstance(sources,dict):
                        for path,digest in sources.items():
                            if path.startswith(('trusted_stack/','tools/')):
                                with self.subTest(file=str(f.relative_to(ROOT)),path=path):self.assertTrue(pins.source_matches(path,digest));checked+=1
                    stack.extend(item.values())
                elif isinstance(item,list):stack.extend(item)
        self.assertGreater(checked,300)

    def test_vault_is_complete_and_current_tree_is_vaulted(self):
        gens=pins.generations();self.assertTrue(gens)
        for g in gens:
            names={str(f.relative_to(g))[:-len('.pysrc')] for f in g.rglob('*.pysrc')}
            self.assertTrue({'tools/deployment_container_entry.py','trusted_stack/controller.py','trusted_stack/server.py','trusted_stack/outbox_receiver.py'}<=names,g.name)
        self.assertIsNotNone(pins.known_generation(pins.current_sources()),'trusted source changed: run `python3 deployment/pins.py snapshot <name>` and regenerate fixtures (see docs/DEPLOYMENT-QUICKSTART.md)')

    def test_digest_must_match_the_path_and_bytes(self):
        digest=self.fake_generation()
        self.assertTrue(pins.source_matches('trusted_stack/controller.py',digest))
        self.assertFalse(pins.source_matches('trusted_stack/server.py',digest),'a digest vaulted for one path must not satisfy another')
        self.assertFalse(pins.source_matches('trusted_stack/controller.py','0'*64))
        (pins.VAULT/'old/trusted_stack/controller.py.pysrc').write_bytes(b'tampered')
        self.assertFalse(pins.source_matches('trusted_stack/controller.py',digest),'vault bytes are checked by hash, not trusted by name')

    def test_replay_accepts_a_vaulted_generation_but_fresh_collection_does_not(self):
        digest=self.fake_generation();compose=self.pinned_example(digest);runtime=EXAMPLES/'clean.runtime.json'
        replayed=collect(compose,runtime,sha(compose),replay=True);fresh=collect(compose,runtime,sha(compose))
        self.assertFalse(self.unknown_drift(replayed));self.assertEqual(replayed['snapshot']['broker_sha256'],digest)
        self.assertTrue(self.unknown_drift(fresh),'a fresh scan must require the current trusted source')
        stale=self.pinned_example('1'*64)
        self.assertTrue(self.unknown_drift(collect(stale,runtime,sha(stale),replay=True)),'an unvaulted digest is drift even in replay')

    def test_image_source_replay_needs_an_exact_vaulted_generation(self):
        current=pins.current_sources();self.assertIsNotNone(pins.known_generation(current))
        self.assertIsNone(pins.known_generation({}))
        self.assertIsNone(pins.known_generation({k:v for k,v in current.items() if k!='slice/entry.py'}),'a missing file is not a generation')
        self.assertIsNone(pins.known_generation({**current,'slice/trusted_stack/extra.py':'2'*64}))

    def test_snapshot_is_append_only(self):
        pins.VAULT=self.tmp/'vault';shutil.copytree(self.vault,pins.VAULT)  # never touch the real vault
        first=pins.generations()[0].name
        with self.assertRaises(SystemExit):pins.snapshot(first)
        if pins.known_generation(pins.current_sources()):
            with self.assertRaises(SystemExit):pins.snapshot('unchanged-copy')
        else:
            pins.snapshot('next');self.assertIsNotNone(pins.known_generation(pins.current_sources()))
            with self.assertRaises(SystemExit):pins.snapshot('again')
        self.assertFalse((self.vault/'unchanged-copy').exists() or (self.vault/'next').exists())

if __name__=='__main__':
    unittest.main()
