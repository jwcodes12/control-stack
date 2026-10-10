#!/usr/bin/env python3
"""Independent observer check of archived raw sink bytes and current source pins."""
import hashlib
import json
import sqlite3
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def check(base):
    base=Path(base)
    result=json.loads((base/'result.json').read_text())
    for path,pin in result['source_sha256'].items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==pin,(path,'source drift')
    snapshots={}
    for label in ['clean-inflight','clean-after-halt','writable-sink-mount','trusted-role-uid-collision']:
        observed=json.loads((base/(label+'-sink.json')).read_text())
        for name,f in observed.items():
            assert Path(name).name==name
            raw=(base/'sink'/name).read_bytes()
            assert hashlib.sha256(raw).hexdigest()==f['sha256'] and len(raw)==f['size']
        snapshots[label]=observed
    assert list(snapshots['clean-inflight'])==['1.body']
    assert snapshots['clean-inflight']==snapshots['clean-after-halt']
    assert (base/'sink/1.body').read_bytes()==b'exact-reviewed-two-agent-slice'
    assert (base/'sink/writable-mutation.body').read_bytes()==b'unapproved writable sink mutation'
    assert (base/'sink/uid-collision.body').read_bytes()==b'unapproved UID collision mutation'
    assert 'confined-mutation.body' not in snapshots['writable-sink-mount']
    assert result['cases']['clean']['halt_client_ready_before_receiver_release']
    assert (base/'halt-ready.marker').read_text() == 'HALT client ready before request'
    assert result['cases']['clean']['halt_during_inflight'].startswith('HALT waited')
    assert result['cases']['writable-sink-mount']['confined_write_denied']
    assert result['cases']['trusted-role-uid-collision']['launcher_same_uid_rejected']
    # This state supplements sink evidence; no gate log substitutes for raw files.
    db=sqlite3.connect('file:'+str((base/'private/gate.db').resolve())+'?mode=ro',uri=True)
    try: assert db.execute('SELECT spent,halted FROM meta WHERE id=1').fetchone()==(1,1)
    finally: db.close()
    return snapshots
if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('base',type=Path);a=ap.parse_args();check(a.base);print('PASS: archived independent sink bytes, shared budget/HALT and source pins')
