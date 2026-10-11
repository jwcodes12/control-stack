"""Versioned trusted-source pins (T9.1).
Archived evidence records the SHA-256 of the trusted source it ran. Those hashes must stay checkable after
trusted_stack changes, so each generation of the pinned files is kept under deployment/pinned-sources/<gen>/
(append-only; one file per repo path, suffix .pysrc so no test runner collects it). A recorded digest is accepted
for a repo path when the current tree matches it, or when some vaulted generation holds a file for that path
whose own SHA-256 equals the digest. The vault is never trusted by name: only its bytes' hash counts.
A fresh scan or live run still requires the CURRENT tree (see current_sources), never a vaulted generation.
"""
import argparse
import hashlib
import shutil
import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
VAULT=ROOT/'deployment/pinned-sources'
ENTRY='tools/deployment_container_entry.py'
BOUNDARY=('tools/run_deployment_boundary.py','tools/test_confined_effect_broker.py')

def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def tracked():
    """Every repo-relative path whose digest any archive may pin."""
    return sorted([str(f.relative_to(ROOT)) for f in (ROOT/'trusted_stack').glob('*.py')]+[ENTRY,*BOUNDARY])

def image_path_to_repo(name):
    """In-image path -> repo path (slice/entry.py and slice/trusted_stack/x.py)."""
    if name=='slice/entry.py':return ENTRY
    if name.startswith('slice/trusted_stack/'):return name.removeprefix('slice/')
    return name

def current_sources():
    """What a fresh image must contain, keyed by in-image path."""
    return {'slice/entry.py':sha(ROOT/ENTRY),**{'slice/trusted_stack/'+f.name:sha(f) for f in (ROOT/'trusted_stack').glob('*.py')}}

def generations():return sorted(p for p in VAULT.iterdir() if p.is_dir()) if VAULT.is_dir() else []

def vaulted_file(rel,digest):
    """The vaulted file for repo path rel whose bytes hash to digest, else None."""
    for gen in generations():
        f=gen/(rel+'.pysrc')
        if f.is_file() and sha(f)==digest:return f
    return None

def source_matches(rel,digest):
    """Archived digest for repo path rel is the current file or a vaulted generation of it."""
    current=ROOT/rel
    return (current.is_file() and sha(current)==digest) or vaulted_file(rel,digest) is not None

def require(rel,digest,what='trusted source drift'):
    assert source_matches(rel,digest),(what,rel)

def generation_sources(gen):
    """The in-image source map a vaulted generation represents (hashes of the vaulted bytes)."""
    out={}
    for f in sorted(Path(gen).rglob('*.pysrc')):
        rel=str(f.relative_to(gen))[:-len('.pysrc')]
        if rel==ENTRY:out['slice/entry.py']=sha(f)
        elif rel.startswith('trusted_stack/'):out['slice/'+rel]=sha(f)
    return out

def known_generation(recorded):
    """The vaulted generation whose in-image source map equals recorded exactly, else None."""
    return next((g for g in generations() if recorded and generation_sources(g)==recorded),None)

def snapshot(gen):
    """Copy every tracked file into a NEW complete generation. Refuses to overwrite, or to add an unchanged one."""
    dest=VAULT/gen
    if dest.exists():raise SystemExit('pins: generation exists; the vault is append-only: '+gen)
    if known_generation(current_sources()):raise SystemExit('pins: the current tree already equals a vaulted generation')
    for rel in tracked():
        out=dest/(rel+'.pysrc');out.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/rel,out)
    return sum(1 for _ in dest.rglob('*.pysrc'))

def main(argv=None):
    p=argparse.ArgumentParser(description=__doc__.splitlines()[0]);sub=p.add_subparsers(dest='command',required=True)
    s=sub.add_parser('snapshot',help='vault the current tracked files as a new complete generation');s.add_argument('generation')
    sub.add_parser('list',help='list generations and whether the current tree is vaulted')
    a=p.parse_args(argv)
    if a.command=='snapshot':print('vaulted',snapshot(a.generation),'files in',a.generation);return 0
    for g in generations():print(g.name,sum(1 for _ in g.rglob('*.pysrc')),'files')
    print('current tree equals a vaulted generation:',known_generation(current_sources()) is not None);return 0
if __name__=='__main__':sys.exit(main())
