"""Versioned trusted-source pins (T9.1).
Archived evidence records the SHA-256 of the trusted source it ran. Those hashes must stay checkable after
trusted_stack changes, so each generation of the pinned files is kept under deployment/pinned-sources/<gen>/
(append-only; one file per repo path, suffix .pysrc so no test runner collects it). A recorded digest is accepted
for a repo path when the current tree matches it, or when some vaulted generation holds a file for that path
whose own SHA-256 equals the digest. A recorded digest is only ever compared with the hash of vaulted BYTES, never with a file name; but the vault itself is part of the
trusted computing base (anything placed in it becomes acceptable on replay) and must be reviewed with the code.
A fresh scan or live run still requires the CURRENT tree (see current_sources), never a vaulted generation.
"""
import argparse
import hashlib
import json
import shutil
import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
VAULT=ROOT/'deployment/pinned-sources'
ENTRY='tools/deployment_container_entry.py'
BOUNDARY=('tools/run_deployment_boundary.py','tools/test_confined_effect_broker.py')

TEMPLATES=ROOT/'deployment/pinned-templates'
TEMPLATE_DIR=ROOT/'examples/compose-two-agent-hardened'
TEMPLATE_NAMES=('clean','writable-sink-mount','trusted-role-uid-collision')

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

class PinMismatch(AssertionError):
    """An archive's recorded source digests do not belong to one source generation."""

def require(rel,digest,what='trusted source drift'):
    if not source_matches(rel,digest):raise PinMismatch((what,rel))

def require_generation(recorded,*,entry_sha256=None,complete=True,what='trusted source drift'):
    """The recorded digests (repo paths such as trusted_stack/x.py, or in-image slice/ paths) must all come from ONE source
    generation: the current tree or a single vaulted generation. Checking each file against any generation separately would accept
    a mixture no deployment ever ran. complete=False accepts a recorded subset (the pre-vault legacy pin); a complete record must
    equal the generation's full file set. Returns the generation name ('current' for the live tree)."""
    image={}
    for rel,digest in recorded.items():
        key=rel if rel.startswith('slice/') else 'slice/'+rel if rel.startswith('trusted_stack/') else rel
        image[key]=digest
    if entry_sha256 is not None:image['slice/entry.py']=entry_sha256
    candidates=[('current',current_sources()),*((g.name,generation_sources(g)) for g in generations())]
    for name,files in candidates:
        if image and all(files.get(k)==v for k,v in image.items()) and (not complete or set(image)==set(files)):return name
    raise PinMismatch((what,'digests do not all belong to one source generation'))

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

def vault_templates():
    """Content-address the current hardened reference templates (they embed the trusted-source pins, so they change with every
    source generation). Archived remediation runs record only the digest of the template their plan was based on; without these
    copies an archive could not be checked after the next source change. Idempotent; never overwrites."""
    TEMPLATES.mkdir(parents=True,exist_ok=True);index=TEMPLATES/'index.json';table=json.loads(index.read_text()) if index.is_file() else {}
    for name in TEMPLATE_NAMES:
        f=TEMPLATE_DIR/(name+'.compose.json');digest=sha(f);target=TEMPLATES/(digest+'.json')
        if not target.exists():shutil.copyfile(f,target)
        if table.setdefault(digest,name)!=name:raise SystemExit('pins: one digest recorded under two template names')
    index.write_text(json.dumps(table,sort_keys=True,indent=2)+'\n');return len(table)

def vaulted_templates(name):
    """Every hardened reference template of this name that exists: the current file and each vaulted copy whose bytes still hash to
    the digest it is filed under. Returns {digest: Path}."""
    found={}
    current=TEMPLATE_DIR/(name+'.compose.json')
    if current.is_file():found[sha(current)]=current
    index=TEMPLATES/'index.json'
    if index.is_file():
        for digest,label in json.loads(index.read_text()).items():
            f=TEMPLATES/(digest+'.json')
            if label==name and f.is_file() and sha(f)==digest:found[digest]=f
    return found

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
    sub.add_parser('vault-templates',help='content-address the current hardened reference templates (run after regenerating fixtures)')
    sub.add_parser('list',help='list generations and whether the current tree is vaulted')
    a=p.parse_args(argv)
    if a.command=='snapshot':print('vaulted',snapshot(a.generation),'files in',a.generation);return 0
    if a.command=='vault-templates':print('template vault holds',vault_templates(),'digests');return 0
    for g in generations():print(g.name,sum(1 for _ in g.rglob('*.pysrc')),'files')
    print('current tree equals a vaulted generation:',known_generation(current_sources()) is not None);return 0
if __name__=='__main__':sys.exit(main())
