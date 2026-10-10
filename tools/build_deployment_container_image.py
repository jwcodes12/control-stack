#!/usr/bin/env python3
"""Import an existing offline rootfs, with pinned experiment code baked in.
Does not download, build with the network, or touch preexisting Docker images.
"""
import argparse
import hashlib
import json
import subprocess
import tarfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
ap=argparse.ArgumentParser(); ap.add_argument('--rootfs',type=Path,default=Path('/var/tmp/sc01-vm-assets/build-root')); ap.add_argument('--output',type=Path,required=True); a=ap.parse_args()
a.output.mkdir(parents=True,exist_ok=True)
archive=a.output/'rootfs.tar'
# sudo tar preserves rootfs paths/permissions; trusted code is added as immutable image content.
subprocess.run(['sudo','-n','tar','--exclude=./boot','--exclude=./dev','--exclude=./proc','--exclude=./sys','--exclude=./root','-C',str(a.rootfs),'-cf',str(archive),'.'],check=True)
subprocess.run(['sudo','-n','chown',str(__import__('os').getuid()),str(archive)],check=True)
with tarfile.open(archive,'a') as tar:
    tar.add(ROOT/'trusted_stack',arcname='slice/trusted_stack',filter=lambda info: None if '__pycache__' in info.name else info)
    tar.add(ROOT/'tools/deployment_container_entry.py',arcname='slice/entry.py')
cmd=['docker','import','--change','WORKDIR /slice','--change','ENV PYTHONPATH=/slice','--change','ENTRYPOINT ["/usr/bin/python3", "/slice/entry.py"]',str(archive)]
p=subprocess.run(cmd,check=True,capture_output=True,text=True)
manifest={'host_root':str(ROOT/'deployment-container-state'),'image':p.stdout.strip(),'rootfs_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'source_sha256':{str(f.relative_to(ROOT)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted((ROOT/'trusted_stack').glob('*.py'))},'entry_sha256':hashlib.sha256((ROOT/'tools/deployment_container_entry.py').read_bytes()).hexdigest(),'offline':True}
(a.output/'image-pin.json').write_text(json.dumps(manifest,sort_keys=True,indent=2)+'\n')
print(manifest['image'])
