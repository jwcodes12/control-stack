#!/usr/bin/env python3
"""Build an offline disposable runtime guest from already installed local assets.
Run as root for owner metadata. No host settings, accounts or network are changed.
"""
import argparse,os,re,shutil,subprocess
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('--workdir',required=True,type=Path);ap.add_argument('--rootfs',required=True,type=Path);a=ap.parse_args()
base=a.workdir; base.mkdir(exist_ok=False)
r=base/'root'; shutil.copytree(a.rootfs,r,symlinks=True)
for p in [r/'usr/lib64',r/'lib64',r/'slice',r/'proc',r/'sys',r/'dev',r/'tmp']:
 p.mkdir(parents=True,exist_ok=True)
# Copy the installed glibc Python runtime and every ELF dependency. No downloads.
shutil.copytree('/usr/lib64/python3.9',r/'usr/lib64/python3.9',ignore=shutil.ignore_patterns('site-packages','__pycache__'))
shutil.copy2('/usr/bin/python3',r/'usr/bin/python3-host')
# /usr/bin/python3 inside the guest must refer to the copied host interpreter.
(r/'usr/bin/python3').unlink(); shutil.copy2('/usr/bin/python3',r/'usr/bin/python3')
files=[Path('/usr/bin/python3'),Path('/usr/lib64/libseccomp.so.2')]+list(Path('/usr/lib64/python3.9/lib-dynload').glob('*.so'))
seen=set()
while files:
 p=files.pop()
 if str(p) in seen:continue
 seen.add(str(p)); target=r/str(p).lstrip('/');target.parent.mkdir(parents=True,exist_ok=True)
 if target.exists() or target.is_symlink():target.unlink()
 shutil.copy2(p,target,follow_symlinks=True)
 out=subprocess.run(['ldd',str(p)],capture_output=True,text=True).stdout
 for q in re.findall(r'(?:=>\s+|^\s*)(/[^\s]+)',out,re.M):
  if Path(q).is_file() and q not in seen:files.append(Path(q))
repo=Path(__file__).resolve().parents[1]
for name in ['trusted_stack','tools']:
 shutil.copytree(repo/name,r/'slice'/name,ignore=shutil.ignore_patterns('__pycache__'))
(r/'init').write_text('''#!/bin/sh
/bin/mount -t proc proc /proc
/bin/mount -t sysfs sysfs /sys
/bin/mount -t devtmpfs devtmpfs /dev
/bin/mkdir -p /sys/kernel/security
/bin/mount -t securityfs securityfs /sys/kernel/security
/bin/chmod 1777 /tmp
export PATH=/usr/bin:/bin:/usr/sbin:/sbin
cd /slice
cat /sys/kernel/security/lsm
/usr/bin/python3 tools/run_deployment_boundary.py --output /tmp/slice-runtime
rc=$?
echo SOL_VM_RC=$rc
if [ "$rc" = 0 ]; then
 echo SOL_EVIDENCE_BEGIN
 tar -C /tmp -czf - slice-runtime | base64
 echo SOL_EVIDENCE_END
fi
/sbin/poweroff -f
''');(r/'init').chmod(0o755)
# Root-owned immutable library files are required by launcher trust checks.
for p in [r,*r.rglob('*')]:
 if not p.is_symlink():os.chown(p,0,0)
with (base/'initramfs.gz').open('wb') as out:
 p=subprocess.Popen(['find','.','-print0'],cwd=r,stdout=subprocess.PIPE)
 c=subprocess.Popen(['cpio','--null','-o','--format=newc'],cwd=r,stdin=p.stdout,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 g=subprocess.run(['gzip','-1'],stdin=c.stdout,stdout=out);p.wait();c.wait();assert g.returncode==0
print(base/'initramfs.gz')
