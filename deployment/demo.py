"""One-command R2 story: fixture verify + Lean, plan, live remediated containers, independent check, report.
Defensive scope: the live stage launches only the two repaired clean configurations with honest work.
Bypass outcomes are archived Tier 2 evidence, never rerun. A skipped stage is reported SKIPPED and never counts as PASS.
"""
import json
import shutil
import subprocess
import sys
import time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
EXAMPLES=ROOT/'examples/compose-two-agent'
ROOTFS=Path('/var/tmp/sc01-vm-assets/build-root')
TAG='cstack-r2-demo:offline'
REPAIRED=('writable-sink-mount','trusted-role-uid-collision')
# Exit codes: 0 every stage PASS; 1 a stage FAILED; 3 no failure but at least one stage SKIPPED (never a pass).
EXIT={'PASS':0,'FAIL':1,'SKIPPED':3}

def dump(path,value):Path(path).write_text(json.dumps(value,sort_keys=True,indent=2)+'\n')

def fixtures(out):
    from security_ir.verifier import verify,report
    from deployment.kernel import check_many
    expected=json.loads((EXAMPLES/'expected.json').read_text());names=sorted(expected)
    irs=[json.loads((ROOT/'security_ir/fixtures'/(n+'.json')).read_text()) for n in names]
    accepted,axioms=check_many(irs);rows=[];bad=[]
    for name,ir,lean in zip(names,irs,accepted):
        bundle=verify(ir)
        for o in bundle['obligations']:
            if o['premise']=='Lean-contract-instances':o.update(status='PROVEN_IN_MODEL' if lean else 'REFUTED',detail=axioms)
        bundle['verdict']='UNASSURED' if any(o['status'] in {'REFUTED','UNASSESSED'} for o in bundle['obligations']) else 'CONDITIONAL'
        exp=expected[name];named=exp['bypass'] is None or exp['bypass'] in json.dumps(bundle)
        ok=bundle['verdict']==exp['verdict'] and lean==exp['lean_accepted'] and named
        rows.append({'fixture':name,'expected':exp['verdict'],'actual':bundle['verdict'],'lean_accepted':lean,'bypass_named':named,'ok':ok})
        if not ok:bad.append(name)
        if name=='clean' or name in REPAIRED:
            dump(out/(name+'.bundle.json'),bundle);(out/(name+'.report.md')).write_text(report(bundle))
    dump(out/'fixtures.json',{'rows':rows,'axioms':axioms})
    false_conditional=[r['fixture'] for r in rows if r['actual']=='CONDITIONAL' and r['expected']!='CONDITIONAL']
    detail=f"{len(rows)-len(bad)}/{len(rows)} fixtures match expected verdict and kernel result; false CONDITIONAL: {false_conditional or 'none'}"
    return ('FAIL' if bad else 'PASS'),detail

def plans(out):
    from extractors.compose import collect,sha
    from deployment.plan import build_plan,apply_patch
    clean=json.loads((EXAMPLES/'clean.compose.json').read_text());done=[]
    for case in REPAIRED:
        c=EXAMPLES/(case+'.compose.json');r=EXAMPLES/(case+'.runtime.json')
        plan=build_plan(json.loads(c.read_text()),json.loads(r.read_text()),collect(c,r,sha(c)),sha(c))
        dump(out/(case+'.plan.json'),plan)
        if apply_patch(json.loads(c.read_text()),plan['patch'])!=clean:return 'FAIL',case+': patch does not yield the reference clean profile'
        done.append(case)
    return 'PASS','read-only JSON Patch for '+', '.join(done)+' yields the reference clean profile'

def live_prerequisites():
    missing=[]
    if shutil.which('docker') is None or subprocess.run(['docker','info'],capture_output=True).returncode:missing.append('Docker daemon unavailable')
    if subprocess.run(['sudo','-n','true'],capture_output=True).returncode:missing.append('passwordless sudo unavailable (state directory ownership)')
    if not ROOTFS.is_dir():missing.append('offline rootfs '+str(ROOTFS)+' absent')
    if (ROOT/'deployment-container-state').exists():missing.append('deployment-container-state already exists; refusing to reuse')
    if not missing:
        leftovers=subprocess.run(['docker','ps','-a','--filter','name=cstack-r2-','--format','{{.Names}}'],capture_output=True,text=True).stdout.strip()
        leftovers+=subprocess.run(['docker','image','ls','--filter','reference=cstack-r2-*','--format','{{.Repository}}:{{.Tag}}'],capture_output=True,text=True).stdout.strip()
        if leftovers:missing.append('existing cstack-r2- resources: '+leftovers.replace('\n',' '))
    return missing

def live(out):
    build=out/'build';subprocess.run([sys.executable,str(ROOT/'tools/build_deployment_container_image.py'),'--output',str(build),'--tag',TAG],cwd=ROOT,check=True,capture_output=True,text=True)
    (build/'rootfs.tar').unlink()  # hash retained in image-pin.json
    pin=json.loads((build/'image-pin.json').read_text())
    try:
        p=subprocess.run([sys.executable,str(ROOT/'deployment/run_remediated.py'),'--output',str(out/'remediated'),'--pin',str(build/'image-pin.json')],cwd=ROOT,capture_output=True,text=True,timeout=900)
    finally:
        subprocess.run(['docker','image','rm',pin['image']],capture_output=True)
    (out/'remediated-stdout.txt').write_text(p.stdout+p.stderr)
    if p.returncode:return 'FAIL','run_remediated exit '+str(p.returncode)+'; see remediated-stdout.txt'
    result=json.loads((out/'remediated/result.json').read_text())
    return 'PASS','fresh daemon capture, fresh scan and kernel CONDITIONAL for '+', '.join(sorted(result['cases']))+'; '+str(sum(c['honest_agents_completed'] for c in result['cases'].values()))+' honest deliveries; own resources removed'

def independent(out):
    p=subprocess.run([sys.executable,str(ROOT/'deployment/check_remediated.py'),str(out/'remediated')],cwd=ROOT,capture_output=True,text=True)
    (out/'independent-check.txt').write_text(p.stdout+p.stderr)
    return ('PASS' if p.returncode==0 else 'FAIL'),(p.stdout.strip().splitlines() or ['no output'])[-1]

def render(summary):
    lines=['# cstack demo','','**'+summary['result']+'**  (exit '+str(summary['exit'])+')','',summary['scope'],'','| Stage | Status | Detail |','|---|---|---|']
    lines+=['| '+s['stage']+' | '+s['status']+' | '+s['detail'].replace('|','\\|')+' |' for s in summary['stages']]
    lines+=['','Claim ladder: fixture verdicts and Lean acceptance are PROVEN_IN_MODEL for the extracted IR only; the live stage is TESTED_BOUNDARY on this host (Docker default seccomp/namespaces, no Landlock, daemon-reported inventory, not independent attestation); faithful extraction and protocol refinement remain ASSUMED; bypass outcomes are archived Tier 2 measurements.']
    return '\n'.join(lines)+'\n'

def run(output,static_only=False):
    out=Path(output).resolve();out.mkdir(parents=True,exist_ok=False);stages=[]
    def stage(name,fn,*args):
        start=time.monotonic()
        try:status,detail=fn(*args)
        except Exception as err:status,detail='FAIL',type(err).__name__+': '+str(err)[:500]
        stages.append({'stage':name,'status':status,'detail':detail,'seconds':round(time.monotonic()-start,1)});return status
    stage('verify fixtures + Lean kernel',fixtures,out)
    stage('plan remediation',plans,out)
    missing=['--static-only requested'] if static_only else live_prerequisites()
    if missing:
        for name in ('live remediated containers','independent sink-side check'):stages.append({'stage':name,'status':'SKIPPED','detail':'; '.join(missing),'seconds':0})
    elif stage('live remediated containers',live,out)=='PASS':stage('independent sink-side check',independent,out)
    else:stages.append({'stage':'independent sink-side check','status':'SKIPPED','detail':'live stage failed','seconds':0})
    statuses={s['status'] for s in stages};result='FAIL' if 'FAIL' in statuses else 'SKIPPED' if 'SKIPPED' in statuses else 'PASS'
    summary={'result':result,'exit':EXIT[result],'stages':stages,'scope':'Scoped R2 local-file two-agent slice. Verdicts never exceed CONDITIONAL; SKIPPED stages are not passes; no bypass is rerun live (defensive scope).'}
    dump(out/'demo.json',summary);(out/'DEMO.md').write_text(render(summary))
    print(render(summary),end='')
    return summary['exit']

if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--output',required=True);p.add_argument('--static-only',action='store_true');a=p.parse_args();sys.exit(run(a.output,a.static_only))
