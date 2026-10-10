"""Batch finite-IR evaluation followed by a kernel proof for every result."""
import re
import subprocess
import tempfile
from pathlib import Path
from tools.check_deployment_lean import projection, ROOT

def check_many(irs):
    subprocess.run(['lake','build','ControlStack.Deployment.Contracts'],cwd=ROOT,check=True,capture_output=True)
    header='import ControlStack.Deployment.Contracts\nopen ControlStack.Deployment\nset_option maxRecDepth 10000\nset_option maxHeartbeats 40000000\n'
    definitions=''.join(f'def instance_{i} : IR := {projection(ir)}\n' for i,ir in enumerate(irs))
    names=','.join(f'instance_{i}' for i in range(len(irs)))
    evaluation='#eval IO.println (String.intercalate "," ((['+names+'] : List IR).map (fun d => toString (decide (Accepted d)))))\n'
    with tempfile.TemporaryDirectory(prefix='cstack-r2-kernel-',dir=ROOT/'.git') as tmp:
        path=Path(tmp)/'Instances.lean';path.write_text(header+definitions+evaluation)
        p=subprocess.run(['lake','env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
        if p.returncode:raise ValueError(p.stdout+p.stderr)
        values=p.stdout.strip().split(',')
        assert len(values)==len(irs) and set(values)<={'true','false'},p.stdout
        accepted=[v=='true' for v in values]
        certificates=''.join(f'theorem certificate_{i} : {"" if ok else "¬ "}Accepted instance_{i} := by decide\n#print axioms certificate_{i}\n' for i,ok in enumerate(accepted))
        path.write_text(header+definitions+certificates)
        p=subprocess.run(['lake','env','lean',str(path)],cwd=ROOT,capture_output=True,text=True)
        if p.returncode:raise ValueError(p.stdout+p.stderr)
        groups=re.findall(r'depends on axioms: \[([^\]]*)\]',p.stdout)
        count=len(groups)+len(re.findall('does not depend on any axioms',p.stdout))
        assert count==len(irs) and 'sorryAx' not in p.stdout
        assert all({x.strip() for x in g.split(',') if x.strip()}<={'propext','Quot.sound','Classical.choice'} for g in groups)
        return accepted, p.stdout
