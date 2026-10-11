#!/usr/bin/env python3
"""Kernel-check every prospective static plan; declaration hypotheses only."""
if not __debug__:raise SystemExit('cstack evidence checkers state their checks as assert; refusing to run under python -O')
import argparse
import json
import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools.test_deployment_plan import matrix
from deployment.kernel import check_many
if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output');a=parser.parse_args()
    rows,irs=matrix();accepted,axioms=check_many(irs)
    assert accepted==[r['prospective_model_accepted'] for r in rows]
    result={'basis':'Synthetic DECLARED prospective selected facts, not runtime evidence; plans retain required host/capture residuals.','fixtures':len(rows),'model_accepted':sum(accepted),'exact_residual_cases':len(rows)-sum(accepted),'rows':rows,'axioms':axioms}
    if a.output:Path(a.output).write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    print('PASS:',len(rows),'prospective kernel certificates;',sum(accepted),'model accepted;',len(rows)-sum(accepted),'exact residual cases')
