"""R2 collector: RUNTIME_OBSERVED Docker daemon facts, not attestation."""
import argparse
import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT))
from tools.collect_deployment_docker import capture, normalize
__all__=['capture','normalize']
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('compose');p.add_argument('--project',required=True);p.add_argument('--output',required=True);a=p.parse_args();capture(a.compose,a.project,a.output)
