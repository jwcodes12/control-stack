"""Schema-only migration; it never invents fresh host observations."""
import copy
from .validator import validate

def to_v01(ir):
    validate(ir)
    result=copy.deepcopy(ir);result['version']='0.1'
    return validate(result)
