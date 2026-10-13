from pathlib import Path
import sys
sys.dont_write_bytecode=True
import importlib.util,concurrent.futures
b=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('regate',b/'regate.py');r=importlib.util.module_from_spec(spec);spec.loader.exec_module(r)

def check(n):
 cid=f'bg1n2_{n}';statement=(b/(cid+'.statement.lean')).read_text()
 ok,slog=r.g.check_statement(cid,statement,[r.r.IMPORTS])
 for target,suffix in [('claim','.proof.lean'),('witness','.witness.proof.lean')]:
  proof=(b/(cid+suffix)).read_text()
  passed,log=r.g.gate(cid,statement,proof,target,[r.r.IMPORTS],timeout=120) if ok else (False,'FAIL statement check\n'+slog)
  r.receipt(cid,target,statement,proof,ok,slog,passed,log)
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex:
 list(ex.map(check,[int(n) for n in sys.argv[1:]] or range(1,11)))
