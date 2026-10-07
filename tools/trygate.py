import sys
sys.path.insert(0, '/home/opc/research/proofledger/harness')
import os; os.chdir('/home/opc/research/proofledger')
import pl, leangate
cid, path, target = sys.argv[1], sys.argv[2], sys.argv[3]
ok, log = leangate.gate(cid, pl.statement_of(cid), open(path).read(), target, pl.dep_texts(cid))
print(ok); print(log[-6000:])
