import sys
sys.path.insert(0, '/home/opc/research/proofledger/harness')
import os; os.chdir('/home/opc/research/proofledger')
import pl, leangate
cid, path, deps = sys.argv[1], sys.argv[2], sys.argv[3].split(',')
ok, log = leangate.check_statement(cid, open(path).read(), pl.dep_statements(deps))
print(ok); print(log[-5000:])
