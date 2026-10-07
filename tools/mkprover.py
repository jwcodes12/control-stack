"""Set up an isolated prover dir: prompt.md, statement.lean, deps.lean (dep statements + gated dep proofs), check.sh."""
import sys, os, pathlib, subprocess, stat
sys.path.insert(0, str(pathlib.Path.home() / "research/proofledger/harness"))
os.chdir(pathlib.Path.home() / "research/proofledger")
import pl
cid = sys.argv[1]
d = pathlib.Path("/var/tmp/opus-provers") / cid
d.mkdir(mode=0o700, parents=True, exist_ok=True)
(d / "prompt.md").write_text(subprocess.run(["python3", "harness/pl.py", "prove-prompt", cid], capture_output=True, text=True).stdout)
(d / "statement.lean").write_text(pl.statement_of(cid))
st = pl.L.derive()
deps = []
for dcid in pl.dep_closure(st[cid]["deps"]):
    deps.append(pl.L.get_blob(st[dcid]["statement_blob"]))
    g = st[dcid]["gates"].get("claim")
    if g:
        deps.append(f"namespace PLDep_{dcid}\nopen PL_{dcid}\n{pl.L.get_blob(g['proof_blob'])}\nend PLDep_{dcid}")
    else:
        # unverified dependency: provide its Claim as a hypothesis-free axiom-free stub? No: the prover must
        # reference it only through the NAME PLDep_<dep>.claim, which will exist at the gate once verified.
        deps.append(f"namespace PLDep_{dcid}\nopen PL_{dcid}\ntheorem claim : Claim := by sorry\nend PLDep_{dcid}")
(d / "deps.lean").write_text("\n".join(deps))
(d / "check.sh").write_text(f"""#!/bin/bash
# Assemble exactly what the gate assembles and compile against the shared (read-only) Mathlib project.
# Usage: ./check.sh            (checks proof.lean in this directory)
D={d}
F=$D/Check_{cid}.lean
{{ echo "import Mathlib"; cat $D/deps.lean; echo; cat $D/statement.lean; echo; echo "namespace PLProof_{cid}"; echo "open PL_{cid}"; cat $D/proof.lean; echo; echo "end PLProof_{cid}"; echo "theorem gate_check_claim : PL_{cid}.Claim := PLProof_{cid}.claim"; echo "theorem gate_check_witness : PL_{cid}.Witness := PLProof_{cid}.witness"; echo "#print axioms gate_check_claim"; echo "#print axioms gate_check_witness"; }} > $F
cd $HOME/research/alignment-contrib/lean/StabilityDebate && timeout 1500 $HOME/.elan/bin/lake env lean $F
""")
(d / "check.sh").chmod(0o700)
print(d, "deps:", pl.dep_closure(st[cid]["deps"]))
