# Untested theory obligations and migration order

**Current branch does not close the following proof obligations.**
Do not relabel drafts as theorems, or use them to justify a deployment.

1. **Halt liveness**: specify a non-vacuous fairness law, such as eventual
   scheduling of an enabled trusted halt transition; prove \`eventually halted\`
   under that law and separately prove halt is absorbing. A trace that forever
   starves the halt transition must remain a counterexample absent fairness.
2. **Audit truncation**: define prefix truncation on the *same* attack/audit
   probability space, the stopping rule and whether the first k attacks are
   unaudited. Show the bound with a supremum over valid adaptive histories, not
   a population-average per-step miss rate.
3. **Leak-witness near attainment**: formalize the exact quantifier order over
   sender-controllable views, seed, receiver decoder, randomization and epsilon;
   a fully controllable N-view construction should approach the cardinality
   upper bound to within \`1−ε\`. The existing exact witness is narrower than
   general runtime attainability.
4. **Positive audit with false positives**: introduce trusted reserved budget
   or randomized paced scheduling so a false-positive adversary cannot exhaust
   all honest availability. Bound honest interruption and catastrophe in the
   same formal protocol under explicitly named assumptions.
5. **Policy integrity**: \`PolicyTamper\` exposes the missing premise, but its
   correspondence to filesystem immutability, gateway process memory and
   privileged host deputies is still unproved.
6. **Gate composition**: \`GateComposition\` needs a concrete shared-state
   instantiation for EgressGate and AuditDispatch (including check-before-effect,
   crash/restart and external callback authority).

## Module transition

The new \`ControlStack/Core/\`, \`Families/F1-F8/\`,
\`Scenarios/\` and \`Witnesses/\` paths are **import-compatible facades**.
Original modules have not moved because historical evidence manifests pin their
source bytes and a mass move would destabilize imports. After the recorded
registry is reviewed, migrate one family at a time, leave re-export modules at
the old paths, update all evidence hashes *only after independently verifying
content equivalence*, and run full Lake and ledger gates.

F4, F5 and F7 facades do **not** imply complete signature verification,
resource leases, or distinct-principal signed human approval. They currently
index nearby primitives only.

## Historical documentation

\`STATUS.md\` is the newly generated synopsis. \`ROADMAP.md\`, \`STACK.md\`,
\`SESSION.md\` and handoffs remain historical evidence because other documents,
commits and reviewers cite them. Archive only after link migration and
provenance audit, not by deleting source records.
