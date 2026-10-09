You are an adversarial reviewer (red team) for a Lean 4 formal model. Files: SC26Transaction.lean (the model and theorems) and Gate.lean (the shared interface it instantiates). Read both fully.

Claimed scenario (SC-26): "an agent never causes an irreversible external transaction (a bank transfer) without an exact, independent, one-use approval; total spend ≤ cap; HALT freezes effects; crash/retry delivery is exactly-once at an idempotent bank." The adversary chooses any sequence of operations; the only premise is `legal` (no untrusted op carries the gate's credential).

Your job: find where the formal statement is weaker than, or different from, the claim. Be concrete. Specifically check:
1. Vacuity: can `Good` hold trivially? Is `Inv`/`Good` satisfied by states that a reasonable reader would call unsafe? (e.g. approvals by the approver for a request that the approver never saw; approvals for a different request id that happen to share payload; `Approved` existentially quantified over any approval for the key)
2. Encoding traps: reqOf first-match semantics; ids reused; `execute` checks "some approval with ap.1 = id" — is the approval used the one that `Good` names? Can one approval authorize two different effects? Can an approval issued BEFORE a request exist (dangling id) later bind to a new request? (Note request ids come from `next` and approvals require reqOf to exist at approval time — check this.)
3. Halt: `halt_freezes` premise and whether pending reservations after halt are a problem; requests after halt; can admin un-halt?
4. Cap: is the bound on bank amounts or on reservations; can amount 0 transactions or overflow matter (ℕ)?
5. The witnesses: does each one actually show the removed check is necessary, or is it trivial? Is `nonce_protects_budget_only` correctly characterized?
6. What important attacker capability is NOT modelled (e.g. approver confusion/UI deception, request content the approver sees vs. what the bank executes, bank accepting gate credential for arbitrary payloads, multiple gates, replay across restarts with DB rollback)? Which of those must be stated as premises in correspondence documentation?
7. Is there a real counterexample: a legal trace whose final state has an effect a careful reader would call unauthorized, yet `sc26_safe` holds?

Output format: ### Verdict (3 sentences) / ### Defects (numbered: location, problem, concrete trace or instance, fix) / ### Prose overclaims / ### Missing premises to document / ### Triviality and novelty (honest). Do not praise. If something is fine, say so in one line.
