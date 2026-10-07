You are a HOSTILE REVIEWER and NOVELTY JUDGE for a set of Lean-verified results in AI control. Do not praise; find
errors. Use web search for prior art. Everything below has passed a Lean kernel gate (standard axioms only) against the
frozen statements shown; your job is NOT to re-check proofs but to check (1) FIDELITY: does each Lean statement say what
the plain-English row in STACK.md claims (look for excess or missing binders, hypotheses that make it vacuous or
trivially true, wrong-reason truth, encoding traps, quantifier order); (2) OVERCLAIMS in STACK.md / the plain-English
guarantees (capability-free? which quantities are really trusted? does it speak to the named real protocols?);
(3) NOVELTY of each result, calibrated: one of known / classical / modest / apparently open, with references
(verify each arXiv id you cite); (4) SIGNIFICANCE of the package for AI control, honestly; (5) the single most
valuable NEXT FORMALISATION STEP (formal work only: a Lean theorem, a verified model, a composition; NOT GPU/model
experiments).
The programme owner accepts classical lemmas as infrastructure; triviality is not a defect, but must be reported.
For each issue: severity (FATAL / MAJOR / MINOR), the exact row/statement, why, and the fix. End with a per-CID table
(fidelity verdict, novelty label, references) and an overall verdict.
