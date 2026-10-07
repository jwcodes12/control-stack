# Fidelity audit (orchestrator): UMHSF1, testing infrastructure

Statement: `ledger/UMHS.lean`, frozen as UMHSF1. Informal source: DESIGN.md v1 §3 (UMHS, UMLEAK).

| conjunct | informal claim | binders and hypotheses | classification | verdict |
|---|---|---|---|---|
| T2 | pass(P) ≤ e^η pass(Q) + hs_η(P‖Q) for every [0,1]-valued rule, every real η | `IsRule φ` | SOURCE (randomised stateless rule). No law hypotheses: the bound holds for any real P and Q, which is stronger | faithful |
| T2 attainment | some rule attains equality | ∃ φ, IsRule φ | Reviewer A: the docstring says "deterministic rule" but the Lean says only "some [0,1] rule". The weaker reading is still the source claim; the intended witness is the indicator | faithful (docstring stronger than statement; noted) |
| T1 | advantage ≤ TV | `IsDist P`, `IsDist Q`, `IsRule φ` | SOURCE. Equal total mass is needed for the symmetric bound | faithful |
| T4a | kernel DPI for hs | `IsKernel K` | SOURCE | faithful |
| T4b | content-only implies hs ≤ content-level hs | `ContentOnly M c` | SOURCE. Renamed from "attainment" per the Reviewer A review | faithful |
| T4c | content-preserving implies content-level hs ≤ hs | `IsKernel M`, `ContentPreserving M c` (exact decoder on supports) | SOURCE; strong hypothesis, no LLM mediator satisfies it (DESIGN §3); hence T4c-approx | faithful |
| T4c-approx | decoder error ≤ γ on every x gives the floor minus (1+e^η)γ | `IsKernel M`, `IsDist PA PH`, per-x error bound | SOURCE | faithful |
| T5d | perturbation | none | TYPING; holds for all reals | faithful |
| T4c' | maximal-leakage floor and its attainment | `IsKernel M`, `B` nonempty, `IsDist Q`, domination | SOURCE. Q ranges over all laws, a superset of mediated honeypot laws, so the floor applies to every honeypot design | faithful |
| domination | class coverage p implies M x ≤ (1/p)·q | `ContentOnly`, `IsDist PH`, `p > 0`, per-bad-class mass ≥ p | SOURCE. `Bad` is a free predicate; PH need not be supported on Bad (more general) | faithful |

**Witness.** TV 1/2 instance; the identity mediator is a kernel, content-preserving and content-only; maximal leakage is
2 for two classes. Non-degenerate.

**Novelty.** Classical:
- (ε,δ)-indistinguishability in hypothesis-testing form;
- post-processing;
- maximal leakage (Issa–Wagner–Kamath 2020).

Infrastructure lemma for the control stack.
