# External critique shared by the programme owner, 2026-10-07 (mid-session 2)

Source: pasted by the programme owner; an outside review of an earlier, broader proposal. Kept here
verbatim in substance as a standing input to the programme. Disposition at the end.

## Main points
1. **Prior work is closer than claimed.**
   - Games for AI Control (Griffin, Thomson, Shlegeris, Abate; arXiv 2409.07985; IASEAI 2026): POSG models of
     control evaluations, Pareto-optimal protocol synthesis, trusted monitoring.
   - Towards Guaranteed Safe AI (2405.06624).
   - Proof-carrying code / seL4.
   - NASA verified runtime assurance (Simplex).
   - SSProve, VCVio.
   - Out of Control (Perrier, 2506.17846).
   - Reliability Theory for AI Control (Molnar, 2609.26419; shared failure domains).
   - Verdict: broad synthesis has limited novelty. A reusable machine-checked analysis that **changes how a real
     protocol is designed** could be substantial.
2. **Experiments → proofs handoff.** A benchmark gives E_{a~Q}[miss | a], but theorems need sup_a and bounds after
   every reachable history. Rare events: 0 failures in 10,000 trials gives 1 − 0.05^{1/10000} ≈ 3·10⁻⁴. The hardest
   contribution may be **defensible empirical assumptions**, not the inequalities.
3. **Strategic intelligence is not a new mathematical obstacle.** A universal theorem covers intelligent
   disturbances inside its quantified class. The questions are: omitted channels, corruption of observations or the
   fallback, hidden information, changes to the dynamics or the spec, and cross-session coordination. The objective
   is inf_{P: Use(P) ≥ u0} sup_{U ∈ 𝒜} Pr(bad by H), and the order matters.
4. **Information bottleneck.** One advice bit can decide the outcome. Leakage ≠ causal influence.
5. **Composition.** Shared blind spots: the same marginals support a 100× difference. The sequential bound
   Pr ≤ 1 − ∏(1 − p_t) ≤ Σ p_t needs conditional bounds after every history.
6. **Four obligations:** deductive correctness; specification fidelity; implementation correspondence;
   environmental validity. Runtime assurance needs a gate *before* irreversible actions. "Trusted" ≈ not scheming,
   not infallible.
7. **Suggested first project:** machine-checked risk bounds for a **stateful trusted-monitoring protocol**.
   - Reproduce a Games-for-AI-Control result.
   - Use one concrete failure event and explicit state (budget, artifacts, feedback, observations, shutdown).
   - Use sets of admissible transition models (uncertainty).
   - An optimiser produces protocol + bound; Lean checks the certificate.
8. **Success criteria:** non-vacuity; specification fidelity; necessary assumptions shown by counterexamples;
   decision relevance; honest scope. Stop if the premise becomes "the monitor reliably detects every strategically
   chosen harmful action".

## Disposition (orchestrator, 2026-10-07)
- Agreed:
  - (2) is our A6 (r) and A9 (coverage). The stack isolates them; it does not solve them.
  - UMLOWERF1 and UMSURVF1 give the protocol-sampling analogue of the rare-event point (risk ≥ about k/n_h for every nonadaptive design). Neither converts a benchmark average into a worst-case, history-conditional premise (Reviewer A, final review 2).
  - (3) matches our use of "capability-free".
  - UMUSE formalises honest availability and a necessary (mimicry) lower constraint on universal certificates; it is not an inf–sup optimisation (Reviewer A and Reviewer B, final review 2).
  - (5) matches our withdrawn product claim.
- Novelty: Games for AI Control has safety/usefulness Pareto frontiers (trusted monitoring), so UMUSE's Pareto framing
  is not new. Add all of the above to the novelty gate and CORRESPONDENCE.
- Already met: necessary-assumption counterexamples (A11 absorbing shutdown; the decoder; defer without incrimination)
  and decision relevance (class-aware vs global slack; incrimination for defer). Weak: non-vacuity (coarse views
  only).
- Actions:
  - Restructure STACK.md by the four obligations, tagging each assumption by what could discharge it.
  - After UMUSE, UMDEFER and the VCVio refinement: propose (7) as the next step to the programme owner, merged with stack item 5
    (trusted monitoring; N1b dual-certificate infrastructure). Pending the programme owner's decision.
