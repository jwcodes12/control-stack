# Fidelity audit (orchestrator): TMGACF1, Games for AI Control trusted monitoring as a certified instance

Statement: `ledger/TMGAC.lean` v1 (frozen 89331ac41986). Depends on TMCERTF1. Proof: 554 lines (isolated prover
agent; certificate soundness for the Witness proved locally), gated, standard axioms. Session 3, direction (A).

History:
- **v0**: Reviewer A major, Reviewer B major. Neither found a false conjunct.
  - The usefulness bridge was to a mis-transcribed recurrence: GAC App. C.2 counts audited safe solutions as used.
    My own numerics had the same transcription error on both sides, so they could not catch it.
  - (M)'s docstring hid the dependence on the current state.
  - The Witness did not compute its values.
- **v1**: corrected usefulness (`usedReward` = 1 − qd + [c > 0]·qa; `uGAC` per App. C.2); adapter lawfulness (LQ);
  grid corollary; coin-count-only separation (9/32); the Witness proves exG3 is a genuine GAC protocol (gacQ with an
  ROC) and computes safety 63/64 and usefulness 3/2, 19/8 and 1 (audited-only); evidence v2 (2400 exact comparisons,
  monotone ROC tables, unrestricted algebra, 0 mismatches).

| element | classification | note |
|---|---|---|
| `gac`, `gacQ` | MODELLING (GAC §4, App. C; perfect auditor; memoryless threshold protocols) | n + 1 indexing; the c = 0 convention qa m 0 = 0, f 0 = 0 is the only reading under which both GAC boundary formulas hold |
| (L), (LQ) | SOURCE | lawfulness of the game and of the threshold adapter |
| (Z) | SOURCE | = App. C.1 case analysis (λ-form with the printed c = 0 typo corrected: TPR f(qd), not FPR); algebraic identity |
| (UZ) | SOURCE | = App. C.2: used = run or audited-and-safe; deferred does not count |
| (M), (Lip), (Grid) | SOURCE | GAC's sup over β is sound only for finite mixtures of constant-rate policies (same rate at every history AND state); grid certification needs J ≈ 5000 at N = 100 for 10⁻² |
| (W) | SOURCE | at C = 0 constant rates are WLOG (also with TA > 0 at c = 0) |
| (T5) | SOURCE, scoped | exact sensitivity of GAC's guarantee to its stated null-observation assumption: 13/50 (constant rates) vs 9/32 (coin count only) vs 11/32 (round index only = full information); a small instance, not a realistic configuration |

**Reading.** Within the GAC model, the constant-rate (memoryless, null-observation) Red class is not without loss of
generality once the Red can tell where it is. Knowing either the round index or the coin count raises its success
probability above every constant rate. The full-information certificate (TMCERTF1 with Vstar) holds without that
assumption. Float numerics with 100 problems, 2 coins and GAC's fitted score laws show the same pattern: 0.36 for a fixed
rate, 0.67 for a Red attacking only late problems, 0.71 with full information. GAC states the restriction explicitly, so
this is a sensitivity result, not a refutation.

**Prior art, by claim.**
- Restricted observations and withholding the round number: Mallen et al. 2412.12480.
- Temporal coordination through timestamps and codebase messages: Korbak et al. 2501.17315, §7.5.
- Time-varying auditing against a constant attack rate: Ctrl-Z 2504.10374, App. L.
- The attack-rate choice: Greenblatt et al. 2312.06942.

Calibrated: modest. The exact separation and the Lean-checked bridges are the artifact.
