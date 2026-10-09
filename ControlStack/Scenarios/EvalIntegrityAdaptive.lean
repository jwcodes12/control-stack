/-
SC-21 (and SC-22) against an ADAPTIVE corrupting agent (review packet 2026-10-09: `EvalIntegrity.sc21_undetected_prob`
is NON_ADAPTIVE in the corrupted set).

Setting, as instances of the existing hidden-schedule audit theorems. Tasks are played in a fixed order as N rounds.
In round i the agent decides whether to corrupt task i's reported result (the attack bit). The independent executor's
re-execution sample S is a uniformly random hidden set of B tasks, drawn before the run and not shown to the agent.
A corrupted task in S is detected (the catch flag). The agent's decision law σ may depend on everything it has
seen: its own earlier decisions and the catch flags. That is MORE than the honest deployment shows it (it sees
nothing about S until publication), so an agent that ignores the flags is a special case. Task content may also be
arbitrary and hidden from the bound (`sc21_adaptive_content`).

Results (adversary class ADAPTIVE_FEEDBACK):
- `sc21_adaptive`: P(the agent corrupts ≥ k results and none of them is re-executed) ≤ C(N−k,B)/C(N,B), for every
  adaptive σ (from `Leakage.audit_adaptive_hidden`). Adaptivity gains nothing over the non-adaptive value of
  `EvalIntegrity.sc21_undetected_prob`.
- `sc21_adaptive_content`: the same bound when each round also carries arbitrary task content and any other hidden
  state (monitor flags, extra checks that may depend on S), provided the agent's corrupt/no-corrupt decision has law
  σ(visible history) (from `ReservedAudit.reserved_adaptive`); success there also requires no detection by any extra
  check.
- `sc21_adaptive_recall`: with IMPERFECT detection (each re-execution of a corrupted task detects with probability
  ≥ r, per history), P(≥ k corrupted and never detected) ≤ hypMiss N B k r (from
  `ReservedRecall.adaptive_recall_bound`).
- `sc21_adaptive_example`: N = 100, B = 10, k = 5 gives ≤ 10104934117421/17310309456440 ≈ 0.584 for every adaptive
  agent.
- Witness `leaked_sample_survives`: if the sample leaks (is observable), the agent corrupts k tasks outside it and is
  never detected (survival 1), so hiddenness of the sample is load-bearing.

Limits: per-round decisions in a fixed task order (the agent cannot reorder tasks); detection by re-execution is
modelled as the catch flag (deterministic re-execution, or recall r); no leak about S (any timing or side leak needs the
certificate form `Leakage.audit_leak_bound`). Classical mathematics; no novelty.
-/
import ControlStack.Core.Leakage
import ControlStack.Families.F6.ReservedAudit
import ControlStack.Families.F6.ReservedRecall
import ControlStack.AuditBudget

namespace ControlStack.EvalIntegrityAdaptive

open Finset ControlStack.Leakage ControlStack.Covert ControlStack.ReservedAudit ControlStack.ReservedRecall

variable {N : ℕ}

/-- **Adaptive corruption of evaluation results.** For every adaptive decision law σ, the probability that the agent
corrupts at least k results and none of them is in the hidden re-execution sample is ≤ C(N−k,B)/C(N,B).
Adversary: ADAPTIVE_FEEDBACK. -/
theorem sc21_adaptive (k B : ℕ) (hB : B ≤ N) (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) :
    ∑ S : Finset (Fin N), (if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ else 0) *
      val (hiddenK σ S) (survInd k S) N [] ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) :=
  audit_adaptive_hidden k B hB σ hσ

/-- **Arbitrary task content and hidden state.** The same bound for any round kernel whose hidden part (task content,
monitor flags, extra checks, even S-dependent ones) is arbitrary, provided the agent's decision has law σ(visible
history). Adversary: ADAPTIVE_FEEDBACK. -/
theorem sc21_adaptive_content {Y : Type} [Fintype Y] (k B : ℕ) (hB : B ≤ N)
    (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ)
    (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h z, 0 ≤ K S h z)
    (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h, ∑ z, K S h z ≤ 1)
    (hmarg : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h (a : Bool),
      ∑ y, ∑ c : Bool, K S h (y, (a, (), c)) ≤ σ (h.map Prod.snd) a) :
    ∑ S : Finset (Fin N), pU N B S * val (K S) (successInd k S) N []
      ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) :=
  reserved_adaptive k B hB K σ hσ hK0 hK1 hmarg

/-- **Imperfect detection.** If each re-execution of a corrupted task detects with probability ≥ r (per history), an
adaptive agent corrupts ≥ k results without any detection with probability ≤ hypMiss N B k r. -/
theorem sc21_adaptive_recall {Y : Type} [Fintype Y] (k B : ℕ) (hB : B ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ)
    (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h z, 0 ≤ K S h z)
    (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h, ∑ z, K S h z ≤ 1)
    (hrec : ∀ S, S ∈ AuditBudget.randomSchedules N B → ∀ h (a : Bool),
      ∑ y, K S h (y, (a, (), false)) ≤
        σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1)) :
    ∑ S : Finset (Fin N), pU N B S * val (K S) (recallSucc (N := N) k) N [] ≤ hypMiss N B k r :=
  adaptive_recall_bound k B hB r hr0 hr1 K σ hσ hK0 hK1 hrec

/-- **Non-vacuous instance**: 100 tasks, 10 re-executed, 5 corrupted: ≤ 10104934117421/17310309456440 ≈ 0.584 for
every adaptive agent. -/
theorem sc21_adaptive_example (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) :
    ∑ S : Finset (Fin 100), (if S ∈ AuditBudget.randomSchedules 100 10 then (Nat.choose 100 10 : ℝ)⁻¹ else 0) *
      val (hiddenK σ S) (survInd 5 S) 100 [] ≤ (10104934117421 : ℝ) / 17310309456440 := by
  have h := sc21_adaptive (N := 100) 5 10 (by norm_num) σ hσ
  rw [show (100 - 5 : ℕ) = 95 from rfl, AuditBudget.choose_95_10, AuditBudget.choose_100_10] at h
  exact_mod_cast h

/-- **Witness: a leaked sample defeats re-execution.** If the agent knows the sample S of size B, it corrupts k ≤ N − B
tasks outside S and survives with probability 1. -/
theorem leaked_sample_survives {B k : ℕ} (S : Finset (Fin N)) (hS : S.card = B) (hk : k ≤ N - B) :
    ∃ A : Finset (Fin N), A.card = k ∧ Disjoint S A ∧ AuditBudget.survival {S} A = 1 :=
  AuditBudget.observable_schedule_nogo S hS hk

end ControlStack.EvalIntegrityAdaptive

#print axioms ControlStack.EvalIntegrityAdaptive.sc21_adaptive
#print axioms ControlStack.EvalIntegrityAdaptive.sc21_adaptive_content
#print axioms ControlStack.EvalIntegrityAdaptive.sc21_adaptive_recall
#print axioms ControlStack.EvalIntegrityAdaptive.sc21_adaptive_example
#print axioms ControlStack.EvalIntegrityAdaptive.leaked_sample_survives
