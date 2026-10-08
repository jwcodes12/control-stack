/-
A leaky instance of `Leakage.audit_leak_bound` (adversarial review D5): the hypotheses are satisfiable with a real
leak, and the bound is attained.

N = 2 rounds, budget B = 1 (the schedule audits round 0 or round 1, each w.p. 1/2), k = 1 attack step. Before round 0
the attacker sees a noisy bit z about "round 0 is audited", flipped with probability ε ∈ [0, 1/2]. It attacks round 0
if z says "not audited", and round 1 otherwise. The leak certificate has round masses 2(1−ε) and 1. The bound is
C(1,1)/C(2,1) · 2(1−ε) = 1 − ε (`leak_bound`). By hand calculation (adversarial review D5), the attacker's true
survival is also 1 − ε, so the bound would be tight here. That equality is NOT proved in Lean.
-/
import ControlStack.Leakage

namespace ControlStack.LeakWitness

open ControlStack.Leakage ControlStack.Covert Finset

/-- the round kernel. Round 0: the leak z ~ BSC([0 ∈ S], ε), attack iff z = false, flag = attack ∧ audited. Round 1:
no leak, attack iff round 0 did not attack. -/
noncomputable def K (ε : ℝ) (S : Finset (Fin 2)) (h : List (Unit × AOut Bool)) (yo : Unit × AOut Bool) : ℝ :=
  let a := yo.2.1
  let z := yo.2.2.1
  let f := yo.2.2.2
  let r := h.length
  let fl : ℝ := if f = (a && decide (memN S r)) then 1 else 0
  if r = 0 then
    (if z = decide (memN S 0) then 1 - ε else ε) * (if a = !z then 1 else 0) * fl
  else
    let a0 := match h with
      | [] => false
      | e :: _ => e.2.1
    (if z = false then 1 else 0) * (if a = !a0 then 1 else 0) * fl

/-- the leak certificate on non-catch outputs -/
noncomputable def cl (ε : ℝ) (g : List (AOut Bool)) (o : AOut Bool) : ℝ :=
  if g.length = 0 then (if o.1 = !o.2.1 then 1 - ε else 0)
  else
    let a0 := match g with
      | [] => false
      | e :: _ => e.1
    (if o.2.1 = false then 1 else 0) * (if o.1 = !a0 then 1 else 0)

variable (ε : ℝ) (h0 : 0 ≤ ε) (h12 : ε ≤ 1 / 2)
include h0 h12

theorem K_nonneg (S : Finset (Fin 2)) (h : List (Unit × AOut Bool)) (z : Unit × AOut Bool) : 0 ≤ K ε S h z := by
  unfold K; dsimp only
  split_ifs <;> first | positivity | (apply mul_nonneg <;> (try apply mul_nonneg) <;> norm_num <;> linarith)

theorem K_sum (S : Finset (Fin 2)) (h : List (Unit × AOut Bool)) : ∑ z, K ε S h z ≤ 1 := by
  simp only [K, Fintype.sum_prod_type, Fintype.univ_unit, Finset.sum_singleton, Fintype.sum_bool]
  by_cases hr : h.length = 0
  · cases hm : decide (memN S 0) <;> simp [hr, hm]
  · cases h with
    | nil => simp at hr
    | cons e t =>
      obtain ⟨u, a0, z0, f0⟩ := e
      cases hm : decide (memN S ((u, a0, z0, f0) :: t).length) <;> cases a0 <;> simp [hm]

theorem K_cons (S : Finset (Fin 2)) (h : List (Unit × AOut Bool)) (y : Unit) (o : AOut Bool) (hK : K ε S h (y, o) ≠ 0) :
    o.2.2 = (o.1 && decide (memN S (h.map Prod.snd).length)) := by
  rw [List.length_map]
  by_contra hne
  apply hK
  unfold K; dsimp only
  simp [hne]

theorem K_dom (S : Finset (Fin 2)) (h : List (Unit × AOut Bool)) (o : AOut Bool) (hf : o.2.2 = false) :
    ∑ y, K ε S h (y, o) ≤ cl ε (h.map Prod.snd) o := by
  obtain ⟨a, z, f⟩ := o
  simp only at hf; subst hf
  simp only [Fintype.univ_unit, Finset.sum_singleton, K, cl, List.length_map]
  by_cases hr : h.length = 0
  · simp only [hr, if_true]
    have hz : (if z = decide (memN S 0) then 1 - ε else ε) ≤ 1 - ε := by split_ifs <;> linarith
    split_ifs <;> nlinarith
  · simp only [hr, if_false]
    cases h with
    | nil => simp at hr
    | cons e t =>
      simp only [List.map_cons]
      split_ifs <;> norm_num

theorem cl_nonneg (g : List (AOut Bool)) (o : AOut Bool) : 0 ≤ cl ε g o := by
  unfold cl; dsimp only; split_ifs <;> norm_num <;> linarith

theorem leak_mass : mass (dropStop caughtFlag (cl ε)) 2 [] = 2 * (1 - ε) := by
  simp only [mass, cval, dropStop, caughtFlag, cl, Fintype.sum_prod_type, Fintype.sum_bool, List.length_nil,
    List.nil_append, List.length_singleton]
  norm_num
  ring

/-- **The leak bound, instantiated with a real leak**: survival ≤ 1 − ε. -/
theorem leak_bound :
    ∑ S : Finset (Fin 2), (if S ∈ AuditBudget.randomSchedules 2 1 then (Nat.choose 2 1 : ℝ)⁻¹ else 0) *
      val (K ε S) (survInd 1 S) 2 [] ≤ 1 - ε := by
  have h := audit_leak_bound (N := 2) 1 1 (by norm_num) (K ε) (cl ε)
    (fun S _ h z => K_nonneg ε h0 h12 S h z) (fun S _ h => K_sum ε h0 h12 S h)
    (fun S _ h y o hK => K_cons ε h0 h12 S h y o hK) (fun S _ h o hf => K_dom ε h0 h12 S h o hf)
    (fun g o => cl_nonneg ε h0 h12 g o)
  rw [leak_mass ε h0 h12] at h
  refine h.trans (le_of_eq ?_)
  norm_num [Nat.choose]
  ring

end ControlStack.LeakWitness

#print axioms ControlStack.LeakWitness.K_sum
#print axioms ControlStack.LeakWitness.K_dom
#print axioms ControlStack.LeakWitness.leak_mass
#print axioms ControlStack.LeakWitness.leak_bound
