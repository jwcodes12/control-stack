/-
No-go results for bounded-observation safeguards (review: SCENARIO-CATALOG §9 Q4; feedback on statement fidelity).

`controllable_leak`: honest usefulness alone does NOT imply leakage; what does is CONTROLLABILITY. If the sender can
realise N traces (`realize : Fin N → T`) whose receiver views are pairwise distinct, then an encoder/decoder pair
recovers a uniform secret on M (|M| ≥ N) with probability exactly N/|M|. Together with `covert_bound` (≤ |V|/|M|),
the achievable leakage is governed by the number of sender-controllable, receiver-distinguishable views.
`one_bit_coordinates`: N = 2 suffices to coordinate a binary action with certainty, so a cardinality cap never implies
"no coordination".
-/
import ControlStack.CovertChannel

namespace ControlStack.CovertNoGo

open ControlStack.Covert

/-- success of a trace-level encoder whose traces are observed through `view` -/
noncomputable def successView {M T V : Type} [Fintype M] [Fintype T]
    (view : T → V) (enc : M → T → ℝ) (dec : V → M → ℝ) : ℝ :=
  (Fintype.card M : ℝ)⁻¹ * ∑ m, ∑ t, enc m t * dec (view t) m

theorem controllable_leak {M T V : Type} [Fintype M] [Fintype T] [DecidableEq M] [DecidableEq T] [DecidableEq V]
    (N : ℕ) (hN : 0 < N) (view : T → V) (realize : Fin N → T)
    (hdist : Function.Injective (fun i => view (realize i)))
    (e : Fin N → M) (he : Function.Injective e) :
    ∃ (enc : M → T → ℝ) (dec : V → M → ℝ),
      (∀ m, IsDist (enc m)) ∧ (∀ v, IsDist (dec v)) ∧
      successView view enc dec = (N : ℝ) / (Fintype.card M : ℝ) := by
  classical
  let i0 : Fin N := ⟨0, hN⟩
  -- encoder: secret e i ↦ trace realize i; other secrets ↦ realize i0
  let pick : M → Fin N := fun m => if h : ∃ i, e i = m then h.choose else i0
  let enc : M → T → ℝ := fun m t => if t = realize (pick m) then 1 else 0
  -- decoder: view of realize i ↦ e i; anything else ↦ e i0
  let back : V → Fin N := fun v => if h : ∃ i, view (realize i) = v then h.choose else i0
  let dec : V → M → ℝ := fun v m => if m = e (back v) then 1 else 0
  have point : ∀ (f : T → ℝ) (t0 : T), ∑ t, (if t = t0 then (1 : ℝ) else 0) * f t = f t0 := by
    intro f t0; rw [Finset.sum_eq_single t0] <;> simp_all
  have pickE : ∀ i, pick (e i) = i := by
    intro i
    have h : ∃ j, e j = e i := ⟨i, rfl⟩
    simp only [pick, dif_pos h]
    exact he h.choose_spec
  have backV : ∀ i, back (view (realize i)) = i := by
    intro i
    have h : ∃ j, view (realize j) = view (realize i) := ⟨i, rfl⟩
    simp only [back, dif_pos h]
    exact hdist h.choose_spec
  refine ⟨enc, dec, ?_, ?_, ?_⟩
  · intro m; refine ⟨fun t => by simp only [enc]; split_ifs <;> norm_num, ?_⟩
    simp [enc]
  · intro v; refine ⟨fun m => by simp only [dec]; split_ifs <;> norm_num, ?_⟩
    simp [dec]
  · unfold successView
    have hterm : ∀ m, (∑ t, enc m t * dec (view t) m) = if (∃ i, e i = m) then 1 else 0 := by
      intro m
      simp only [enc]
      rw [point (fun t => dec (view t) m) (realize (pick m))]
      by_cases hm : ∃ i, e i = m
      · obtain ⟨i, rfl⟩ := hm
        simp [dec, pickE, backV]
      · have hp : pick m = i0 := by simp [pick, hm]
        have : m ≠ e (back (view (realize (pick m)))) := fun h => hm ⟨_, h.symm⟩
        simp [dec, this, hm]
    simp only [hterm]
    rw [Finset.sum_boole]
    have : (Finset.univ.filter fun m : M => ∃ i, e i = m) = Finset.univ.image e := by
      ext m; simp [eq_comm]
    rw [this, Finset.card_image_of_injective _ he, Finset.card_univ, Fintype.card_fin, div_eq_inv_mul]

/-- **One bit coordinates.** Two sender-realisable, receiver-distinguishable traces let colluders agree on a binary
action with certainty. -/
theorem one_bit_coordinates {T V : Type} [Fintype T] [DecidableEq T] [DecidableEq V]
    (view : T → V) (t0 t1 : T) (h : view t0 ≠ view t1) :
    ∃ (enc : Bool → T → ℝ) (dec : V → Bool → ℝ),
      (∀ m, IsDist (enc m)) ∧ (∀ v, IsDist (dec v)) ∧ successView view enc dec = 1 := by
  obtain ⟨enc, dec, h1, h2, h3⟩ := controllable_leak (M := Bool) 2 (by norm_num) view
    (fun i => if i = 0 then t0 else t1)
    (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [eq_comm])
    (fun i => decide (i = 1)) (by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all)
  exact ⟨enc, dec, h1, h2, by rw [h3]; simp⟩

#print axioms controllable_leak
#print axioms one_bit_coordinates

end ControlStack.CovertNoGo
