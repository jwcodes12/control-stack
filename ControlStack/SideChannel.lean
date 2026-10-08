/-
Side-observation extension of the covert-propagation bound (CovertChannel.lean).

`covert_bound` assumes the receiver observes nothing but the mediated view v ∈ V. Here the receiver additionally sees a
side observation o ∈ O, produced by a FIXED kernel W from a side state s ∈ S that the sender may choose (jointly with v,
adaptively, with a shared seed). W models the environment, not an adversarial component: the sender controls only s.

Domination certificate: any c : O → ℝ with W s o ≤ c o for every s. Then
  P(recover a uniform secret on M) ≤ |V| · Σ_o c o / |M|.
The least such Σ_o c o is Σ_o max_s W s o, the exponential of the maximal leakage of W. Special cases:
- a side observation the sender cannot influence (W s = w for all s) gives Σ c = 1, recovering `covert_bound`;
- the trivial certificate c ≡ 1 gives |V|·|O|/|M| (the side observation as an extra noiseless channel);
- certificates multiply over independent per-episode kernels (`dom_pi`), matching the lifetime ledger.

Assumptions carried by the deployment, not by these theorems: W is fixed and independent of the secret except through
s; per-episode kernels act independently given the side states (no feedback from side outputs into later side states);
nothing else is observed.
-/
import ControlStack.CovertChannel

namespace ControlStack.SideChannel

open Finset ControlStack.Covert

/-- success probability with a mediated view v ∈ V and a side observation o ~ W(s) of a sender-chosen side state s -/
noncomputable def sideSuccess {Ω M V S O : Type} [Fintype Ω] [Fintype M] [Fintype V] [Fintype S] [Fintype O]
    (ρ : Ω → ℝ) (W : S → O → ℝ) (enc : Ω → M → V × S → ℝ) (dec : Ω → V × O → M → ℝ) : ℝ :=
  ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, ∑ x : V × S, enc ω m x * ∑ o, W x.2 o * dec ω (x.1, o) m)

/-- per-seed core: Σ_m Σ_{v,s} enc(v,s|m) Σ_o W(o|s) dec(m|v,o) ≤ |V| · Σ_o c o -/
theorem per_seed_side {M V S O : Type} [Fintype M] [Fintype V] [Fintype S] [Fintype O]
    (W : S → O → ℝ) (c : O → ℝ) (hc : ∀ s o, W s o ≤ c o) (hc0 : ∀ o, 0 ≤ c o)
    (enc : M → V × S → ℝ) (dec : V × O → M → ℝ)
    (henc : ∀ m, IsDist (enc m)) (hdec : ∀ y, IsDist (dec y)) :
    ∑ m, ∑ x : V × S, enc m x * ∑ o, W x.2 o * dec (x.1, o) m ≤ (Fintype.card V : ℝ) * ∑ o, c o := by
  set g : V → M → ℝ := fun v m => ∑ o, c o * dec (v, o) m with hg
  have g0 : ∀ v m, 0 ≤ g v m := fun v m =>
    Finset.sum_nonneg fun o _ => mul_nonneg (hc0 o) ((hdec (v, o)).1 m)
  -- step 1: replace W by its dominating certificate
  have step1 : ∀ m, ∑ x : V × S, enc m x * ∑ o, W x.2 o * dec (x.1, o) m ≤ ∑ x : V × S, enc m x * g x.1 m := by
    intro m
    apply Finset.sum_le_sum; intro x _
    apply mul_le_mul_of_nonneg_left _ ((henc m).1 x)
    apply Finset.sum_le_sum; intro o _
    exact mul_le_mul_of_nonneg_right (hc x.2 o) ((hdec (x.1, o)).1 m)
  -- step 2: the marginal Σ_s enc(v,s|m) is at most 1
  have marg : ∀ m v, ∑ s, enc m (v, s) ≤ 1 := by
    intro m v
    have hsub : ∑ s, enc m (v, s) ≤ ∑ x : V × S, enc m x := by
      rw [Fintype.sum_prod_type]
      exact Finset.single_le_sum (f := fun v' => ∑ s, enc m (v', s))
        (fun v' _ => Finset.sum_nonneg fun s _ => (henc m).1 (v', s)) (Finset.mem_univ v)
    linarith [(henc m).2]
  have step2 : ∀ m, ∑ x : V × S, enc m x * g x.1 m ≤ ∑ v, g v m := by
    intro m
    rw [Fintype.sum_prod_type]
    apply Finset.sum_le_sum; intro v _
    have e : ∑ s, enc m (v, s) * g (v, s).1 m = (∑ s, enc m (v, s)) * g v m := by
      rw [Finset.sum_mul]
    rw [e]
    exact mul_le_of_le_one_left (g0 v m) (marg m v)
  -- step 3: sum over m using that each decoder row is a distribution
  have step3 : ∑ m, ∑ v, g v m = (Fintype.card V : ℝ) * ∑ o, c o := by
    rw [Finset.sum_comm]
    have : ∀ v, ∑ m, g v m = ∑ o, c o := by
      intro v
      simp only [hg]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro o _
      rw [← Finset.mul_sum, (hdec (v, o)).2, mul_one]
    simp [this]
  calc ∑ m, ∑ x : V × S, enc m x * ∑ o, W x.2 o * dec (x.1, o) m
      ≤ ∑ m, ∑ v, g v m := Finset.sum_le_sum fun m _ => (step1 m).trans (step2 m)
    _ = _ := step3

/-- **Side-channel bound.** For every shared seed law, every adaptive randomised choice of (view, side state) and every
decoder of (view, side observation): P(recover m) ≤ |V| · Σ_o c o / |M|, for any domination certificate c of W. -/
theorem side_bound {Ω M V S O : Type} [Fintype Ω] [Fintype M] [Fintype V] [Fintype S] [Fintype O] [Nonempty M]
    (ρ : Ω → ℝ) (W : S → O → ℝ) (c : O → ℝ) (hc : ∀ s o, W s o ≤ c o) (hc0 : ∀ o, 0 ≤ c o)
    (enc : Ω → M → V × S → ℝ) (dec : Ω → V × O → M → ℝ)
    (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω y, IsDist (dec ω y)) :
    sideSuccess ρ W enc dec ≤ (Fintype.card V : ℝ) * (∑ o, c o) / (Fintype.card M : ℝ) := by
  unfold sideSuccess
  have hM : (0 : ℝ) < (Fintype.card M : ℝ) := by exact_mod_cast Fintype.card_pos
  calc ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ *
          ∑ m, ∑ x : V × S, enc ω m x * ∑ o, W x.2 o * dec ω (x.1, o) m)
      ≤ ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ((Fintype.card V : ℝ) * ∑ o, c o)) := by
        apply Finset.sum_le_sum; intro ω _
        apply mul_le_mul_of_nonneg_left _ (hρ.1 ω)
        exact mul_le_mul_of_nonneg_left (per_seed_side W c hc hc0 _ _ (henc ω) (hdec ω))
          (inv_nonneg.2 hM.le)
    _ = _ := by rw [← Finset.sum_mul, hρ.2, one_mul, div_eq_inv_mul]

/-- A side observation the sender cannot influence costs nothing: the bound is the original |V| / |M|. -/
theorem side_bound_uninfluenced {Ω M V S O : Type} [Fintype Ω] [Fintype M] [Fintype V] [Fintype S] [Fintype O]
    [Nonempty M] (ρ : Ω → ℝ) (w : O → ℝ) (hw : IsDist w)
    (enc : Ω → M → V × S → ℝ) (dec : Ω → V × O → M → ℝ)
    (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω y, IsDist (dec ω y)) :
    sideSuccess ρ (fun _ => w) enc dec ≤ (Fintype.card V : ℝ) / (Fintype.card M : ℝ) := by
  have h := side_bound ρ (fun _ => w) w (fun _ _ => le_rfl) hw.1 enc dec hρ henc hdec
  rwa [hw.2, mul_one] at h

/-- The trivial certificate: an arbitrary side observation acts at worst like |O| extra noiseless views. -/
theorem side_bound_trivial {Ω M V S O : Type} [Fintype Ω] [Fintype M] [Fintype V] [Fintype S] [Fintype O]
    [Nonempty M] (ρ : Ω → ℝ) (W : S → O → ℝ) (hW : ∀ s, IsDist (W s))
    (enc : Ω → M → V × S → ℝ) (dec : Ω → V × O → M → ℝ)
    (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω y, IsDist (dec ω y)) :
    sideSuccess ρ W enc dec ≤ (Fintype.card V : ℝ) * (Fintype.card O : ℝ) / (Fintype.card M : ℝ) := by
  have hle1 : ∀ s o, W s o ≤ 1 := fun s o => by
    have : W s o ≤ ∑ o', W s o' :=
      Finset.single_le_sum (f := W s) (fun o' _ => (hW s).1 o') (Finset.mem_univ o)
    linarith [(hW s).2]
  have h := side_bound ρ W (fun _ => 1) hle1 (fun _ => zero_le_one) enc dec hρ henc hdec
  simpa using h

/-- Certificates multiply over independent per-episode kernels: if c e dominates W e, then o ↦ ∏ c e (o e) dominates
the product kernel, and its total mass is ∏_e Σ_o c e o. -/
theorem dom_pi {E : ℕ} {S O : Fin E → Type} [∀ e, Fintype (O e)]
    (W : (e : Fin E) → S e → O e → ℝ) (c : (e : Fin E) → O e → ℝ)
    (hW0 : ∀ e s o, 0 ≤ W e s o) (hc : ∀ e s o, W e s o ≤ c e o) :
    (∀ (s : (e : Fin E) → S e) (o : (e : Fin E) → O e), ∏ e, W e (s e) (o e) ≤ ∏ e, c e (o e)) ∧
      ∑ o : ((e : Fin E) → O e), ∏ e, c e (o e) = ∏ e, ∑ o, c e o := by
  refine ⟨fun s o => Finset.prod_le_prod₀ (fun e _ => hW0 e (s e) (o e)) (fun e _ => hc e (s e) (o e)), ?_⟩
  exact (Finset.prod_univ_sum (fun e => (Finset.univ : Finset (O e))) (fun e o => c e o)).symm.trans
    (by simp)

/-- **Reduction.** The side model is an instance of the plain covert model with view V × O. -/
theorem side_as_covert {Ω M V S O : Type} [Fintype Ω] [Fintype M] [Fintype V] [Fintype S] [Fintype O]
    (ρ : Ω → ℝ) (W : S → O → ℝ) (enc : Ω → M → V × S → ℝ) (dec : Ω → V × O → M → ℝ) :
    sideSuccess ρ W enc dec =
      successProb ρ (fun ω m y => ∑ s, enc ω m (y.1, s) * W s y.2) dec := by
  unfold sideSuccess successProb
  apply Finset.sum_congr rfl; intro ω _
  congr 2
  apply Finset.sum_congr rfl; intro m _
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro v _
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro o _
  ring

/-- Binary symmetric side channel with crossover q ≤ 1/2: Σ_o max_s W s o = 2(1 − q). -/
def bsc (q : ℝ) : Bool → Bool → ℝ := fun s o => if s = o then 1 - q else q

theorem bsc_dom (q : ℝ) (hq : q ≤ 1 / 2) : ∀ s o, bsc q s o ≤ 1 - q := by
  intro s o; unfold bsc; split_ifs <;> linarith

theorem bsc_dist (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (s : Bool) : IsDist (bsc q s) := by
  refine ⟨fun o => ?_, ?_⟩
  · unfold bsc; split_ifs <;> linarith
  · cases s <;> simp [bsc]

#print axioms per_seed_side
#print axioms side_bound
#print axioms side_bound_uninfluenced
#print axioms side_bound_trivial
#print axioms dom_pi
#print axioms side_as_covert
#print axioms bsc_dom

end ControlStack.SideChannel
