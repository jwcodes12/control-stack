/-
Covert-propagation bound for mediated machine channels (CATASTROPHE-SPEC.md).

U holds a uniform secret m ∈ Fin K (K = 2^k). Everything the receiver observes is a single value v in a finite set V
(the whole mediated transcript: n schema messages give V = schema^n, a canonicaliser gives the canonical forms).
U's encoder and the receiver's decoder may share an arbitrary random seed ω (colluding instances share weights and
prompts), may be randomised, and the encoder may be adaptive (any law on transcripts per (ω, m)). Then
  P(decoder recovers m) ≤ |V| / K,
and the identity code attains min(1, |V|/K). With the gateway's budget |V| ≤ 2^16 and K = 2^32, P ≤ 2^-16.
Assumptions carried by the deployment, not this theorem: the receiver observes nothing but v (no other channel, no
timing, fixed message count), and m is independent of ω and of the receiver's inputs.
-/
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi

namespace ControlStack.Covert

open Finset

/-- a probability vector -/
def IsDist {α : Type} [Fintype α] (p : α → ℝ) : Prop := (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

/-- probability that the decoder recovers a uniform secret, averaged over the shared seed -/
noncomputable def successProb {Ω M V : Type} [Fintype Ω] [Fintype M] [Fintype V]
    (ρ : Ω → ℝ) (enc : Ω → M → V → ℝ) (dec : Ω → V → M → ℝ) : ℝ :=
  ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, ∑ v, enc ω m v * dec ω v m)

/-- the per-seed core: Σ_m Σ_v enc(v|m)·dec(m|v) ≤ |V| -/
theorem per_seed_le {M V : Type} [Fintype M] [Fintype V] (enc : M → V → ℝ) (dec : V → M → ℝ)
    (henc : ∀ m, IsDist (enc m)) (hdec : ∀ v, IsDist (dec v)) :
    ∑ m, ∑ v, enc m v * dec v m ≤ (Fintype.card V : ℝ) := by
  have hle1 : ∀ m v, enc m v ≤ 1 := fun m v => by
    have h := (henc m).2
    have : enc m v ≤ ∑ v', enc m v' :=
      Finset.single_le_sum (f := enc m) (fun v' _ => (henc m).1 v') (Finset.mem_univ v)
    linarith
  calc ∑ m, ∑ v, enc m v * dec v m = ∑ v, ∑ m, enc m v * dec v m := Finset.sum_comm
    _ ≤ ∑ v, ∑ m, dec v m := by
        apply Finset.sum_le_sum; intro v _; apply Finset.sum_le_sum; intro m _
        exact mul_le_of_le_one_left ((hdec v).1 m) (hle1 m v)
    _ = ∑ _v : V, (1 : ℝ) := by
        apply Finset.sum_congr rfl; intro v _; exact (hdec v).2
    _ = (Fintype.card V : ℝ) := by simp

/-- **Covert-channel bound.** For every shared-seed law, every (adaptive, randomised) encoder and every randomised
decoder, a uniform secret on M is recovered with probability at most |V| / |M|. -/
theorem covert_bound {Ω M V : Type} [Fintype Ω] [Fintype M] [Fintype V] [Nonempty M]
    (ρ : Ω → ℝ) (enc : Ω → M → V → ℝ) (dec : Ω → V → M → ℝ)
    (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) :
    successProb ρ enc dec ≤ (Fintype.card V : ℝ) / (Fintype.card M : ℝ) := by
  unfold successProb
  have hM : (0 : ℝ) < (Fintype.card M : ℝ) := by exact_mod_cast Fintype.card_pos
  calc ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * ∑ m, ∑ v, enc ω m v * dec ω v m)
      ≤ ∑ ω, ρ ω * ((Fintype.card M : ℝ)⁻¹ * (Fintype.card V : ℝ)) := by
        apply Finset.sum_le_sum; intro ω _
        apply mul_le_mul_of_nonneg_left _ (hρ.1 ω)
        exact mul_le_mul_of_nonneg_left (per_seed_le _ _ (henc ω) (hdec ω)) (inv_nonneg.2 hM.le)
    _ = (Fintype.card V : ℝ) / (Fintype.card M : ℝ) := by
        rw [← Finset.sum_mul, hρ.2, one_mul, div_eq_inv_mul]

/-- Product channels: n messages over a schema of size s give |V| = s^n, so P ≤ s^n / K. -/
theorem covert_bound_schema {Ω M S : Type} [Fintype Ω] [Fintype M] [Fintype S] [Nonempty M] [DecidableEq S]
    (n : ℕ) (ρ : Ω → ℝ) (enc : Ω → M → (Fin n → S) → ℝ) (dec : Ω → (Fin n → S) → M → ℝ)
    (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) :
    successProb ρ enc dec ≤ (Fintype.card S : ℝ) ^ n / (Fintype.card M : ℝ) := by
  have h := covert_bound ρ enc dec hρ henc hdec
  simpa [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using h

/-- Attainment: when |V| ≥ |M|, an injective code with a matching decoder recovers the secret with probability 1, so the
bound cannot be improved without restricting V. -/
theorem attain_injective {M V : Type} [Fintype M] [Fintype V] [DecidableEq M] [DecidableEq V] [Nonempty M]
    (code : M → V) (decode : V → M) (hinv : ∀ m, decode (code m) = m) :
    successProb (Ω := Unit) (fun _ => 1) (fun _ m v => if v = code m then 1 else 0)
      (fun _ v m => if m = decode v then 1 else 0) = 1 := by
  unfold successProb
  have hM : (Fintype.card M : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have e : ∀ m, (∑ v, (if v = code m then (1 : ℝ) else 0) * (if m = decode v then 1 else 0)) = 1 := by
    intro m
    rw [Finset.sum_eq_single (code m)]
    · simp [hinv m]
    · intro v _ hv; simp [hv]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp only [e, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Fintype.card_unit, one_mul]
  field_simp
  try simp

/-- The design point: 16 schema bits, a 32-bit secret: P ≤ 2^-16. -/
theorem design_point {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ)
    (enc : Ω → Fin (2 ^ 32) → (Fin 16 → Bool) → ℝ) (dec : Ω → (Fin 16 → Bool) → Fin (2 ^ 32) → ℝ)
    (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) :
    successProb ρ enc dec ≤ 1 / 2 ^ 16 := by
  have h := covert_bound_schema 16 ρ enc dec hρ henc hdec
  have e : (Fintype.card Bool : ℝ) ^ 16 / (Fintype.card (Fin (2 ^ 32)) : ℝ) = 1 / 2 ^ 16 := by
    simp [Fintype.card_bool, Fintype.card_fin]; norm_num
  linarith [h, e.le]

#print axioms covert_bound
#print axioms covert_bound_schema
#print axioms attain_injective
#print axioms design_point

end ControlStack.Covert
