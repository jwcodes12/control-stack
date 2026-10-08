import ControlStack.ScenarioARepair
import ControlStack.SideChannel

/-! SC-01 repair design point with a side observation (SideChannel.lean).

`ScenarioARepair.repair_target` (P ≤ 2^-16) assumes the receiver observes only the 5-episode gateway transcript.
With an additional side observation from a fixed kernel with domination mass L = Σ_o c o over the lifetime:
- `repair_side`: P ≤ 59049 · L / 2^32;
- `repair_side_target`: the 2^-16 target survives iff (sufficient direction proved here) L ≤ 65536/59049 ≈ 1.1099;
- `repair_one_bit_attained`: ONE noiseless side bit per lifetime is attained at 2 · 59049 / 2^32 > 2^-16, so the
  current design point does not tolerate even a single clean bit outside the transcript;
- `bsc_lifetime_*`: five independent binary symmetric side bits (one per episode) meet the target at crossover 0.49
  and miss it at 0.48 (domination mass (2(1 − q))^5).
These are model statements; whether the deployment's side kernel has such a certificate is an empirical assumption. -/
namespace ControlStack.ScenarioASide
open ControlStack.Covert ControlStack.SideChannel ControlStack.ScenarioARepair

theorem repair_side {Ω S O : Type} [Fintype Ω] [Fintype S] [Fintype O] (ρ : Ω → ℝ)
    (W : S → O → ℝ) (c : O → ℝ) (hc : ∀ s o, W s o ≤ c o) (hc0 : ∀ o, 0 ≤ c o)
    (enc : Ω → Fin (2 ^ 32) → Transcript × S → ℝ) (dec : Ω → Transcript × O → Fin (2 ^ 32) → ℝ)
    (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω y, IsDist (dec ω y)) :
    sideSuccess ρ W enc dec ≤ 59049 * (∑ o, c o) / 2 ^ 32 := by
  have h := side_bound ρ W c hc hc0 enc dec hρ henc hdec
  rw [transcript_card, Fintype.card_fin] at h
  convert h using 2; push_cast; ring

theorem repair_side_target {Ω S O : Type} [Fintype Ω] [Fintype S] [Fintype O] (ρ : Ω → ℝ)
    (W : S → O → ℝ) (c : O → ℝ) (hc : ∀ s o, W s o ≤ c o) (hc0 : ∀ o, 0 ≤ c o)
    (hL : ∑ o, c o ≤ 65536 / 59049)
    (enc : Ω → Fin (2 ^ 32) → Transcript × S → ℝ) (dec : Ω → Transcript × O → Fin (2 ^ 32) → ℝ)
    (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω y, IsDist (dec ω y)) :
    sideSuccess ρ W enc dec ≤ 1 / 2 ^ 16 := by
  have h := repair_side ρ W c hc hc0 enc dec hρ henc hdec
  calc sideSuccess ρ W enc dec ≤ 59049 * (∑ o, c o) / 2 ^ 32 := h
    _ ≤ 59049 * (65536 / 59049) / 2 ^ 32 := by gcongr
    _ = 1 / 2 ^ 16 := by norm_num

/-- the noiseless one-bit side kernel -/
def idKernel : Bool → Bool → ℝ := fun s o => if s = o then 1 else 0

lemma card_obs : Fintype.card (Transcript × Bool) ≤ 2 ^ 32 := by
  rw [Fintype.card_prod, transcript_card]; norm_num

/-- an injective code for (transcript, side bit) pairs into the secret space -/
noncomputable def emb : Transcript × Bool → Fin (2 ^ 32) :=
  fun y => Fin.castLE card_obs (Fintype.equivFin _ y)

lemma emb_inj : Function.Injective emb := by
  intro a b h
  have := Fin.castLE_injective card_obs h
  exact (Fintype.equivFin _).injective this

open Classical in
/-- **One clean side bit breaks the design point.** With the noiseless one-bit side kernel, the embedding code
recovers the 32-bit secret with probability exactly 2 · 59049 / 2^32, which exceeds 2^-16. -/
theorem repair_one_bit_attained :
    ∃ (enc : Unit → Fin (2 ^ 32) → Transcript × Bool → ℝ) (dec : Unit → Transcript × Bool → Fin (2 ^ 32) → ℝ),
      (∀ ω m, IsDist (enc ω m)) ∧ (∀ ω y, IsDist (dec ω y)) ∧
      sideSuccess (fun _ => (1 : ℝ)) idKernel enc dec = 2 * 59049 / 2 ^ 32 ∧
      (1 : ℝ) / 2 ^ 16 < 2 * 59049 / 2 ^ 32 := by
  set E : Unit → Fin (2 ^ 32) → Transcript × Bool → ℝ := fun _ m v =>
    if (∃ w, emb w = m) then (if emb v = m then 1 else 0)
    else (if v = Classical.arbitrary (Transcript × Bool) then 1 else 0) with hE
  set D : Unit → Transcript × Bool → Fin (2 ^ 32) → ℝ := fun _ v m => if m = emb v then 1 else 0 with hD
  have hEd : ∀ ω m, IsDist (E ω m) := by
    intro ω m
    refine ⟨fun v => by simp only [hE]; split_ifs <;> norm_num, ?_⟩
    simp only [hE]
    split_ifs with h
    · obtain ⟨w, rfl⟩ := h
      rw [Finset.sum_eq_single w]
      · simp
      · intro v _ hv; simp [emb_inj.ne hv]
      · simp
    · simp
  have hDd : ∀ ω v, IsDist (D ω v) := by
    intro ω v
    refine ⟨fun m => by simp only [hD]; split_ifs <;> norm_num, by simp [hD]⟩
  refine ⟨E, D, hEd, hDd, ?_, by norm_num⟩
  rw [side_as_covert]
  have hred : (fun ω m (y : Transcript × Bool) => ∑ s, E ω m (y.1, s) * idKernel s y.2) = E := by
    funext ω m y
    obtain ⟨v, o⟩ := y
    cases o <;> simp [idKernel]
  rw [hred]
  have h := attain_embedding emb emb_inj
  rw [Fintype.card_prod, transcript_card, Fintype.card_bool, Fintype.card_fin] at h
  convert h using 1
  norm_num

/-- five independent binary symmetric side bits, crossover q: domination mass (2(1 − q))^5 -/
theorem bsc_lifetime_ok : (2 * (1 - (49 : ℝ) / 100)) ^ 5 ≤ 65536 / 59049 := by norm_num

theorem bsc_lifetime_fails : (65536 : ℝ) / 59049 < (2 * (1 - (48 : ℝ) / 100)) ^ 5 := by norm_num

#print axioms repair_side
#print axioms repair_side_target
#print axioms repair_one_bit_attained
#print axioms bsc_lifetime_ok
#print axioms bsc_lifetime_fails

end ControlStack.ScenarioASide
