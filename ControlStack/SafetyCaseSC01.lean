/-
SC-01 conditional safety/usefulness case: the Lean conjuncts in one statement (`sc01_case`).

Every assumption that is not a theorem appears as an explicit hypothesis or is listed in
assurance/sc01-safety-case.json and checked by tools/check_sc01_case.sh. In particular:
- SAFETY is conditional on a side-kernel domination certificate with mass ≤ 65536/59049 (≈ 1.11). `bit_refutes`
  shows how a measurement refutes that hypothesis: any side kernel through which a uniform bit is recovered with
  probability p forces every certificate to have mass ≥ 2p, so p > 0.555 already rules out the target;
- USEFULNESS is conditional on independent lifetimes (binomial model);
- the Python gateway and SQLite ledger are related to these models by differential tests and transition models, not
  by a refinement proof.
-/
import ControlStack.ScenarioASide
import ControlStack.ScenarioAUsefulness
import ControlStack.LifetimeLedger
import ControlStack.GatewayCore

namespace ControlStack.SafetyCaseSC01

open ControlStack.Covert ControlStack.SideChannel ControlStack.ScenarioARepair ControlStack.ScenarioASide
  ControlStack.ScenarioAUsefulness ControlStack.LifetimeLedger ControlStack.GatewayCore

/-! ### Ledger: at most five nine-view episodes per lineage -/

lemma step_adm {L : Type} [DecidableEq L] (cap : ℕ) (s : Option (L → ℕ)) (e : Ev L) (a : L × ℕ)
    (h : (step cap s e).2 = some a) : ∃ ℓ k, e = .charge ℓ k ∧ a = (ℓ, k) := by
  cases s <;> cases e <;> simp [step] at h
  case some.charge f ℓ k =>
    split_ifs at h with hk
    exact ⟨ℓ, k, rfl, (Option.some.inj h).symm⟩

lemma run_sizes {L : Type} [DecidableEq L] (cap : ℕ) (K : ℕ) :
    ∀ (es : List (Ev L)) (st : Option (L → ℕ) × List (L × ℕ)),
      (∀ e ∈ es, ∀ ℓ k, e = .charge ℓ k → k = K) → (∀ a ∈ st.2, a.2 = K) →
      ∀ a ∈ (run cap st es).2, a.2 = K
  | [], st, _, h => h
  | e :: es, (s, adm), hes, h => by
      simp only [run]
      apply run_sizes cap K es _ (fun e' he' => hes e' (List.mem_cons_of_mem e he'))
      intro a ha
      rcases List.mem_append.1 ha with ha | ha
      · exact h a ha
      · cases hst : (step cap s e).2 with
        | none => simp [hst] at ha
        | some b =>
          simp [hst] at ha; rw [ha]
          obtain ⟨ℓ, k, rfl, rfl⟩ := step_adm cap s e b hst
          exact hes _ List.mem_cons_self ℓ k rfl

lemma pr_const {L : Type} [DecidableEq L] (ℓ : L) (K : ℕ) (adm : List (L × ℕ)) (h : ∀ a ∈ adm, a.2 = K) :
    pr ℓ adm = K ^ (adm.filter (fun a => a.1 = ℓ)).length := by
  unfold pr
  have : (adm.filter (fun a => a.1 = ℓ)).map Prod.snd = List.replicate (adm.filter (fun a => a.1 = ℓ)).length K := by
    apply List.eq_replicate_iff.2
    refine ⟨by simp, fun b hb => ?_⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hb
    exact h a (List.mem_of_mem_filter ha)
  rw [this, List.prod_replicate]

/-- With cap 2^16 and every charge of size 9, no lineage is ever admitted more than five episodes. -/
theorem ledger_five {L : Type} [DecidableEq L] (es : List (Ev L)) (hes : ∀ e ∈ es, ¬ e.isRestore)
    (h9 : ∀ e ∈ es, ∀ ℓ k, e = .charge ℓ k → k = 9) (ℓ : L) :
    ((run (2 ^ 16) (some (fun _ => 1), []) es).2.filter (fun a => a.1 = ℓ)).length ≤ 5 := by
  have hsafe := ledger_safe (2 ^ 16) (by norm_num) es hes ℓ
  have hs := run_sizes (2 ^ 16) 9 es (some (fun _ => 1), []) h9 (by simp)
  rw [pr_const ℓ 9 _ hs] at hsafe
  by_contra hk
  push Not at hk
  have : 9 ^ 6 ≤ 9 ^ ((run (2 ^ 16) (some (fun _ => 1), []) es).2.filter (fun a => a.1 = ℓ)).length :=
    Nat.pow_le_pow_right (by norm_num) hk
  have : (9 : ℕ) ^ 6 ≤ 2 ^ 16 := le_trans this hsafe
  norm_num at this

/-! ### How a measurement refutes the side-certificate hypothesis -/

/-- If a uniform bit is recovered through the side kernel alone with probability p, every domination certificate of
the kernel has mass ≥ 2p. -/
theorem bit_refutes {Ω S O : Type} [Fintype Ω] [Fintype S] [Fintype O]
    (ρ : Ω → ℝ) (W : S → O → ℝ) (c : O → ℝ) (hc : ∀ s o, W s o ≤ c o) (hc0 : ∀ o, 0 ≤ c o)
    (enc : Ω → Bool → Unit × S → ℝ) (dec : Ω → Unit × O → Bool → ℝ)
    (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω y, IsDist (dec ω y)) :
    2 * sideSuccess ρ W enc dec ≤ ∑ o, c o := by
  have h := side_bound ρ W c hc hc0 enc dec hρ henc hdec
  simp only [Fintype.card_unit, Fintype.card_bool, Nat.cast_one, one_mul, Nat.cast_ofNat] at h
  linarith

theorem refute_threshold : (2 : ℝ) * (5551 / 10000) > 65536 / 59049 := by norm_num

/-! ### The case -/

/-- **SC-01 conditional case.** (1) conditional safety under a side certificate of mass ≤ 65536/59049;
(2) gate validity under the binomial model; (3) the observed endpoint clears the floor; (4) the gateway core's
episode view count is 9 and the five-episode transcript has 59049 values; (5) the ledger admits at most five
nine-view episodes per lineage on every restore-free trace. -/
theorem sc01_case :
    (∀ {Ω S O : Type} [Fintype Ω] [Fintype S] [Fintype O] (ρ : Ω → ℝ) (W : S → O → ℝ) (c : O → ℝ),
      (∀ s o, W s o ≤ c o) → (∀ o, 0 ≤ c o) → ∑ o, c o ≤ 65536 / 59049 →
      ∀ (enc : Ω → Fin (2 ^ 32) → Transcript × S → ℝ) (dec : Ω → Transcript × O → Fin (2 ^ 32) → ℝ),
      IsDist ρ → (∀ ω m, IsDist (enc ω m)) → (∀ ω y, IsDist (dec ω y)) →
      sideSuccess ρ W enc dec ≤ 1 / 2 ^ 16) ∧
    (∀ p : ℝ, 0 ≤ p → p ≤ 9 / 10 → passProb p ≤ 1 / 80) ∧
    (tail 64 (93382 / 100000) ≤ 1 / 80 ∧ (9 : ℝ) / 10 ≤ 93382 / 100000) ∧
    (viewSpace (C := 1) (fun _ => 1) (fun _ => 8) = 9 ∧ Fintype.card Transcript = 9 ^ 5) ∧
    (∀ {L : Type} [DecidableEq L] (es : List (Ev L)), (∀ e ∈ es, ¬ e.isRestore) →
      (∀ e ∈ es, ∀ ℓ k, e = .charge ℓ k → k = 9) →
      ∀ ℓ, ((run (2 ^ 16) (some (fun _ => 1), []) es).2.filter (fun a => a.1 = ℓ)).length ≤ 5) := by
  refine ⟨fun ρ W c hc hc0 hL enc dec hρ henc hdec => repair_side_target ρ W c hc hc0 hL enc dec hρ henc hdec,
    fun p h0 h1 => false_pass_le p h0 h1, ⟨endpoint64.1, endpoints_clear_floor.1.trans endpoints_clear_floor.2⟩,
    ⟨sc01_episode_views, by rw [transcript_card]; norm_num⟩, fun es hes h9 ℓ => ledger_five es hes h9 ℓ⟩

#print axioms ledger_five
#print axioms bit_refutes
#print axioms refute_threshold
#print axioms sc01_case

end ControlStack.SafetyCaseSC01
