/-
Scenario A, derived from the gateway core (fixes for audit `reviews/codex-lean-audit-2026-10-08.md`, §1).

`ScenarioARepair` posits the per-episode view carrier `View := Option (Fin 8)` and the lifetime transcript
`Fin 5 → View` directly. This file ties both to `GatewayCore` and makes the fixed-episode-count premise explicit.

Proved (standard axioms only):

Part 1 — the 9-view carrier is the core gateway's reachable view set.
- `card_epPrefix`: for the core gateway with one channel (`C = 1`), schema `Fin 8` and one slot, the prefix tuples
  `Prefixes (fun _ => Fin 8) (fun _ => 1)` number exactly 9.
- `prefixEquiv : EpPrefix ≃ ScenarioARepair.View`, whose forward map is "read channel 0, slot 0 of `embedAll p`"
  (`prefixEquiv_apply`), so the equivalence is the gateway's own delivery map.
- `embedAll_injective`, `embedAll_surjective`, `reachable_eq_univ`: with one slot `embedAll` is a bijection onto the
  core `View`, so every core view is reachable; `epView_card`: the core view type itself has 9 elements.
- `delivered_view_coord`: every delivered final view of the core gateway (any raw trace) is `embedAll` of the prefix
  tuple `prefixEquiv.symm (v 0 0)`, i.e. the delivered view is losslessly the `Option (Fin 8)` value.
- `transcriptEquiv : ScenarioARepair.Transcript ≃ (Fin 5 → EpPrefix)`.
- `lifetime_bound_prefixes`: carrier-level lifetime bound with `V e = EpPrefix` for five episodes (via
  `covert_bound_lifetime`): P ≤ 59049 / 2^32 ≤ 2^-16.
- `five_episode_core_bound`: end-to-end form. The encoder is any law on five raw event traces of the core gateway
  (each of length L), the decoder sees only the five delivered final views (`finalView ∘ runG`): P ≤ 59049/2^32 ≤ 2^-16.

Part 2 — the fixed-five-episode premise is load-bearing.
- `card_varObs`: the variable-count observation set `(j : Fin 6) × (Fin j → Option (Fin 8))` has 66430 = Σ_{j≤5} 9^j
  elements; `varObs_gt`: 66430 > 2^16.
- `varObs_attain`: an explicit deterministic encoder/decoder pair (built from `attain_embedding` with an injection
  `VarObs ↪ Fin (2^32)`) whose encoder and decoder laws are genuine distributions and whose success is exactly
  66430 / 2^32 > 2^-16; `varObs_breaks_target` packages this as an existential counterexample to the 2^-16 target.
  So if the receiver can observe a variable episode count j ≤ 5, the 2^-16 target fails.

Remains assumed (not proved here): the receiver observes nothing but the five delivered views (no count, timing or
side channel); the deployment always runs exactly five episodes, delivering failed/absent episodes as the blank view;
the secret is uniform and independent of the shared seed; the Python gateway refines `GatewayCore`
(`python_refines_model`); the shared seed space Ω is finite; the raw payload alphabet R is finite (and, as in
`GatewayCore.core_bound`, a `Fintype (Ev 1 R)` instance is taken as a parameter); each episode's raw trace has a fixed
length L, as in `core_bound`.
-/
import ControlStack.GatewayCore
import ControlStack.ScenarioARepair

namespace ControlStack.ScenarioACore

open ControlStack.Covert ControlStack.GatewayModel ControlStack.GatewayCore

/-! ### Part 1: the per-episode carrier from the core gateway -/

/-- prefix tuples of the SC-01 core gateway: one channel, schema `Fin 8`, one slot -/
abbrev EpPrefix := Prefixes (C := 1) (fun _ => Fin 8) (fun _ => 1)

/-- the core gateway's delivered view type for the same configuration -/
abbrev EpView := GatewayCore.View (C := 1) (fun _ => Fin 8) (fun _ => 1)

/-- **Nine reachable prefix tuples per episode.** -/
theorem card_epPrefix : Fintype.card EpPrefix = 9 := by
  rw [card_prefixes]
  simpa [Fintype.card_fin] using sc01_episode_views

/-- the core view type itself has 9 elements -/
theorem epView_card : Fintype.card EpView = 9 := by
  simp [EpView, GatewayCore.View, Fintype.card_pi, Fintype.card_option, Fintype.card_fin]

/-- read the single delivered cell (channel 0, slot 0) of a prefix tuple's embedding -/
def prefixToView (p : EpPrefix) : ScenarioARepair.View := embedAll p 0 0

/-- the prefix tuple with no accepted value (`none`) or one accepted value `x` (`some x`) -/
def viewToPrefix : ScenarioARepair.View → EpPrefix
  | none => fun _ => ⟨0, fun i => i.elim0⟩
  | some x => fun _ => ⟨1, fun _ => x⟩

lemma prefixToView_viewToPrefix (o : ScenarioARepair.View) : prefixToView (viewToPrefix o) = o := by
  cases o <;> simp [prefixToView, viewToPrefix, embedAll, embedPrefix]

lemma viewToPrefix_prefixToView (p : EpPrefix) : viewToPrefix (prefixToView p) = p := by
  funext c
  have hc : c = 0 := Subsingleton.elim _ _
  subst hc
  unfold prefixToView embedAll
  generalize p 0 = q
  obtain ⟨⟨j, hj⟩, v⟩ := q
  interval_cases j
  · simp only [embedPrefix]
    exact Sigma.ext rfl (heq_of_eq (funext fun i => i.elim0))
  · simp only [embedPrefix, Fin.val_zero, Nat.zero_lt_one, dite_true, viewToPrefix]
    refine Sigma.ext rfl (heq_of_eq (funext fun i => ?_))
    show v ⟨0, _⟩ = v i
    have hi : (i : ℕ) < 1 := i.isLt
    congr 1
    exact Fin.ext (by simp only; omega)

/-- **The 9-view carrier of `ScenarioARepair` is the core gateway's prefix set.** -/
def prefixEquiv : EpPrefix ≃ ScenarioARepair.View where
  toFun := prefixToView
  invFun := viewToPrefix
  left_inv := viewToPrefix_prefixToView
  right_inv := prefixToView_viewToPrefix

/-- the equivalence is the gateway's delivery map, read at channel 0, slot 0 -/
theorem prefixEquiv_apply (p : EpPrefix) : prefixEquiv p = embedAll p 0 0 := rfl

/-- a core view is determined by its single cell -/
lemma epView_ext (v w : EpView) (h : v 0 0 = w 0 0) : v = w := by
  funext c i
  have hc : c = 0 := Subsingleton.elim _ _
  have hi : i = 0 := Subsingleton.elim _ _
  subst hc hi
  exact h

/-- every core view is the embedding of the prefix tuple read off its cell -/
theorem embedAll_viewToPrefix (v : EpView) : embedAll (prefixEquiv.symm (v 0 0)) = v :=
  epView_ext _ _ (prefixToView_viewToPrefix (v 0 0))

/-- with one slot, `embedAll` is onto the core view type -/
theorem embedAll_surjective : Function.Surjective (embedAll (C := 1) (S := fun _ => Fin 8) (slots := fun _ => 1)) :=
  fun v => ⟨_, embedAll_viewToPrefix v⟩

/-- `embedAll` is injective (it factors the equivalence) -/
theorem embedAll_injective : Function.Injective (embedAll (C := 1) (S := fun _ => Fin 8) (slots := fun _ => 1)) := by
  intro p q h
  have : prefixEquiv p = prefixEquiv q := by rw [prefixEquiv_apply, prefixEquiv_apply, h]
  exact prefixEquiv.injective this

/-- **Exact reachable view set**: every one of the 9 core views is reachable, and only those. -/
theorem reachable_eq_univ :
    Set.range (embedAll (C := 1) (S := fun _ => Fin 8) (slots := fun _ => 1)) = Set.univ :=
  Set.range_eq_univ.mpr embedAll_surjective

/-- **Delivered views are the `Option (Fin 8)` value.** For any raw trace of the SC-01 core gateway, the delivered final
view is the embedding of the prefix tuple that `prefixEquiv` assigns to its single cell. -/
theorem delivered_view_coord {R : Type} (valid : (c : Fin 1) → R → Option (Fin 8)) (tr : List (Ev 1 R)) :
    finalView (runG valid (init (S := fun _ => Fin 8) (slots := fun _ => 1)) tr) =
      embedAll (prefixEquiv.symm
        (finalView (runG valid (init (S := fun _ => Fin 8) (slots := fun _ => 1)) tr) 0 0)) :=
  (embedAll_viewToPrefix _).symm

/-- the five-episode transcript of `ScenarioARepair` is the five-fold product of core prefix sets -/
def transcriptEquiv : ScenarioARepair.Transcript ≃ (Fin 5 → EpPrefix) :=
  Equiv.piCongrRight fun _ => prefixEquiv.symm

theorem card_five_prefixes : Fintype.card (Fin 5 → EpPrefix) = 59049 := by
  rw [Fintype.card_fun, card_epPrefix, Fintype.card_fin]
  norm_num

/-- **Carrier-level lifetime bound.** Five episodes, each observed as a reachable core prefix tuple. -/
theorem lifetime_bound_prefixes {Ω : Type} [Fintype Ω] (ρ : Ω → ℝ)
    (enc : Ω → Fin (2 ^ 32) → (Fin 5 → EpPrefix) → ℝ) (dec : Ω → (Fin 5 → EpPrefix) → Fin (2 ^ 32) → ℝ)
    (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) :
    successProb ρ enc dec ≤ (59049 : ℝ) / 2 ^ 32 ∧ (59049 : ℝ) / 2 ^ 32 ≤ 1 / 2 ^ 16 := by
  refine ⟨?_, by norm_num⟩
  have h := covert_bound_lifetime (M := Fin (2 ^ 32)) (fun _ : Fin 5 => EpPrefix) ρ enc dec hρ henc hdec
  simp only [card_epPrefix, Fintype.card_fin] at h
  norm_num at h ⊢
  exact h

/-- the five delivered views of five raw core traces -/
def lifetimeView {R : Type} (valid : (c : Fin 1) → R → Option (Fin 8)) {L : ℕ} (tr : Fin 5 → Fin L → Ev 1 R) :
    Fin 5 → EpView :=
  fun e => finalView (runG valid (init (S := fun _ => Fin 8) (slots := fun _ => 1)) (List.ofFn (tr e)))

/-- **End-to-end five-episode bound for the core gateway.** Any shared seed, any randomised adaptive encoder of five
raw event traces (each of length L) of the SC-01 core gateway, any decoder of the five delivered final views:
P(recover a uniform 32-bit secret) ≤ 59049 / 2^32 ≤ 2^-16. -/
theorem five_episode_core_bound {Ω R : Type} [Fintype Ω] [Fintype R] [Fintype (Ev 1 R)]
    (valid : (c : Fin 1) → R → Option (Fin 8)) (L : ℕ)
    (ρ : Ω → ℝ) (enc : Ω → Fin (2 ^ 32) → (Fin 5 → Fin L → Ev 1 R) → ℝ)
    (dec : Ω → (Fin 5 → EpView) → Fin (2 ^ 32) → ℝ)
    (hρ : IsDist ρ) (henc : ∀ ω m, IsDist (enc ω m)) (hdec : ∀ ω v, IsDist (dec ω v)) :
    successProb ρ enc (fun ω tr m => dec ω (lifetimeView valid tr) m) ≤ (59049 : ℝ) / 2 ^ 32 ∧
      (59049 : ℝ) / 2 ^ 32 ≤ 1 / 2 ^ 16 := by
  classical
  refine ⟨?_, by norm_num⟩
  set pv : (Fin 5 → Fin L → Ev 1 R) → (Fin 5 → EpPrefix) := fun tr e =>
    Classical.choose (view_reachable valid (List.ofFn (tr e)))
  have hview : ∀ tr, lifetimeView valid tr = fun e => embedAll (pv tr e) := fun tr => by
    funext e
    exact (Classical.choose_spec (view_reachable valid (List.ofFn (tr e)))).symm
  have hpush : ∀ ω m, (∑ tr, enc ω m tr * dec ω (lifetimeView valid tr) m) =
      ∑ p, push pv (enc ω m) p * dec ω (fun e => embedAll (p e)) m := by
    intro ω m
    unfold push
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun tr _ => ?_
    rw [Finset.sum_eq_single (pv tr)]
    · simp [hview tr]
    · intro p _ hp; simp [Ne.symm hp]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h := covert_bound ρ (fun ω m => push pv (enc ω m)) (fun ω p => dec ω (fun e => embedAll (p e))) hρ
    (fun ω m => push_dist _ _ (henc ω m)) (fun ω p => hdec ω _)
  unfold successProb at h ⊢
  simp_rw [hpush]
  refine le_trans h (le_of_eq ?_)
  rw [card_five_prefixes, Fintype.card_fin]
  norm_num

/-! ### Part 2: a variable, observable episode count breaks the 2^-16 target -/

/-- observations when the receiver sees a variable number j ≤ 5 of episode views -/
abbrev VarObs := (j : Fin 6) × (Fin j → ScenarioARepair.View)

/-- **Σ_{j ≤ 5} 9^j = 66430.** -/
theorem card_varObs : Fintype.card VarObs = 66430 := by
  simp only [VarObs, ScenarioARepair.View, Fintype.card_sigma, Fintype.card_fun, Fintype.card_option,
    Fintype.card_fin]
  rfl

/-- 66430 > 2^16 -/
theorem varObs_gt : (2 : ℕ) ^ 16 < 66430 := by norm_num

instance : Nonempty VarObs := ⟨⟨0, fun i => i.elim0⟩⟩

/-- an injection of the variable-count observations into the 32-bit secrets -/
noncomputable def varObsEmbed : VarObs → Fin (2 ^ 32) :=
  fun o => Fin.castLE (by norm_num) (finCongr card_varObs (Fintype.equivFin VarObs o))

theorem varObsEmbed_injective : Function.Injective varObsEmbed := by
  intro a b h
  unfold varObsEmbed at h
  exact (Fintype.equivFin VarObs).injective ((finCongr card_varObs).injective (Fin.castLE_injective _ h))

/-- the attaining encoder of `attain_embedding`: send `e⁻¹ m` if m is in the image of `e`, else a fixed observation -/
noncomputable def attainEnc {M V : Type} [Fintype V] [DecidableEq M] [DecidableEq V] [Nonempty V] (e : V → M) :
    Unit → M → V → ℝ :=
  fun _ m v => if (∃ w, e w = m) then (if e v = m then 1 else 0) else (if v = Classical.arbitrary V then 1 else 0)

/-- the attaining decoder of `attain_embedding`: decode by `e` -/
def attainDec {M V : Type} [DecidableEq M] (e : V → M) : Unit → V → M → ℝ :=
  fun _ v m => if m = e v then 1 else 0

lemma attainEnc_dist {M V : Type} [Fintype V] [DecidableEq M] [DecidableEq V] [Nonempty V] (e : V → M) (he : Function.Injective e) (m : M) :
    IsDist (attainEnc e () m) := by
  unfold attainEnc
  refine ⟨fun v => by dsimp only; split_ifs <;> norm_num, ?_⟩
  by_cases hm : ∃ w, e w = m
  · obtain ⟨w, rfl⟩ := hm
    have hx : ∃ w', e w' = e w := ⟨w, rfl⟩
    simp only [hx, ite_true]
    rw [Finset.sum_eq_single w]
    · simp
    · intro v _ hv; have : e v ≠ e w := fun h => hv (he h); simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  · simp [hm]

lemma attainDec_dist {M V : Type} [Fintype M] [DecidableEq M] (e : V → M) (v : V) : IsDist (attainDec e () v) := by
  unfold attainDec
  refine ⟨fun m => by dsimp only; split_ifs <;> norm_num, ?_⟩
  simp

/-- **Attainment for variable-count observations.** The deterministic code that sends the observation `e⁻¹ m`
(with `e = varObsEmbed`) and decodes by `e` is a genuine encoder/decoder pair and recovers a uniform 32-bit secret
with probability exactly 66430 / 2^32, which exceeds 2^-16. -/
theorem varObs_attain :
    (∀ m, IsDist (attainEnc varObsEmbed () m)) ∧ (∀ v, IsDist (attainDec varObsEmbed () v)) ∧
      successProb (Ω := Unit) (fun _ => 1) (attainEnc varObsEmbed) (attainDec varObsEmbed) = (66430 : ℝ) / 2 ^ 32 ∧
      (1 : ℝ) / 2 ^ 16 < (66430 : ℝ) / 2 ^ 32 := by
  refine ⟨attainEnc_dist _ varObsEmbed_injective, attainDec_dist _, ?_, by norm_num⟩
  have h := attain_embedding (M := Fin (2 ^ 32)) varObsEmbed varObsEmbed_injective
  rw [card_varObs, Fintype.card_fin] at h
  refine h.trans ?_
  push_cast
  norm_num

/-- **The target depends on the fixed count.** No bound of the form `success ≤ 1 / 2^16` holds uniformly over
encoder/decoder pairs on the variable-count observation set. -/
theorem varObs_breaks_target :
    ∃ (enc : Unit → Fin (2 ^ 32) → VarObs → ℝ) (dec : Unit → VarObs → Fin (2 ^ 32) → ℝ),
      IsDist (fun _ : Unit => (1 : ℝ)) ∧ (∀ ω m, IsDist (enc ω m)) ∧ (∀ ω v, IsDist (dec ω v)) ∧
        (1 : ℝ) / 2 ^ 16 < successProb (fun _ => 1) enc dec := by
  obtain ⟨h1, h2, h3, h4⟩ := varObs_attain
  refine ⟨attainEnc varObsEmbed, attainDec varObsEmbed, ⟨fun _ => by norm_num, by simp⟩,
    fun _ m => h1 m, fun _ v => h2 v, ?_⟩
  rw [h3]; exact h4

#print axioms card_epPrefix
#print axioms epView_card
#print axioms prefixEquiv
#print axioms prefixEquiv_apply
#print axioms embedAll_surjective
#print axioms embedAll_injective
#print axioms reachable_eq_univ
#print axioms delivered_view_coord
#print axioms transcriptEquiv
#print axioms card_five_prefixes
#print axioms lifetime_bound_prefixes
#print axioms five_episode_core_bound
#print axioms card_varObs
#print axioms varObs_gt
#print axioms varObs_attain
#print axioms varObs_breaks_target

end ControlStack.ScenarioACore
