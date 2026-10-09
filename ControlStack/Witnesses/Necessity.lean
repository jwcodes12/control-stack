/-
Missing necessity witnesses (circle consultation 2026-10-08, reviews/circle-consult-2026-10-08/synthesis.md).

Each theorem shows that ONE specific premise cannot simply be dropped: without it, the bound that used it fails on an
explicit instance. A witness shows that dropping the premise outright breaks the bound. It does not show that the premise is
necessary in every weaker form (see NECESSITY.md for the exact scope of each witness).

- `seed_secret_breaks_covert`: `covert_bound` assumes the secret is independent of the shared seed. If the secret is
  a function of the seed, a decoder that sees NOTHING (|V| = 1) recovers it with certainty, versus the bound 1/|M|.
- `correlated_lifetimes_break_gate`: `false_pass_le` assumes independent lifetimes. With every lifetime completing with
  marginal probability 9/10 but all lifetimes perfectly correlated, the gate passes with probability 9/10, not ≤ 1/80.
- `marginal_certs_dont_compose`: per-channel certificates do not multiply. Two side outputs R and R xor m each have
  the same law for both values of the secret bit m (proved), yet together they reveal m with certainty (success 1,
  proved). The certificate masses (1 alone, 2 for the second given the first) are prose arithmetic, not Lean. Composition needs the joint or sequential domination of `Leakage.seq_transfer`
  (the second output's certificate given the first has mass 2).
- `shared_score_product_unsound` (ILLUSTRATION, not a witness against a stack theorem; adversarial review
  2026-10-08): two layers fired by the same score miss together w.p. 1/10, not 1/100. This is just P(A ∩ A) = P(A).
  The stack-level counterpart is `ComposeBlindSpot` and the fresh-coins premise of `ComposeGame`.
-/
import ControlStack.CovertChannel
import ControlStack.ScenarioAUsefulness

namespace ControlStack.Necessity

open Finset ControlStack.Covert

/-! ## Secret independence -/

/-- success with a JOINT law q on (seed, secret): Σ q(ω,m) Σ_v enc(v|ω,m) dec(m|ω,v) -/
noncomputable def jointSuccess {Ω M V : Type} [Fintype Ω] [Fintype M] [Fintype V]
    (q : Ω → M → ℝ) (enc : Ω → M → V → ℝ) (dec : Ω → V → M → ℝ) : ℝ :=
  ∑ ω, ∑ m, q ω m * ∑ v, enc ω m v * dec ω v m

/-- the joint form reduces to `successProb` when the secret is uniform and independent of the seed -/
theorem jointSuccess_indep {Ω M V : Type} [Fintype Ω] [Fintype M] [Fintype V]
    (ρ : Ω → ℝ) (enc : Ω → M → V → ℝ) (dec : Ω → V → M → ℝ) :
    jointSuccess (fun ω _ => ρ ω * (Fintype.card M : ℝ)⁻¹) enc dec = successProb ρ enc dec := by
  unfold jointSuccess successProb
  apply Finset.sum_congr rfl; intro ω _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro m _; ring

/-- **Seed-correlated secret.** The secret equals the shared seed (uniform on M, |M| ≥ 2); the view is a single
constant value. The decoder outputs its seed and succeeds with probability 1, strictly above what `covert_bound`
gives for an independent secret, |V|/|M| = 1/|M| < 1 (`jointSuccess_indep` ties the joint form to `successProb`).
This is the extreme case. Partial correlation (the secret equals the seed with probability α) is not treated
(adversarial review D4). -/
theorem seed_secret_breaks_covert {M : Type} [Fintype M] [DecidableEq M] (hM : 2 ≤ Fintype.card M) :
    jointSuccess (fun (ω m : M) => if ω = m then (Fintype.card M : ℝ)⁻¹ else 0)
      (fun (_ _ : M) (_ : Unit) => (1 : ℝ)) (fun (ω : M) (_ : Unit) (m : M) => if m = ω then (1 : ℝ) else 0) = 1 ∧
    (Fintype.card Unit : ℝ) / (Fintype.card M : ℝ) < 1 := by
  have hM0 : (0 : ℝ) < (Fintype.card M : ℝ) := by exact_mod_cast (by omega : 0 < Fintype.card M)
  have hM' : (Fintype.card M : ℝ) ≠ 0 := hM0.ne'
  refine ⟨?_, ?_⟩
  · unfold jointSuccess
    simp only [Fintype.univ_unit, Finset.sum_singleton, one_mul]
    have : ∀ ω : M, ∑ m, (if ω = m then (Fintype.card M : ℝ)⁻¹ else 0) * (if m = ω then 1 else 0)
        = (Fintype.card M : ℝ)⁻¹ := by
      intro ω
      rw [Finset.sum_eq_single ω]
      · simp
      · intro m _ hm; simp [Ne.symm hm]
      · simp
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  · rw [Fintype.card_unit, Nat.cast_one, div_lt_one hM0]
    exact_mod_cast (by omega : 1 < Fintype.card M)

/-! ## Independent lifetimes -/

/-- the comonotone law on 64 lifetimes: all complete (prob p) or none complete (prob 1 − p) -/
noncomputable def comono (p : ℝ) (x : Fin 64 → Bool) : ℝ :=
  (if x = fun _ => true then p else 0) + (if x = fun _ => false then 1 - p else 0)

/-- number of completed lifetimes -/
def count (x : Fin 64 → Bool) : ℕ := (univ.filter fun i => x i = true).card

/-- the comonotone law is a probability distribution for p ∈ [0, 1] (review D13) -/
theorem comono_dist (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : IsDist (comono p) := by
  refine ⟨fun x => ?_, ?_⟩
  · unfold comono; split_ifs <;> linarith
  · unfold comono
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp

theorem comono_marginal (p : ℝ) (i : Fin 64) :
    ∑ x, comono p x * (if x i = true then 1 else 0) = p := by
  unfold comono
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

/-- **Correlated lifetimes break the gate's validity.** Every lifetime completes with marginal probability 9/10 (at the
floor), yet the gate (≥ 63 of 64 complete) passes with probability 9/10, not ≤ 1/80 as `false_pass_le` gives under
independence. -/
theorem correlated_lifetimes_break_gate :
    (∀ i : Fin 64, ∑ x, comono (9 / 10) x * (if x i = true then 1 else 0) = 9 / 10) ∧
    ∑ x, comono (9 / 10) x * (if 63 ≤ count x then 1 else 0) = 9 / 10 ∧
    ScenarioAUsefulness.passProb (9 / 10) ≤ 1 / 80 ∧
    (1 : ℝ) / 80 < 9 / 10 := by
  refine ⟨fun i => comono_marginal _ i, ?_, ScenarioAUsefulness.false_pass_le _ (by norm_num) le_rfl, by norm_num⟩
  unfold comono
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  have h1 : count (fun _ => true) = 64 := by simp [count]
  have h0 : count (fun _ => false) = 0 := by simp [count]
  simp [h1, h0]

/-! ## Per-channel certificates do not compose -/

/-- law of the two side outputs (o₁, o₂) = (r, r xor m) given the secret bit m, with r a fresh uniform bit -/
noncomputable def xorLaw (m : Bool) (o : Bool × Bool) : ℝ := if o.2 = xor o.1 m then 1 / 2 else 0

/-- **Marginal certificates do not compose.** Each output alone has the same law for both secrets (so its least
certificate has mass 1: it is useless alone), yet the decoder `o₁ xor o₂` recovers a uniform secret bit with
probability 1, twice the blind value 1/2. -/
theorem marginal_certs_dont_compose :
    (∀ m b, ∑ o : Bool × Bool, xorLaw m o * (if o.1 = b then 1 else 0) = 1 / 2) ∧
    (∀ m b, ∑ o : Bool × Bool, xorLaw m o * (if o.2 = b then 1 else 0) = 1 / 2) ∧
    (1 / 2 : ℝ) * ∑ m : Bool, ∑ o : Bool × Bool, xorLaw m o * (if xor o.1 o.2 = m then 1 else 0) = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> (simp [xorLaw, Fintype.sum_prod_type]; try norm_num)

/-! ## Layers driven by one score -/

/-- an attack's score is high (prob 9/10) or low (prob 1/10); both layers fire exactly on a high score -/
noncomputable def scoreLaw (high : Bool) : ℝ := if high then 9 / 10 else 1 / 10

/-- **Shared-score layers do not multiply.** Each layer misses with probability 1/10, but both miss together with
probability 1/10, ten times the independent product 1/100. -/
theorem shared_score_product_unsound :
    (∑ s : Bool, scoreLaw s * (if s = false then 1 else 0)) = 1 / 10 ∧
    (∑ s : Bool, scoreLaw s * (if s = false ∧ s = false then 1 else 0)) = 1 / 10 ∧
    (1 / 10 : ℝ) * (1 / 10) < 1 / 10 := by
  refine ⟨?_, ?_, by norm_num⟩ <;> simp [scoreLaw]

end ControlStack.Necessity

#print axioms ControlStack.Necessity.seed_secret_breaks_covert
#print axioms ControlStack.Necessity.jointSuccess_indep
#print axioms ControlStack.Necessity.comono_dist
#print axioms ControlStack.Necessity.correlated_lifetimes_break_gate
#print axioms ControlStack.Necessity.marginal_certs_dont_compose
#print axioms ControlStack.Necessity.shared_score_product_unsound

/-! ## Audit budget consumed by false positives (first-come, score-triggered auditing) -/

namespace ControlStack.Necessity

/-- first-come auditing: round i is audited iff it is flagged and fewer than B earlier rounds were flagged -/
def audited {N : ℕ} (B : ℕ) (flags : Fin N → Bool) (i : Fin N) : Bool :=
  flags i && decide ((Finset.univ.filter (fun j : Fin N => j < i ∧ flags j = true)).card < B)

/-- **Exhaustion.** If at least B rounds before every attack round were flagged (e.g. honest false positives), no
attack round is audited, whatever the attack's own flags. -/
theorem exhausted_no_audit {N : ℕ} (B : ℕ) (flags : Fin N → Bool) (A : Finset (Fin N))
    (h : ∀ i ∈ A, B ≤ (Finset.univ.filter (fun j : Fin N => j < i ∧ flags j = true)).card) :
    ∀ i ∈ A, audited B flags i = false := by
  intro i hi
  simp [audited, Nat.not_lt.2 (h i hi)]

/-- flags on Fin 4 from the three honest flags; the attack (round 3) is always flagged (a perfect monitor) -/
def flagsOf (b : Bool × Bool × Bool) : Fin 4 → Bool := ![b.1, b.2.1, b.2.2, true]

theorem audited_last (b : Bool × Bool × Bool) :
    audited 1 (flagsOf b) 3 = (!b.1 && !b.2.1 && !b.2.2) := by
  rcases b with ⟨_ | _, _ | _, _ | _⟩ <;> decide

/-- **Policy comparison, not a premise witness** (adversarial review D3). N = 4 rounds, budget B = 1, one attack step in the last
round, a monitor that flags every attack, and three honest rounds that each raise a false positive w.p. 1/2
(uniform over the 8 patterns). First-come auditing lets the attack survive with probability 7/8. A hidden uniformly
random schedule of the same size (`AuditBudget`, `Leakage.audit_adaptive_hidden`) gives 3/4. The comparison is
between two MECHANISMS at one false-positive rate: at rate 0 the same first-come policy catches this attack
(survival 0 < 3/4). What is shown is that flag-triggered first-come auditing can be exploited by an attacker who
waits for the budget to run out. The underlying premise is that audit allocation is independent of the attacker's
timing. -/
theorem fp_exhaustion_breaks_audit :
    (∑ b : Bool × Bool × Bool, (1 / 8 : ℚ) * (if audited 1 (flagsOf b) 3 = false then 1 else 0)) = 7 / 8 ∧
    (Nat.choose 3 1 : ℚ) / Nat.choose 4 1 = 3 / 4 := by
  refine ⟨?_, by norm_num [Nat.choose]⟩
  simp only [audited_last, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num

end ControlStack.Necessity

#print axioms ControlStack.Necessity.exhausted_no_audit
#print axioms ControlStack.Necessity.fp_exhaustion_breaks_audit
