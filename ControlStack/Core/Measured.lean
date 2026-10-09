/-
Measured premises: from measurement to certificates (TrustRoot: the most-shared root is `measured_rates`).

(1) The certificate rule. A premise that is a MEASUREMENT CLAIM holds except with probability ≤ δ over the
measurement's own randomness. The setup is a product space Ω_m × Ω_d with law μ_m ⊗ μ_d: the measurement's
randomness is independent of the deployment's.
- If every good measurement outcome ω_m (event G) yields a certificate P_d(bad(ω_m, ·)) ≤ b (the deployment may be
  configured from ω_m), then P(bad) ≤ b + δ jointly (`measured_prod`; quantity form `measured_bound`).
- `ProbCert.ofMeasured` packages this as a Cert rule. The premise moves to the kind
  `measuredWithConfidence procedure δ`, so the ledger records the procedure name and δ. A separate correspondence
  premise records the sampling model: i.i.d. samples from the deployment's law, independent of deployment
  randomness.

(2) A proved one-sided binomial bound, by finite sums.
- n i.i.d. Bernoulli(p) trials form the space `Fin n → Bool` with weight `wB p`.
- `tailP n t p` = P(at least t successes) satisfies the standard recursion (`tailP_succ`).
- It is monotone in p (`tailP_mono`) and decreasing in t (`tailP_anti`).
- Its closed form is `tailP_eq_cf`: Σ_{k ≥ t} C(n,k) p^k (1−p)^{n−k}.
- `cp_valid` (Clopper–Pearson style): for ANY lower-bound rule r_low(s) with r_low(s) = 0 or P_{r_low(s)}(S ≥ s) ≤ δ,
  and for EVERY true p, P_p(p < r_low(S)) ≤ δ.
- `cp_threshold`: the preregistered one-threshold rule "report r₀ if S ≥ s₀" is valid when P_{r₀}(S ≥ s₀) ≤ δ.

(3) Instance. Monitor recall measured as 190 / 200 caught on a held-out attack set.
- `tail_200_190`: P_{9/10}(S ≥ 190) ≤ 1/100, so r_low = 9/10 at δ = 0.01 (exact computation).
- `measured_recall_example`: plugging into the adaptive reserved-audit bound (`ReservedRecall.adaptive_recall_bound`,
  `DamageBound.hyp_geom`) for N = 100, Bh = 10, k = 5, the joint probability (over measurement AND deployment) that
  the gate deploys and the attacker escapes 5 attack rounds is ≤ (91/100)^5 + 1/100 = 6340321451/10^10 ≈ 0.634.

THE PITFALL (per-history vs population). The measurement estimates a POPULATION recall: the catch rate on attacks
drawn like the held-out set. The adaptive theorem needs recall ≥ r for EVERY history. `measured_recall_example`
therefore carries the explicit premise `homogeneous`: the kernel's per-history recall is ≥ the measured population
recall p.
- `population_not_per_history` shows why: recall 1 on 95% of histories and 0 on 5% has population recall 0.95, yet
  an attacker who reaches the 5% stratum always escapes.
- The safe version measures each stratum separately and uses the minimum, with `strata_union` (failure ≤ Σ δ_s).

No novelty: product-space conditioning, the binomial tail and Clopper–Pearson are classical.
-/
import Mathlib.Tactic
import ControlStack.Core.Cert
import ControlStack.Families.F6.DamageBound

namespace ControlStack.Measured

open Finset ControlStack.Cert

/-! ## (1) Measured premises on a product space -/

section Product

variable {Ωm Ωd : Type} [Fintype Ωm] [Fintype Ωd]

/-- **Quantity form.** If a [0,1]-valued quantity f (e.g. the deployment's bad-event probability) is ≤ b on the good
measurement outcomes G, and G fails with probability ≤ δ, then E_m[f] ≤ b + δ. -/
theorem measured_bound (μm : Ωm → ℝ) (hm0 : ∀ ω, 0 ≤ μm ω) (hm1 : ∑ ω, μm ω = 1) (G : Ωm → Prop) (δ b : ℝ)
    (hG : prob μm (fun ω => ¬ G ω) ≤ δ) (hb0 : 0 ≤ b) (f : Ωm → ℝ) (hf1 : ∀ ω, f ω ≤ 1)
    (hfG : ∀ ω, G ω → f ω ≤ b) : ∑ ω, μm ω * f ω ≤ b + δ := by
  classical
  have hterm : ∀ ω, μm ω * f ω ≤ b * μm ω + (if ¬ G ω then μm ω else 0) := by
    intro ω
    by_cases hg : G ω
    · rw [if_neg (not_not.2 hg)]; nlinarith [hfG ω hg, hm0 ω]
    · rw [if_pos hg]; nlinarith [hf1 ω, hm0 ω]
  calc ∑ ω, μm ω * f ω ≤ ∑ ω, (b * μm ω + (if ¬ G ω then μm ω else 0)) := Finset.sum_le_sum fun ω _ => hterm ω
    _ = b + prob μm (fun ω => ¬ G ω) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hm1, mul_one]; unfold prob
        exact congrArg _ (Finset.sum_congr rfl fun ω _ => by split_ifs <;> simp_all)
    _ ≤ b + δ := by linarith

theorem prob_le_one (μ : Ωd → ℝ) (h0 : ∀ ω, 0 ≤ μ ω) (h1 : ∑ ω, μ ω = 1) (A : Ωd → Prop) : prob μ A ≤ 1 := by
  classical
  rw [← h1]; unfold prob
  apply Finset.sum_le_sum; intro ω _; split_ifs; exact le_rfl; exact h0 ω

/-- **Product-space form.** The measurement (law μ_m) is independent of the deployment (law μ_d); the deployment may
be configured from the measurement outcome (bad depends on both). If every good outcome yields
P_d(bad(ω_m, ·)) ≤ b, then the JOINT probability of bad is ≤ b + δ. -/
theorem measured_prod (μm : Ωm → ℝ) (hm0 : ∀ ω, 0 ≤ μm ω) (hm1 : ∑ ω, μm ω = 1)
    (μd : Ωd → ℝ) (hd0 : ∀ ω, 0 ≤ μd ω) (hd1 : ∑ ω, μd ω = 1) (G : Ωm → Prop) (δ b : ℝ)
    (hG : prob μm (fun ω => ¬ G ω) ≤ δ) (hb0 : 0 ≤ b) (bad : Ωm → Ωd → Prop)
    (hcert : ∀ ωm, G ωm → prob μd (bad ωm) ≤ b) :
    prob (fun ω : Ωm × Ωd => μm ω.1 * μd ω.2) (fun ω => bad ω.1 ω.2) ≤ b + δ := by
  classical
  have e : prob (fun ω : Ωm × Ωd => μm ω.1 * μd ω.2) (fun ω => bad ω.1 ω.2) = ∑ a, μm a * prob μd (bad a) := by
    unfold prob
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl; intro a _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro d _
    split_ifs <;> simp
  rw [e]
  exact measured_bound μm hm0 hm1 G δ b hG hb0 _ (fun a => prob_le_one μd hd0 hd1 _) hcert

/-- **The Cert rule.** A certificate that needs a measured premise G becomes a product-space certificate with bound
b + δ. The ledger records the procedure and δ (`measuredWithConfidence`) and the sampling-model correspondence. -/
noncomputable def ProbCert.ofMeasured (μm : Ωm → ℝ) (hm0 : ∀ ω, 0 ≤ μm ω) (hm1 : ∑ ω, μm ω = 1)
    (μd : Ωd → ℝ) (hd0 : ∀ ω, 0 ≤ μd ω) (hd1 : ∑ ω, μd ω = 1) (procedure : String) (δ : ℚ) (G : Ωm → Prop)
    (bad : Ωm → Ωd → Prop) (ps : List Premise) (b : ℝ) (hb0 : 0 ≤ b)
    (hcert : AllHold ps → ∀ ωm, G ωm → prob μd (bad ωm) ≤ b) :
    ProbCert (fun ω : Ωm × Ωd => μm ω.1 * μd ω.2) (fun ω => bad ω.1 ω.2) :=
  ⟨ps ++ [⟨"measured: " ++ procedure, .measuredWithConfidence procedure δ, prob μm (fun ω => ¬ G ω) ≤ δ⟩,
          ⟨"sampling model: " ++ procedure ++ " samples i.i.d. from the deployment law, independent of deployment",
            .correspondence, True⟩],
   b + δ, fun hp => by
    obtain ⟨hps, hm⟩ := hp.append
    obtain ⟨hG, -⟩ := hm.cons
    exact measured_prod μm hm0 hm1 μd hd0 hd1 G δ b hG hb0 bad (hcert hps)⟩

/-- the ledger of `ofMeasured`: the measured premise is recorded with its procedure and δ, plus the sampling-model
correspondence, and the bound is b + δ -/
theorem ofMeasured_ledger (μm : Ωm → ℝ) (hm0 : ∀ ω, 0 ≤ μm ω) (hm1 : ∑ ω, μm ω = 1)
    (μd : Ωd → ℝ) (hd0 : ∀ ω, 0 ≤ μd ω) (hd1 : ∑ ω, μd ω = 1) (procedure : String) (δ : ℚ) (G : Ωm → Prop)
    (bad : Ωm → Ωd → Prop) (ps : List Premise) (b : ℝ) (hb0 : 0 ≤ b)
    (hcert : AllHold ps → ∀ ωm, G ωm → prob μd (bad ωm) ≤ b) :
    let c := ProbCert.ofMeasured μm hm0 hm1 μd hd0 hd1 procedure δ G bad ps b hb0 hcert
    typedLedger c.premises = typedLedger ps ++
      [("measured: " ++ procedure, .measuredWithConfidence procedure δ),
       ("sampling model: " ++ procedure ++ " samples i.i.d. from the deployment law, independent of deployment",
         .correspondence)] ∧ c.bound = b + δ := by
  simp [ProbCert.ofMeasured, typedLedger]

end Product

/-! ## (2) The binomial tail on the i.i.d. trial space -/

section Binomial

/-- the law of n i.i.d. Bernoulli(p) trials -/
def wB (p : ℝ) {n : ℕ} (x : Fin n → Bool) : ℝ := ∏ i, (if x i then p else 1 - p)

/-- the number of successes -/
def cnt {n : ℕ} (x : Fin n → Bool) : ℕ := ∑ i, (if x i then 1 else 0)

/-- P_p(at least t successes in n trials) -/
noncomputable def tailP (n t : ℕ) (p : ℝ) : ℝ := ∑ x : Fin n → Bool, if t ≤ cnt x then wB p x else 0

theorem sum_cons {n : ℕ} (F : (Fin (n + 1) → Bool) → ℝ) :
    ∑ x, F x = ∑ b : Bool, ∑ y : Fin n → Bool, F (Fin.cons b y) := by
  rw [← (Fin.consEquiv (fun _ => Bool)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem wB_cons (p : ℝ) {n : ℕ} (b : Bool) (y : Fin n → Bool) :
    wB p (Fin.cons b y : Fin (n + 1) → Bool) = (if b then p else 1 - p) * wB p y := by
  simp [wB, Fin.prod_univ_succ]

theorem cnt_cons {n : ℕ} (b : Bool) (y : Fin n → Bool) :
    cnt (Fin.cons b y : Fin (n + 1) → Bool) = (if b then 1 else 0) + cnt y := by
  simp only [cnt, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem wB_total (p : ℝ) (n : ℕ) : ∑ x : Fin n → Bool, wB p x = 1 := by
  unfold wB
  rw [← Fintype.prod_sum (fun _ (b : Bool) => if b then p else 1 - p)]
  simp

theorem wB_nonneg (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) {n : ℕ} (x : Fin n → Bool) : 0 ≤ wB p x := by
  unfold wB; apply Finset.prod_nonneg; intro i _; split_ifs <;> linarith [hp.1, hp.2]

theorem tailP_zero (n : ℕ) (p : ℝ) : tailP n 0 p = 1 := by
  unfold tailP; simp only [Nat.zero_le, if_true]; exact wB_total p n

theorem tailP_nil (t : ℕ) (p : ℝ) : tailP 0 (t + 1) p = 0 := by
  unfold tailP; simp [cnt]

/-- **The recursion**: the first trial succeeds with probability p -/
theorem tailP_succ (n t : ℕ) (p : ℝ) :
    tailP (n + 1) (t + 1) p = p * tailP n t p + (1 - p) * tailP n (t + 1) p := by
  unfold tailP
  rw [sum_cons, Fintype.sum_bool]
  simp only [wB_cons, cnt_cons, if_true, Bool.false_eq_true, if_false, zero_add, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl; intro y _
    by_cases h : t ≤ cnt y
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h, mul_zero]
  · apply Finset.sum_congr rfl; intro y _
    split_ifs <;> simp

theorem tailP_nonneg (n t : ℕ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) : 0 ≤ tailP n t p := by
  unfold tailP; apply Finset.sum_nonneg; intro x _; split_ifs; exact wB_nonneg p hp x; exact le_rfl

/-- **Decreasing in t** -/
theorem tailP_anti (n t : ℕ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) : tailP n (t + 1) p ≤ tailP n t p := by
  unfold tailP; apply Finset.sum_le_sum; intro x _
  split_ifs with h1 h2 <;> first | exact le_rfl | exact wB_nonneg p hp x | omega

/-- **Monotone in p** (by the recursion: p'A' + (1−p')B' − (pA + (1−p)B) = (p'−p)(A'−B') + p(A'−A) + (1−p)(B'−B)) -/
theorem tailP_mono (n : ℕ) : ∀ (t : ℕ) (p p' : ℝ), 0 ≤ p → p ≤ p' → p' ≤ 1 → tailP n t p ≤ tailP n t p' := by
  induction n with
  | zero =>
    intro t p p' _ _ _
    cases t with
    | zero => rw [tailP_zero, tailP_zero]
    | succ t => rw [tailP_nil, tailP_nil]
  | succ n ih =>
    intro t p p' h0 hpp h1
    cases t with
    | zero => rw [tailP_zero, tailP_zero]
    | succ t =>
      rw [tailP_succ, tailP_succ]
      have hA := ih t p p' h0 hpp h1
      have hB := ih (t + 1) p p' h0 hpp h1
      have hAB := tailP_anti n t p' ⟨by linarith, h1⟩
      nlinarith [mul_nonneg (sub_nonneg.2 hpp) (sub_nonneg.2 hAB), mul_nonneg h0 (sub_nonneg.2 hA),
        mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - p) (sub_nonneg.2 hB)]

/-- the closed form Σ_{k ≥ t} C(n,k) p^k (1−p)^{n−k} -/
noncomputable def cf (n t : ℕ) (p : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1), if t ≤ k then (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) else 0

theorem cf_zero (n : ℕ) (p : ℝ) : cf n 0 p = 1 := by
  calc cf n 0 p = ∑ k ∈ range (n + 1), p ^ k * (1 - p) ^ (n - k) * (n.choose k : ℝ) := by
        unfold cf; apply Finset.sum_congr rfl; intro k _; rw [if_pos (Nat.zero_le k)]; ring
    _ = (p + (1 - p)) ^ n := (add_pow p (1 - p) n).symm
    _ = 1 := by rw [add_sub_cancel, one_pow]

theorem cf_nil (t : ℕ) (p : ℝ) : cf 0 (t + 1) p = 0 := by
  simp [cf]

theorem cf_succ (n t : ℕ) (p : ℝ) : cf (n + 1) (t + 1) p = p * cf n t p + (1 - p) * cf n (t + 1) p := by
  unfold cf
  rw [Finset.sum_range_succ']
  simp only [Nat.le_zero, Nat.add_one_ne_zero, if_false, add_zero]
  -- Pascal
  have hpas : ∀ k ∈ range (n + 1), (if t + 1 ≤ k + 1 then ((n + 1).choose (k + 1) : ℝ) * p ^ (k + 1) *
      (1 - p) ^ (n + 1 - (k + 1)) else 0) =
      p * (if t ≤ k then (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) else 0) +
      (if t + 1 ≤ k + 1 then (n.choose (k + 1) : ℝ) * p ^ (k + 1) * (1 - p) ^ (n + 1 - (k + 1)) else 0) := by
    intro k _
    by_cases h : t ≤ k
    · rw [if_pos (by omega), if_pos h, if_pos (by omega), Nat.choose_succ_succ]; push_cast; ring
    · rw [if_neg (by omega), if_neg h, if_neg (by omega)]; ring
  rw [Finset.sum_congr rfl hpas, Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  -- the shifted sum: reindex and drop the vanishing end terms
  set g : ℕ → ℝ := fun j => if t + 1 ≤ j then (n.choose j : ℝ) * p ^ j * (1 - p) ^ (n + 1 - j) else 0 with hg
  have hshift : ∑ k ∈ range (n + 1), (if t + 1 ≤ k + 1 then (n.choose (k + 1) : ℝ) * p ^ (k + 1) *
      (1 - p) ^ (n + 1 - (k + 1)) else 0) = ∑ k ∈ range (n + 1), g (k + 1) := rfl
  rw [hshift]
  have h0 : g 0 = 0 := by simp [hg]
  have hlast : g (n + 1) = 0 := by simp [hg, Nat.choose_succ_self]
  have e1 : ∑ k ∈ range (n + 1), g (k + 1) = ∑ j ∈ range (n + 1), g j := by
    have := Finset.sum_range_succ' g (n + 1)
    rw [h0, add_zero, Finset.sum_range_succ, hlast, add_zero] at this
    exact this.symm
  rw [e1, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j hj
  rw [mem_range] at hj
  simp only [hg]
  split_ifs
  · rw [show n + 1 - j = (n - j) + 1 by omega, pow_succ]; ring
  · ring

/-- **Closed form** of the binomial tail -/
theorem tailP_eq_cf (n : ℕ) : ∀ (t : ℕ) (p : ℝ), tailP n t p = cf n t p := by
  induction n with
  | zero =>
    intro t p
    cases t with
    | zero => rw [tailP_zero, cf_zero]
    | succ t => rw [tailP_nil, cf_nil]
  | succ n ih =>
    intro t p
    cases t with
    | zero => rw [tailP_zero, cf_zero]
    | succ t => rw [tailP_succ, cf_succ, ih, ih]

end Binomial

/-! ## Clopper–Pearson-style validity -/

section CP

/-- **Validity of any tail-test lower bound.** For a rule r_low with r_low(s) ∈ [0, 1] and, whenever r_low(s) > 0,
P_{r_low(s)}(S ≥ s) ≤ δ: for EVERY true success probability p ∈ [0, 1], P_p(p < r_low(S)) ≤ δ. -/
theorem cp_valid (n : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (rLow : ℕ → ℝ) (hr1 : ∀ s, rLow s ≤ 1)
    (hval : ∀ s, 0 < rLow s → tailP n s (rLow s) ≤ δ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    ∑ x : Fin n → Bool, (if p < rLow (cnt x) then wB p x else 0) ≤ δ := by
  classical
  by_cases hex : ∃ s, p < rLow s
  · let s0 := Nat.find hex
    have hs0 : p < rLow s0 := Nat.find_spec hex
    have hmin : ∀ s, p < rLow s → s0 ≤ s := fun s hs => Nat.find_min' hex hs
    calc ∑ x : Fin n → Bool, (if p < rLow (cnt x) then wB p x else 0)
        ≤ ∑ x : Fin n → Bool, (if s0 ≤ cnt x then wB p x else 0) := by
          apply Finset.sum_le_sum; intro x _
          by_cases h : p < rLow (cnt x)
          · rw [if_pos h, if_pos (hmin _ h)]
          · rw [if_neg h]; split_ifs; exact wB_nonneg p hp x; exact le_rfl
      _ = tailP n s0 p := rfl
      _ ≤ tailP n s0 (rLow s0) := tailP_mono n s0 p (rLow s0) hp.1 hs0.le (hr1 s0)
      _ ≤ δ := hval s0 (by linarith [hp.1])
  · push_neg at hex
    calc _ = (0 : ℝ) := Finset.sum_eq_zero fun x _ => by rw [if_neg (not_lt.2 (hex _))]
      _ ≤ δ := hδ

/-- **The preregistered one-threshold rule**: report r₀ iff S ≥ s₀. Valid when P_{r₀}(S ≥ s₀) ≤ δ. -/
theorem cp_threshold (n s₀ : ℕ) (r₀ δ : ℝ) (hδ : 0 ≤ δ) (hr0 : 0 ≤ r₀) (hr1 : r₀ ≤ 1)
    (htail : tailP n s₀ r₀ ≤ δ) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    ∑ x : Fin n → Bool, (if p < (if s₀ ≤ cnt x then r₀ else 0) then wB p x else 0) ≤ δ := by
  refine cp_valid n δ hδ (fun s => if s₀ ≤ s then r₀ else 0) (fun s => by split_ifs <;> linarith)
    (fun s hs => ?_) p hp
  by_cases h : s₀ ≤ s
  · simp only [h, if_true] at hs ⊢
    -- monotone in t: P(S ≥ s) ≤ P(S ≥ s₀) for s ≥ s₀
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    clear h hs
    induction d with
    | zero => simpa using htail
    | succ d ih => exact (tailP_anti n (s₀ + d) r₀ ⟨hr0, hr1⟩).trans ih
  · simp only [h, if_false, lt_self_iff_false] at hs

end CP

/-! ## (3) The instance: recall 190/200 at δ = 0.01 -/

theorem choose_200_190 : Nat.choose 200 190 = 22451004309013280 := by
  rw [← Nat.choose_symm (by norm_num)]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

theorem choose_200_191 : Nat.choose 200 191 = 1175445251780800 := by
  rw [← Nat.choose_symm (by norm_num)]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

theorem choose_200_192 : Nat.choose 200 192 = 55098996177225 := by
  rw [← Nat.choose_symm (by norm_num)]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

theorem choose_200_193 : Nat.choose 200 193 = 2283896214600 := by
  rw [← Nat.choose_symm (by norm_num)]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

theorem choose_200_194 : Nat.choose 200 194 = 82408626300 := by
  rw [← Nat.choose_symm (by norm_num)]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

theorem choose_200_195 : Nat.choose 200 195 = 2535650040 := by
  rw [← Nat.choose_symm (by norm_num)]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

theorem choose_200_196 : Nat.choose 200 196 = 64684950 := by
  rw [← Nat.choose_symm (by norm_num)]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

theorem choose_200_197 : Nat.choose 200 197 = 1313400 := by
  rw [← Nat.choose_symm (by norm_num)]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

theorem choose_200_198 : Nat.choose 200 198 = 19900 := by
  rw [← Nat.choose_symm (by norm_num)]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

theorem choose_200_199 : Nat.choose 200 199 = 200 := by
  rw [← Nat.choose_symm (by norm_num)]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

theorem choose_200_200 : Nat.choose 200 200 = 1 := by
  rw [← Nat.choose_symm (by norm_num)]
  norm_num [Nat.choose_eq_descFactorial_div_factorial, Nat.descFactorial, Nat.factorial]

/-- the exact tail: P_{9/10}(at least 190 of 200) ≤ 1/100 (≈ 0.00807) -/
theorem tail_200_190 : tailP 200 190 (9 / 10) ≤ 1 / 100 := by
  rw [tailP_eq_cf]
  unfold cf
  rw [← Finset.sum_range_add_sum_Ico _ (show 190 ≤ 200 + 1 by norm_num), Finset.sum_Ico_eq_sum_range]
  rw [Finset.sum_eq_zero (fun k hk => by rw [mem_range] at hk; rw [if_neg (by omega)]), zero_add]
  rw [Finset.sum_congr rfl (fun j _ => by rw [if_pos (by omega)])]
  simp only [show 200 + 1 - 190 = 11 from rfl, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [choose_200_190, choose_200_191, choose_200_192, choose_200_193, choose_200_194, choose_200_195, choose_200_196, choose_200_197, choose_200_198, choose_200_199, choose_200_200]

open ControlStack.Leakage ControlStack.Covert ControlStack.ReservedAudit ControlStack.ReservedRecall

/-- **The pitfall: population ≠ per-history.** Recall 1 on 95% of histories and 0 on 5% averages to 0.95, but the
worst history has recall 0. An attacker that can reach that stratum always escapes. -/
theorem population_not_per_history :
    (95 / 100 : ℝ) * 1 + 5 / 100 * 0 = 95 / 100 ∧ min (1 : ℝ) 0 = 0 := by norm_num

/-- **Strata, union bound.** Measuring each stratum separately: all stratum claims hold except with probability
≤ Σ δ_s. -/
theorem strata_union {Ω : Type} [Fintype Ω] (μ : Ω → ℝ) (hμ : ∀ ω, 0 ≤ μ ω) (strata : Finset ℕ)
    (G : ℕ → Ω → Prop) :
    prob μ (fun ω => ∃ s ∈ strata, ¬ G s ω) ≤ ∑ s ∈ strata, prob μ (fun ω => ¬ G s ω) := by
  classical
  unfold prob
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum; intro ω _
  by_cases h : ∃ s ∈ strata, ¬ G s ω
  · rw [if_pos h]
    obtain ⟨s, hs, hns⟩ := h
    have h1 := Finset.single_le_sum (f := fun s' => if ¬ G s' ω then μ ω else 0)
      (fun s' _ => by split_ifs <;> first | exact hμ ω | exact le_rfl) hs
    simp only [if_pos hns] at h1
    exact h1.trans (le_of_eq (Finset.sum_congr rfl fun s' _ => by split_ifs <;> simp_all))
  · rw [if_neg h]; exact Finset.sum_nonneg fun s _ => by split_ifs <;> first | exact hμ ω | exact le_rfl

/-- **End to end.** A held-out attack set of 200, each caught independently with the population recall p (the
measurement law `wB p`). The gate deploys iff at least 190 are caught, reporting r_low = 9/10. Premise
`homogeneous`: every history's recall is ≥ p (the kernel's `hrec` with r = p). Deployment uses reserved hidden
audits with N = 100, Bh = 10, against any adaptive attacker needing k = 5 attack rounds. Then, jointly over
measurement and deployment:
P(the gate deploys ∧ the attacker escapes) ≤ (91/100)^5 + 1/100. -/
theorem measured_recall_example {Y : Type} [Fintype Y] (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (K : Finset (Fin 100) → List (Y × AOut Unit) → Y × AOut Unit → ℝ)
    (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules 100 10 → ∀ h z, 0 ≤ K S h z)
    (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules 100 10 → ∀ h, ∑ z, K S h z ≤ 1)
    (homogeneous : ∀ S, S ∈ AuditBudget.randomSchedules 100 10 → ∀ h (a : Bool),
      ∑ y, K S h (y, (a, (), false)) ≤
        σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - p else 1)) :
    ∑ x : Fin 200 → Bool, wB p x *
        (if 190 ≤ cnt x then ∑ S : Finset (Fin 100), pU 100 10 S * val (K S) (recallSucc (N := 100) 5) 100 [] else 0)
      ≤ (91 / 100) ^ 5 + 1 / 100 := by
  classical
  set V := ∑ S : Finset (Fin 100), pU 100 10 S * val (K S) (recallSucc (N := 100) 5) 100 []
  have hV : V ≤ (1 - p * 10 / 100) ^ 5 :=
    (adaptive_recall_bound 5 10 (by norm_num) p hp.1 hp.2 K σ hσ hK0 hK1 homogeneous).trans
      (DamageBound.hyp_geom (N := 100) 10 (by norm_num) p hp.1 hp.2 5 (by norm_num))
  have hq0 : 0 ≤ 1 - p * 10 / 100 := by nlinarith [hp.2]
  have hq1 : 1 - p * 10 / 100 ≤ 1 := by nlinarith [hp.1]
  have hV1 : V ≤ 1 := hV.trans (pow_le_one₀ hq0 hq1)
  -- the good measurement event: if the gate deploys, the true recall is ≥ 9/10
  have hfail : prob (wB p) (fun x : Fin 200 → Bool => ¬ (190 ≤ cnt x → 9 / 10 ≤ p)) ≤ 1 / 100 := by
    have h := cp_threshold 200 190 (9 / 10) (1 / 100) (by norm_num) (by norm_num) (by norm_num) tail_200_190 p hp
    refine le_trans (le_of_eq ?_) h
    unfold prob
    apply Finset.sum_congr rfl; intro x _
    by_cases hc : 190 ≤ cnt x
    · by_cases hlt : p < 9 / 10
      · rw [if_pos (by intro h'; linarith [h' hc]), if_pos (by rw [if_pos hc]; exact hlt)]
      · rw [if_neg (by intro h'; exact h' (fun _ => by linarith)), if_neg (by rw [if_pos hc]; exact hlt)]
    · rw [if_neg (by intro h'; exact h' (fun h'' => absurd h'' hc)), if_neg (by rw [if_neg hc]; linarith [hp.1])]
  have := measured_bound (wB p) (wB_nonneg p hp) (wB_total p 200) (fun x => 190 ≤ cnt x → 9 / 10 ≤ p)
    (1 / 100) ((91 / 100) ^ 5) hfail (by norm_num)
    (fun x => if 190 ≤ cnt x then V else 0) (fun x => by split_ifs; exact hV1; norm_num)
    (fun x hG => by
      split_ifs with hc
      · have hp9 := hG hc
        refine hV.trans ?_
        have : 1 - p * 10 / 100 ≤ 91 / 100 := by linarith
        exact pow_le_pow_left₀ hq0 this 5
      · positivity)
  exact this

/-- the procedure name used in the recall ledger -/
def recallProcedure : String := "held-out attack set, n = 200, one-sided Clopper-Pearson at s >= 190 -> r_low = 9/10"

/-- **The instance ledger.** It lists:
- the kernel's trace premises;
- the homogeneity premise (the pitfall, stated as a correspondence obligation);
- the measured recall with δ = 1/100, and the sampling model.
It is NOT free text: `measuredRecallLedger_eq` proves it equal, by `rfl`, to the typed ledger of `recallPremises`,
the premise list whose propositions are exactly the hypotheses and conclusion of `measured_recall_example`, plus the
two premises `ProbCert.ofMeasured` appends (`ofMeasured_premises`). -/
def measuredRecallLedger : List (String × PremiseKind) :=
  [("measured recall bound: N = 100, Bh = 10, k = 5, any adaptive attacker",
     .proofObligation "ControlStack.Measured.measured_recall_example"),
   ("reserved audits: schedule uniform over 10-of-100 rounds, hidden from the attacker", .correspondence),
   ("homogeneous recall: every history's recall >= the measured population recall (or: per-stratum minimum)",
     .correspondence),
   ("measured: " ++ recallProcedure, .measuredWithConfidence recallProcedure (1 / 100)),
   ("sampling model: " ++ recallProcedure ++ " samples i.i.d. from the deployment law, independent of deployment",
     .correspondence)]

/-! ## The instance ledger, computed from the instance's premises -/

/-- the two premises `ProbCert.ofMeasured` appends: the measured premise (its failure event has probability ≤ δ
over the measurement) and the sampling model -/
def measuredPremises {Ωm : Type} [Fintype Ωm] (procedure : String) (δ : ℚ) (μm : Ωm → ℝ) (G : Ωm → Prop) :
    List Premise :=
  [⟨"measured: " ++ procedure, .measuredWithConfidence procedure δ, prob μm (fun ω => ¬ G ω) ≤ δ⟩,
   ⟨"sampling model: " ++ procedure ++ " samples i.i.d. from the deployment law, independent of deployment",
     .correspondence, True⟩]

/-- `ofMeasured` appends exactly `measuredPremises` -/
theorem ofMeasured_premises {Ωm Ωd : Type} [Fintype Ωm] [Fintype Ωd] (μm : Ωm → ℝ) (hm0 : ∀ ω, 0 ≤ μm ω)
    (hm1 : ∑ ω, μm ω = 1) (μd : Ωd → ℝ) (hd0 : ∀ ω, 0 ≤ μd ω) (hd1 : ∑ ω, μd ω = 1) (procedure : String) (δ : ℚ)
    (G : Ωm → Prop) (bad : Ωm → Ωd → Prop) (ps : List Premise) (b : ℝ) (hb0 : 0 ≤ b)
    (hcert : AllHold ps → ∀ ωm, G ωm → prob μd (bad ωm) ≤ b) :
    (ProbCert.ofMeasured μm hm0 hm1 μd hd0 hd1 procedure δ G bad ps b hb0 hcert).premises =
      ps ++ measuredPremises procedure δ μm G := rfl

/-- the good measurement event: if the gate deploys (S ≥ 190), the true recall is ≥ 9/10 -/
def recallGood (p : ℝ) (x : Fin 200 → Bool) : Prop := 190 ≤ cnt x → 9 / 10 ≤ p

section Instance

variable {Y : Type} [Fintype Y]

/-- reserved audits: the attacker's strategy is a distribution, the kernel a sub-distribution on the schedules -/
def reservedProp (K : Finset (Fin 100) → List (Y × AOut Unit) → Y × AOut Unit → ℝ)
    (σ : List (AOut Unit) → Bool → ℝ) : Prop :=
  (∀ g, IsDist (σ g)) ∧ (∀ S, S ∈ AuditBudget.randomSchedules 100 10 → ∀ h z, 0 ≤ K S h z) ∧
    (∀ S, S ∈ AuditBudget.randomSchedules 100 10 → ∀ h, ∑ z, K S h z ≤ 1)

/-- homogeneity: every history's recall is ≥ the measured population recall p -/
def homogeneousProp (p : ℝ) (K : Finset (Fin 100) → List (Y × AOut Unit) → Y × AOut Unit → ℝ)
    (σ : List (AOut Unit) → Bool → ℝ) : Prop :=
  ∀ S, S ∈ AuditBudget.randomSchedules 100 10 → ∀ h (a : Bool),
    ∑ y, K S h (y, (a, (), false)) ≤
      σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - p else 1)

/-- the conclusion of `measured_recall_example` -/
def recallBoundProp (p : ℝ) (K : Finset (Fin 100) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) : Prop :=
  ∑ x : Fin 200 → Bool, wB p x *
      (if 190 ≤ cnt x then ∑ S : Finset (Fin 100), pU 100 10 S * val (K S) (recallSucc (N := 100) 5) 100 [] else 0)
    ≤ (91 / 100) ^ 5 + 1 / 100

/-- the instance's premises, each with the proposition the theorem uses: the proof obligation (the theorem's
conclusion), the two kernel/correspondence premises, then `ofMeasured`'s measured and sampling-model premises -/
def recallPremises (p : ℝ) (K : Finset (Fin 100) → List (Y × AOut Unit) → Y × AOut Unit → ℝ)
    (σ : List (AOut Unit) → Bool → ℝ) : List Premise :=
  [⟨"measured recall bound: N = 100, Bh = 10, k = 5, any adaptive attacker",
     .proofObligation "ControlStack.Measured.measured_recall_example", recallBoundProp p K⟩,
   ⟨"reserved audits: schedule uniform over 10-of-100 rounds, hidden from the attacker", .correspondence,
     reservedProp K σ⟩,
   ⟨"homogeneous recall: every history's recall >= the measured population recall (or: per-stratum minimum)",
     .correspondence, homogeneousProp p K σ⟩] ++
  measuredPremises recallProcedure (1 / 100) (wB p) (recallGood p)

/-- **The ledger is the instance's ledger** (as `Cert.stack_ledger_eq`): for every p, kernel and attacker. -/
theorem measuredRecallLedger_eq (p : ℝ) (K : Finset (Fin 100) → List (Y × AOut Unit) → Y × AOut Unit → ℝ)
    (σ : List (AOut Unit) → Bool → ℝ) : typedLedger (recallPremises p K σ) = measuredRecallLedger := rfl

/-- the measured premise is a THEOREM for the sampling model (n = 200 i.i.d. Bernoulli(p) trials, any true p):
P_p(S ≥ 190 and p < 9/10) ≤ 1/100 (`cp_threshold`, `tail_200_190`) -/
theorem recall_measured_holds (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
    prob (wB p) (fun x : Fin 200 → Bool => ¬ recallGood p x) ≤ ((1 / 100 : ℚ) : ℝ) := by
  classical
  have h := cp_threshold 200 190 (9 / 10) (1 / 100) (by norm_num) (by norm_num) (by norm_num) tail_200_190 p hp
  push_cast
  refine le_trans (le_of_eq ?_) h
  unfold prob recallGood
  apply Finset.sum_congr rfl; intro x _
  by_cases hc : 190 ≤ cnt x
  · by_cases hlt : p < 9 / 10
    · rw [ite_eq_left (by intro h'; linarith [h' hc]), ite_eq_left (by rw [ite_eq_left hc]; exact hlt)]
    · rw [ite_eq_right (by intro h'; exact h' (fun _ => by linarith)), ite_eq_right (by rw [ite_eq_left hc]; exact hlt)]
  · rw [ite_eq_right (by intro h'; exact h' (fun h'' => absurd h'' hc)), ite_eq_right (by rw [ite_eq_right hc]; linarith [hp.1])]

/-- **Every premise of the ledger is discharged except the two correspondence premises.** The proof obligation is
`measured_recall_example`, and the measured premise is `recall_measured_holds`. The sampling model is recorded
(`True`: that the real held-out set is this i.i.d. law is not a formal statement). What remains is exactly
reserved audits and homogeneity. -/
theorem recallPremises_hold (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1)
    (K : Finset (Fin 100) → List (Y × AOut Unit) → Y × AOut Unit → ℝ) (σ : List (AOut Unit) → Bool → ℝ)
    (hres : reservedProp K σ) (hhom : homogeneousProp p K σ) : AllHold (recallPremises p K σ) := by
  intro q hq
  simp only [recallPremises, measuredPremises, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · exact measured_recall_example p hp K σ hres.1 hres.2.1 hres.2.2 hhom
  · exact hres
  · exact hhom
  · exact recall_measured_holds p hp
  · trivial

end Instance

/-- the final number: (91/100)^5 + 1/100 = 6340321451/10^10 ≈ 0.634 -/
theorem measured_recall_number : (91 / 100 : ℝ) ^ 5 + 1 / 100 = 6340321451 / 10 ^ 10 := by norm_num

end ControlStack.Measured

#print axioms ControlStack.Measured.measured_prod
#print axioms ControlStack.Measured.ofMeasured_ledger
#print axioms ControlStack.Measured.ProbCert.ofMeasured
#print axioms ControlStack.Measured.tailP_mono
#print axioms ControlStack.Measured.tailP_eq_cf
#print axioms ControlStack.Measured.cp_valid
#print axioms ControlStack.Measured.cp_threshold
#print axioms ControlStack.Measured.tail_200_190
#print axioms ControlStack.Measured.strata_union
#print axioms ControlStack.Measured.measured_recall_example
#print axioms ControlStack.Measured.measured_recall_number
#print axioms ControlStack.Measured.ofMeasured_premises
#print axioms ControlStack.Measured.measuredRecallLedger_eq
#print axioms ControlStack.Measured.recall_measured_holds
#print axioms ControlStack.Measured.recallPremises_hold

#eval IO.println (ControlStack.Cert.ledgerJson ControlStack.Measured.measuredRecallLedger)
