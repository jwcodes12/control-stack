/-
F6: reserved hidden audits with IMPERFECT recall against ADAPTIVE attackers, and the exact hypergeometric miss
probability. Builds on `ReservedAudit.lean` (perfect-recall adaptive bound; two-term non-adaptive recall bound).

Results.
1. `count_inter`: for |A| = k and j ≤ B, the number of B-subsets S of Fin N with |S ∩ A| = j is C(k,j)·C(N−k,B−j).
2. `missRecall_closed`: exact non-adaptive miss probability with constant recall r. For a fixed attack set A with
   |A| = k and a uniform size-B schedule,
     P(no catch) = Σ_{j ≤ min(k,B)} C(k,j)·C(N−k,B−j)/C(N,B) · (1−r)^j   (=: hypMiss N B k r).
   `missRecall_anti`: the miss probability is antitone in the attack set.
   `miss_ge_k`: any attack set with ≥ k rounds misses with probability ≤ hypMiss N B k r.
3. `adaptive_recall_bound` (adversary class ADAPTIVE_FEEDBACK, no leak about S beyond catch flags).
   Setting: the reserved hidden schedule S is uniform of size Bh, and flag-triggered audits or any other extra
   catches are arbitrary. Premise `hrec`: given the full history, the probability of attacking (a = true) in a
   reserved round and NOT being caught is ≤ σ(visible history)(a)·(1−r). In every other case the non-catch
   probability is ≤ σ(visible)(a). This is "each S-audit of an attack round catches with probability ≥ r,
   independently of the attacker's coins".
   Conclusion: P(≥ k attacks and never caught) ≤ hypMiss N Bh k r, the non-adaptive value. Adaptivity gains
   nothing. `adaptive_recall_two_term` weakens it to ≤ b + (1−b)(1−r), b = C(N−k,Bh)/C(N,Bh).
   Proof: the S-dependent (1−r) discount is moved from the certificate into the payoff (`cval_factor`). On a
   no-catch transcript the accumulated discount is (1−r)^{|S ∩ attackSet|} (`phi_live`). Its average over S is
   the non-adaptive miss probability of the transcript's own attack set (`miss_ge_k`). The attacker's coins never
   see S, because the certificate σ is S-independent.
4. `recallK` / `recall_instance_bound`: a concrete kernel (each S-audit of an attacked round detects with probability
   exactly r via a hidden coin) satisfying the premises, so the bound is non-vacuous.
   `recall_example`: N = 100, Bh = 10, k = 5, r = 1/2 gives ≤ (10104934117421/17310309456440 + 1)/2 ≈ 0.792
   for EVERY adaptive attacker.

Limits (what is NOT claimed).
- No leak about S: the visible output is (attack bit, catch flag) only. A timing or side leak needs a certificate
  with mass > 1 (as in `Leakage.audit_leak_bound`); combining it with imperfect recall is not done here.
- The recall premise is per-history (conditional on everything the attacker has done and seen). A population
  average detection rate does not imply it (ADVERSARY-CLASSES.md: no average-to-worst-case substitution).
- Catch coins are independent of the attacker's choice of round only through `hrec`. A monitor whose recall
  drops on the attacker's chosen content (CONTENT_ADAPTIVE) violates the premise unless r is a worst-case lower
  bound over that content.
- Statements about the model only; no deployment draws S, keeps it hidden or achieves recall r by these theorems.
- Classical mathematics (Vandermonde-style counting, optional stopping/transfer); no novelty is claimed.
-/
import ControlStack.Families.F6.ReservedAudit

namespace ControlStack.ReservedRecall

open Finset ControlStack.Leakage ControlStack.Covert ControlStack.ReservedAudit

/-! ## 1–2. Hypergeometric count and the exact non-adaptive miss probability -/

section Count

variable {N : ℕ}

/-- **Hypergeometric count.** For |A| = k and j ≤ B, #{S : |S| = B, |S ∩ A| = j} = C(k,j)·C(N−k,B−j). -/
theorem count_inter (B k j : ℕ) (A : Finset (Fin N)) (hA : A.card = k) (hj : j ≤ B) :
    ((AuditBudget.randomSchedules N B).filter (fun S => (S ∩ A).card = j)).card
      = Nat.choose k j * Nat.choose (N - k) (B - j) := by
  have hT : (powersetCard j A ×ˢ powersetCard (B - j) Aᶜ).card = Nat.choose k j * Nat.choose (N - k) (B - j) := by
    rw [card_product, card_powersetCard, card_powersetCard, card_compl, Fintype.card_fin, hA]
  rw [← hT]
  refine Finset.card_bij' (fun S _ => (S ∩ A, S \ A)) (fun p _ => p.1 ∪ p.2) ?_ ?_ ?_ ?_
  · intro S hS
    simp only [mem_filter, AuditBudget.randomSchedules, mem_powersetCard, subset_univ, true_and] at hS
    have hsd := card_sdiff_add_card_inter S A
    simp only [mem_product, mem_powersetCard]
    refine ⟨⟨inter_subset_right, hS.2⟩, ?_, ?_⟩
    · intro x hx; simp only [mem_sdiff] at hx; simpa using hx.2
    · omega
  · intro p hp
    simp only [mem_product, mem_powersetCard] at hp
    obtain ⟨⟨h1A, h1c⟩, h2A, h2c⟩ := hp
    have hdisj : Disjoint p.1 p.2 := by
      rw [Finset.disjoint_left]; intro x hx1 hx2
      have := h2A hx2; simp only [mem_compl] at this; exact this (h1A hx1)
    have hinter : (p.1 ∪ p.2) ∩ A = p.1 := by
      ext x; simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨hx | hx, hxA⟩
        · exact hx
        · have := h2A hx; simp only [mem_compl] at this; exact absurd hxA this
      · intro hx; exact ⟨Or.inl hx, h1A hx⟩
    simp only [mem_filter, AuditBudget.randomSchedules, mem_powersetCard, subset_univ, true_and]
    refine ⟨?_, by rw [hinter, h1c]⟩
    rw [card_union_of_disjoint hdisj, h1c, h2c]; omega
  · intro S _
    ext x; simp only [mem_union, mem_inter, mem_sdiff]; tauto
  · intro p hp
    simp only [mem_product, mem_powersetCard] at hp
    obtain ⟨⟨h1A, -⟩, h2A, -⟩ := hp
    have hnot : ∀ x ∈ p.2, x ∉ A := fun x hx => by have := h2A hx; simpa using this
    ext x
    · simp only [mem_inter, mem_union]
      constructor
      · rintro ⟨hx | hx, hxA⟩
        · exact hx
        · exact absurd hxA (hnot x hx)
      · intro hx; exact ⟨Or.inl hx, h1A hx⟩
    · simp only [mem_sdiff, mem_union]
      constructor
      · rintro ⟨hx | hx, hxA⟩
        · exact absurd (h1A hx) hxA
        · exact hx
      · intro hx; exact ⟨Or.inr hx, hnot x hx⟩

/-- the hypergeometric miss probability: Σ_{j ≤ min(k,B)} C(k,j)C(N−k,B−j)/C(N,B) · (1−r)^j -/
noncomputable def hypMiss (N B k : ℕ) (r : ℝ) : ℝ :=
  ∑ j ∈ range (min k B + 1),
    ((Nat.choose k j : ℝ) * (Nat.choose (N - k) (B - j) : ℝ)) / (Nat.choose N B : ℝ) * (1 - r) ^ j

theorem hypMiss_nonneg (N B k : ℕ) (r : ℝ) (hr1 : r ≤ 1) : 0 ≤ hypMiss N B k r := by
  unfold hypMiss
  apply Finset.sum_nonneg; intro j _
  have : 0 ≤ 1 - r := by linarith
  positivity

/-- **Exact non-adaptive miss probability** (NON_ADAPTIVE): a fixed k-round attack against a uniform size-B schedule
with per-audit recall r escapes with probability exactly hypMiss N B k r. -/
theorem missRecall_closed (B k : ℕ) (A : Finset (Fin N)) (hA : A.card = k) (r : ℝ) :
    missRecall B A (fun _ => r) = hypMiss N B k r := by
  rw [missRecall_const]
  have h1 : ∀ S : Finset (Fin N), pU N B S * (1 - r) ^ (S ∩ A).card
      = if S ∈ AuditBudget.randomSchedules N B then (Nat.choose N B : ℝ)⁻¹ * (1 - r) ^ (S ∩ A).card else 0 := by
    intro S; unfold pU; split_ifs <;> simp
  simp_rw [h1]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hmaps : ∀ S ∈ AuditBudget.randomSchedules N B, (S ∩ A).card ∈ range (min k B + 1) := by
    intro S hS
    simp only [AuditBudget.randomSchedules, mem_powersetCard, subset_univ, true_and] at hS
    have ha := card_le_card (inter_subset_right (s₁ := S) (s₂ := A))
    have hs := card_le_card (inter_subset_left (s₁ := S) (s₂ := A))
    rw [mem_range]; omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  unfold hypMiss
  apply Finset.sum_congr rfl
  intro j hj
  have hjB : j ≤ B := by rw [mem_range] at hj; omega
  rw [Finset.sum_congr rfl (fun S hS => by rw [(mem_filter.1 hS).2])]
  rw [Finset.sum_const, nsmul_eq_mul, count_inter B k j A hA hjB]
  push_cast
  ring

/-- the miss probability is antitone in the attack set -/
theorem missRecall_anti (B : ℕ) (A A' : Finset (Fin N)) (hAA : A ⊆ A') (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    missRecall B A' (fun _ => r) ≤ missRecall B A (fun _ => r) := by
  rw [missRecall_const, missRecall_const]
  apply Finset.sum_le_sum; intro S _
  apply mul_le_mul_of_nonneg_left _ (pU_nonneg N B S)
  apply pow_le_pow_of_le_one (by linarith) (by linarith)
  exact card_le_card (inter_subset_inter_left hAA)

/-- any attack set with ≥ k rounds escapes with probability ≤ hypMiss N B k r -/
theorem miss_ge_k (B k : ℕ) (A : Finset (Fin N)) (hA : k ≤ A.card) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    missRecall B A (fun _ => r) ≤ hypMiss N B k r := by
  obtain ⟨A', hA'A, hA'⟩ := exists_subset_card_eq hA
  rw [← missRecall_closed B k A' hA' r]
  exact missRecall_anti B A' A hA'A r hr0 hr1

/-- hypMiss is at most the two-term bound b + (1−b)(1−r) of `recall_miss_le` -/
theorem hypMiss_le_two_term (B k : ℕ) (hB : B ≤ N) (hk : k ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    hypMiss N B k r ≤ (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) +
      (1 - (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ)) * (1 - r) := by
  have hcard : k ≤ (univ : Finset (Fin N)).card := by simpa using hk
  obtain ⟨A, -, hA⟩ := exists_subset_card_eq hcard
  rw [← missRecall_closed B k A hA r]
  exact recall_miss_le B k hB A hA r (fun _ => r) hr0 (fun _ => ⟨le_rfl, hr1⟩)

end Count

/-! ## 3. Adaptive attackers with imperfect recall -/

section Factor

variable {O : Type} [Fintype O]

/-- moving a multiplicative certificate factor into the payoff: if Φ(g ++ [o]) = Φ(g)·f(g,o), then
Φ(g)·cval(c·f, B) = cval(c, B·Φ) -/
theorem cval_factor (c f : List O → O → ℝ) (Φ : List O → ℝ) (B : List O → ℝ)
    (hΦ : ∀ g o, Φ (g ++ [o]) = Φ g * f g o) :
    ∀ n g, Φ g * cval (fun g o => c g o * f g o) B n g = cval c (fun t => B t * Φ t) n g := by
  intro n; induction n with
  | zero => intro g; simp only [cval]; ring
  | succ n ih =>
    intro g
    simp only [cval]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro o _
    rw [← ih (g ++ [o]), hΦ]; ring

end Factor

section Adaptive

variable {N : ℕ}

/-- round i was an attack that was NOT caught -/
def attNC (t : List (AOut Unit)) (i : ℕ) : Bool :=
  match t[i]? with
  | some o => o.1 && !o.2.2
  | none => false

/-- accumulated recall discount: (1−r) per reserved round attacked without being caught -/
noncomputable def phi (r : ℝ) (S : Finset (Fin N)) (t : List (AOut Unit)) : ℝ :=
  ∏ j : Fin N, (if j ∈ S ∧ attNC t j = true then (1 - r) else 1)

/-- the per-round discount factor -/
noncomputable def fac (r : ℝ) (S : Finset (Fin N)) (g : List (AOut Unit)) (o : AOut Unit) : ℝ :=
  if memN S g.length ∧ o.1 = true ∧ o.2.2 = false then (1 - r) else 1

theorem term_snoc (r : ℝ) (S : Finset (Fin N)) (g : List (AOut Unit)) (o : AOut Unit) (j : Fin N) :
    (if j ∈ S ∧ attNC (g ++ [o]) j = true then 1 - r else 1)
      = (if j ∈ S ∧ attNC g j = true then 1 - r else 1) *
        (if (j : ℕ) = g.length ∧ j ∈ S ∧ (o.1 = true ∧ o.2.2 = false) then 1 - r else 1) := by
  rcases lt_trichotomy (j : ℕ) g.length with h | h | h
  · have e : attNC (g ++ [o]) j = attNC g j := by
      unfold attNC; rw [List.getElem?_append_left h]
    have hne : (j : ℕ) ≠ g.length := by omega
    rw [e]; simp [hne]
  · have e1 : attNC g j = false := by
      unfold attNC; rw [List.getElem?_eq_none (by omega)]
    have e2 : attNC (g ++ [o]) j = (o.1 && !o.2.2) := by
      unfold attNC; rw [List.getElem?_append_right (by omega), h, Nat.sub_self]; rfl
    rw [e1, e2]
    obtain ⟨a, u, c⟩ := o
    by_cases hS : j ∈ S <;> cases a <;> cases c <;> simp [hS, h]
  · have e1 : attNC g j = false := by
      unfold attNC; rw [List.getElem?_eq_none (by omega)]
    have e2 : attNC (g ++ [o]) j = false := by
      unfold attNC; rw [List.getElem?_eq_none (by simp; omega)]
    have hne : (j : ℕ) ≠ g.length := by omega
    rw [e1, e2]; simp [hne]

theorem prod_single_fac (r : ℝ) (S : Finset (Fin N)) (g : List (AOut Unit)) (o : AOut Unit) :
    ∏ j : Fin N, (if (j : ℕ) = g.length ∧ j ∈ S ∧ (o.1 = true ∧ o.2.2 = false) then 1 - r else 1)
      = fac r S g o := by
  unfold fac memN
  by_cases hex : ∃ j ∈ S, (j : ℕ) = g.length
  · obtain ⟨j0, hj0S, hj0⟩ := hex
    have hex' : ∃ j ∈ S, (j : ℕ) = g.length := ⟨j0, hj0S, hj0⟩
    rw [Finset.prod_eq_single j0]
    · simp only [hj0, hj0S, true_and, hex']
    · intro j _ hne
      rw [if_neg]
      rintro ⟨hj, -, -⟩
      exact hne (Fin.ext (hj.trans hj0.symm))
    · intro h; exact absurd (mem_univ j0) h
  · rw [Finset.prod_eq_one]
    · rw [if_neg]; rintro ⟨h, -⟩; exact hex h
    · intro j _
      rw [if_neg]
      rintro ⟨hj, hjS, -⟩
      exact hex ⟨j, hjS, hj⟩

theorem phi_snoc (r : ℝ) (S : Finset (Fin N)) (g : List (AOut Unit)) (o : AOut Unit) :
    phi r S (g ++ [o]) = phi r S g * fac r S g o := by
  unfold phi
  simp_rw [term_snoc r S g o]
  rw [Finset.prod_mul_distrib, prod_single_fac]

theorem phi_nil (r : ℝ) (S : Finset (Fin N)) : phi r S [] = 1 := by
  unfold phi attNC; simp

/-- on a transcript with no catch flag, the discount is (1−r)^{|S ∩ attackSet|} -/
theorem phi_live (r : ℝ) (S : Finset (Fin N)) (t : List (AOut Unit))
    (hl : (t.all fun o => !caughtFlag o) = true) :
    phi r S t = (1 - r) ^ (S ∩ attackSet (N := N) t).card := by
  have hatt : ∀ j : ℕ, attNC t j = attacked t j := by
    intro j
    unfold attNC attacked
    cases hj : t[j]? with
    | none => rfl
    | some o =>
      have hmem : o ∈ t := List.mem_of_getElem? hj
      rw [List.all_eq_true] at hl
      have := hl o hmem
      simp only [caughtFlag, Bool.not_eq_eq_eq_not, Bool.not_true] at this
      simp [this]
  unfold phi
  simp_rw [hatt]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
  congr 1
  congr 1
  ext j
  simp [attackSet]

/-- success under imperfect recall: ≥ k attacks and never caught -/
noncomputable def recallSucc (k : ℕ) (t : List (AOut Unit)) : ℝ :=
  (if k ≤ (attackSet (N := N) t).card then 1 else 0) * liveInd caughtFlag t

/-- **Adaptive attackers gain nothing against reserved hidden audits with imperfect recall.** Adversary class:
ADAPTIVE_FEEDBACK (sees its own actions and every catch flag; no other information about S). Kernel premises on the
support: sub-distribution, and `hrec`: the non-catch probability of attack bit a is ≤ σ(visible history)(a), with an
extra factor (1−r) when the round is reserved and a = true. Flag-triggered and other extra catches are arbitrary.
Then P(≥ k attacks, never caught) ≤ hypMiss N Bh k r, the exact non-adaptive miss probability of a k-round attack. -/
theorem adaptive_recall_bound {Y : Type} [Fintype Y] (k Bh : ℕ) (_hB : Bh ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ)
    (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h z, 0 ≤ K S h z)
    (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h, ∑ z, K S h z ≤ 1)
    (hrec : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h (a : Bool),
      ∑ y, K S h (y, (a, (), false)) ≤
        σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1)) :
    ∑ S : Finset (Fin N), pU N Bh S * val (K S) (recallSucc (N := N) k) N [] ≤ hypMiss N Bh k r := by
  -- S-independent certificate (catch outputs weight 1) and the S-dependent discount
  set c : List (AOut Unit) → AOut Unit → ℝ := fun g o => if o.2.2 then 1 else σ g o.1 with hc
  have hc0 : ∀ g o, 0 ≤ c g o := fun g o => by simp only [hc]; split_ifs; exact zero_le_one; exact (hσ g).1 _
  have hfac0 : ∀ (S : Finset (Fin N)) (g : List (AOut Unit)) (o : AOut Unit), 0 ≤ fac r S g o := fun S g o => by unfold fac; split_ifs <;> linarith
  have hpay0 : ∀ t, 0 ≤ recallSucc (N := N) k t := fun t =>
    mul_nonneg (by split_ifs <;> norm_num) (liveInd_nonneg _ _)
  -- step 1: per schedule, val ≤ cval with the discounted certificate = cval c (pay · phi)
  have hstep : ∀ S, pU N Bh S * val (K S) (recallSucc (N := N) k) N []
      ≤ pU N Bh S * cval c (fun t => recallSucc (N := N) k t * phi r S t) N [] := by
    intro S
    by_cases hS : S ∈ AuditBudget.randomSchedules N Bh
    · apply mul_le_mul_of_nonneg_left _ (pU_nonneg N Bh S)
      have hdom : Dominated (K S) (fun g o => c g o * fac r S g o) := by
        intro h o
        obtain ⟨a, u, cf⟩ := o
        cases u
        cases cf
        · have := hrec S hS h a
          simp only [hc, fac]
          simp only [Bool.false_eq_true, if_false, and_true]
          refine this.trans (le_of_eq ?_)
          by_cases hm : memN S (List.map Prod.snd h).length <;> cases a <;> simp
        · simp only [hc, fac, if_true]
          simp only [Bool.true_eq_false, and_false, if_false, mul_one]
          calc ∑ y, K S h (y, (a, (), true)) ≤ ∑ z, K S h z := by
                rw [Fintype.sum_prod_type]
                exact Finset.sum_le_sum fun y _ => Finset.single_le_sum (f := fun o' => K S h (y, o'))
                  (fun o' _ => hK0 S hS h _) (Finset.mem_univ _)
            _ ≤ 1 := hK1 S hS h
      have h1 := val_le_cval (K S) (fun g o => c g o * fac r S g o) (recallSucc (N := N) k) (hK0 S hS) hdom
        (fun g o => mul_nonneg (hc0 g o) (hfac0 S g o)) hpay0 N []
      have h2 := cval_factor c (fac r S) (phi r S) (recallSucc (N := N) k) (phi_snoc r S) N []
      rw [phi_nil, one_mul] at h2
      simpa [h2] using h1
    · simp [pU, hS]
  -- step 2: average over S inside the certificate value
  have hsum := Finset.sum_le_sum fun S (_ : S ∈ univ) => hstep S
  rw [cval_wsum] at hsum
  -- step 3: blind value of each transcript
  have hblind : ∀ t, ∑ S : Finset (Fin N), pU N Bh S * (recallSucc (N := N) k t * phi r S t)
      ≤ hypMiss N Bh k r * liveInd caughtFlag t := by
    intro t
    unfold recallSucc liveInd
    by_cases hl : (t.all fun o => !caughtFlag o) = true
    · simp only [hl, if_true, mul_one]
      by_cases hk : k ≤ (attackSet (N := N) t).card
      · simp only [hk, if_true, one_mul]
        simp_rw [phi_live r _ t hl]
        have := miss_ge_k Bh k (attackSet (N := N) t) hk r hr0 hr1
        rw [missRecall_const] at this
        simpa [Finset.inter_comm] using this
      · simp only [hk, if_false, zero_mul, mul_zero, Finset.sum_const_zero]
        exact hypMiss_nonneg N Bh k r hr1
    · simp [hl]
  have h3 := cval_mono c _ _ hc0 hblind N []
  rw [cval_smul, cval_live] at h3
  have hl0 : liveInd caughtFlag ([] : List (AOut Unit)) = 1 := by simp [liveInd]
  rw [hl0, one_mul] at h3
  -- step 4: the certificate mass without catch outputs is ≤ 1
  have hm : mass (dropStop caughtFlag c) N [] ≤ 1 ^ N := by
    apply mass_le_pow _ 1
    · intro g o; unfold dropStop; split_ifs; exact le_rfl; exact hc0 g o
    · exact zero_le_one
    · intro g
      simp only [dropStop, caughtFlag, hc, Fintype.sum_prod_type, Fintype.univ_unit, Finset.sum_singleton,
        Fintype.sum_bool]
      have h1 := (hσ g).2
      rw [Fintype.sum_bool] at h1
      simp; linarith
  rw [one_pow] at hm
  calc _ ≤ _ := hsum
    _ ≤ _ := h3
    _ ≤ hypMiss N Bh k r * 1 := mul_le_mul_of_nonneg_left hm (hypMiss_nonneg N Bh k r hr1)
    _ = _ := mul_one _

/-- the two-term form: P(≥ k attacks, never caught) ≤ b + (1−b)(1−r) for every adaptive attacker -/
theorem adaptive_recall_two_term {Y : Type} [Fintype Y] (k Bh : ℕ) (hB : Bh ≤ N) (hk : k ≤ N) (r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ)
    (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h z, 0 ≤ K S h z)
    (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h, ∑ z, K S h z ≤ 1)
    (hrec : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h (a : Bool),
      ∑ y, K S h (y, (a, (), false)) ≤
        σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1)) :
    ∑ S : Finset (Fin N), pU N Bh S * val (K S) (recallSucc (N := N) k) N [] ≤
      (Nat.choose (N - k) Bh : ℝ) / (Nat.choose N Bh : ℝ) +
        (1 - (Nat.choose (N - k) Bh : ℝ) / (Nat.choose N Bh : ℝ)) * (1 - r) :=
  (adaptive_recall_bound k Bh hB r hr0 hr1 K σ hσ hK0 hK1 hrec).trans
    (hypMiss_le_two_term Bh k hB hk r hr0 hr1)

/-! ## 4. A concrete kernel: detection coin with probability exactly r -/

/-- hidden y = the auditor's detection coin (true w.p. r); catch = attack ∧ reserved round ∧ detected -/
noncomputable def recallK (r : ℝ) (σ : List (AOut Unit) → Bool → ℝ) :
    Finset (Fin N) → List (Bool × AOut Unit) → Bool × AOut Unit → ℝ :=
  fun S h yo => σ (h.map Prod.snd) yo.2.1 * (if yo.1 then r else 1 - r) *
    (if yo.2.2.2 = (yo.2.1 && decide (memN S (h.map Prod.snd).length) && yo.1) then 1 else 0)

/-- **Non-vacuity**: the detection-coin kernel satisfies the premises; every adaptive attacker against it escapes
with probability ≤ hypMiss N Bh k r. -/
theorem recall_instance_bound (k Bh : ℕ) (hB : Bh ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) :
    ∑ S : Finset (Fin N), pU N Bh S * val (recallK r σ S) (recallSucc (N := N) k) N [] ≤ hypMiss N Bh k r := by
  have hr1' : 0 ≤ 1 - r := by linarith
  refine adaptive_recall_bound k Bh hB r hr0 hr1 (recallK r σ) σ hσ ?_ ?_ ?_
  · intro S _ h z
    unfold recallK
    refine mul_nonneg (mul_nonneg ((hσ _).1 _) ?_) (by split_ifs <;> norm_num)
    split_ifs <;> assumption
  · intro S _ h
    have h1 := (hσ (h.map Prod.snd)).2
    rw [Fintype.sum_bool] at h1
    have h0 := (hσ (h.map Prod.snd)).1
    simp only [recallK, Fintype.sum_prod_type, Fintype.univ_unit, Finset.sum_singleton, Fintype.sum_bool]
    cases hm : decide (memN S (List.map Prod.snd h).length) <;> simp <;> nlinarith [h0 true, h0 false]
  · intro S _ h a
    have h0 := (hσ (h.map Prod.snd)).1 a
    simp only [recallK, Fintype.sum_bool, List.length_map]
    by_cases hm : memN S h.length <;> cases a <;> simp [hm] <;> nlinarith

/-- **Numeric instance.** N = 100, Bh = 10 reserved hidden audits, k = 5, recall 1/2: every adaptive attacker
escapes with probability ≤ (10104934117421/17310309456440 + 1)/2 ≈ 0.792. -/
theorem recall_example (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) :
    ∑ S : Finset (Fin 100), pU 100 10 S * val (recallK (1 / 2) σ S) (recallSucc (N := 100) 5) 100 []
      ≤ ((10104934117421 : ℝ) / 17310309456440 + 1) / 2 := by
  have h := (recall_instance_bound 5 10 (by norm_num) (1 / 2) (by norm_num) (by norm_num) σ hσ).trans
    (hypMiss_le_two_term (N := 100) 10 5 (by norm_num) (by norm_num) (1 / 2) (by norm_num) (by norm_num))
  rw [show (100 - 5 : ℕ) = 95 from rfl, AuditBudget.choose_95_10, AuditBudget.choose_100_10] at h
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

end Adaptive

end ControlStack.ReservedRecall

#print axioms ControlStack.ReservedRecall.count_inter
#print axioms ControlStack.ReservedRecall.missRecall_closed
#print axioms ControlStack.ReservedRecall.missRecall_anti
#print axioms ControlStack.ReservedRecall.miss_ge_k
#print axioms ControlStack.ReservedRecall.hypMiss_le_two_term
#print axioms ControlStack.ReservedRecall.cval_factor
#print axioms ControlStack.ReservedRecall.phi_snoc
#print axioms ControlStack.ReservedRecall.phi_live
#print axioms ControlStack.ReservedRecall.adaptive_recall_bound
#print axioms ControlStack.ReservedRecall.adaptive_recall_two_term
#print axioms ControlStack.ReservedRecall.recall_instance_bound
#print axioms ControlStack.ReservedRecall.recall_example
