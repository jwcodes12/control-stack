/-
F6 × F5 × F3: expected DAMAGE (not only the probability of k unaudited attacks) under reserved hidden audits with
imperfect recall, per-step damage caps and halt-on-catch.

Reviewers (Gemini adversarial review, "Missing Results: Damage Bounds") noted that the audit bounds control
P(k unaudited attack steps) but not harm. This file composes three primitives:
- F6: reserved hidden audit schedule S (uniform of size Bh), recall ≥ r per audit of an attacked round,
  arbitrary extra (flag-triggered) catches. This is the setting of `ReservedRecall.adaptive_recall_bound`.
- F5: per-step damage cap D (each uncaught attack round deals damage in [0, D]; e.g. a gate cap per transaction),
  and optionally a global cap G on total damage.
- F3: the first catch triggers HALT. Damage counts only uncaught attack rounds strictly before the first catch,
  so the caught action is blocked (audit before effect) and nothing happens after the halt. An in-flight budget F
  covers effects already dispatched when the halt lands (cf. the SC-26 gate's `halt_freezes`: after halt no new
  effect is admitted; only effects already reserved/dispatched can complete).

Results. Let X(t) (`ucX`) be the number of attack rounds before the first catch flag in transcript t.
1. `tail_bound`: P(X ≥ j) ≤ hypMiss N Bh j r. Adversary class ADAPTIVE_FEEDBACK, same premises as
   `adaptive_recall_bound`. Proof: freeze the attacker after its j-th uncaught attack (`freezeK`, `freeze_le`),
   then on every reachable transcript X ≥ j implies "≥ j attacks, never caught" (`pX_le_succ`).
2. `expected_uc`: E[X] ≤ Σ_{j=1}^{N} hypMiss N Bh j r (tail-sum formula `ucX_tail`).
   `damage_bound`: E[damage] ≤ D · Σ_{j=1}^{N} hypMiss N Bh j r for every damage function with
   0 ≤ damage ≤ D · X.
3. Closed forms:
   - `expected_r1`, perfect recall: Σ_{j=1}^{N} hypMiss N B j 1 = (N − B)/(B + 1) exactly (hockey stick,
     `sum_range_choose_succ`).
   - `hyp_geom`, any recall: hypMiss N B k r ≤ (1 − rB/N)^k, i.e. sampling without replacement is dominated by
     independent rounds that catch with probability rB/N. Proof: one-step recursion plus Chebyshev's sum
     inequality, `hyp_step`.
   - `expected_geom`: Σ_{j=1}^{N} hypMiss N B j r ≤ (N − rB)/(rB).
4. Deterministic complements (F5/F3), `damage_cap_inflight`: if damage ≤ G always (global cap) and
   damage ≤ D · X + F (F: in-flight budget, effects already dispatched when the halt lands), then
   E[damage] ≤ min(G, D · Σ hypMiss + F).
5. Witnesses:
   - `no_halt_damage`: if a catch is only logged, not halting, an always-attacking attacker that is caught EVERY
     round still deals N·D, while the halt-coupled count X is 0;
   - `no_cap_damage`: without a per-step cap, one uncaught attack round deals any amount M.
6. Numbers, N = 100 rounds, Bh = 10 reserved audits:
   - `example_r1`: r = 1 gives E[X] ≤ 90/11 ≈ 8.18 attack rounds before the first catch;
   - `example_r_half`: r = 1/2 gives E[X] ≤ 19.

Limits (what is NOT claimed).
- Damage is a function of the visible transcript bounded by D · X. Hidden-state-dependent damage is covered only
  through that pointwise bound, and a monitor that misreads damage is not modelled.
- Halt is modelled as "damage stops counting at the first catch". That a deployed HALT really stops all effects is
  an F3 correspondence obligation; the SC-26 gate model's `halt_freezes` is one such model-level statement.
- Recall is a per-history lower bound (see `ReservedRecall`). There is no leak about S beyond catch flags.
- Expected-damage bounds say nothing about tail risk of a single catastrophic step. That is exactly what the
  per-step cap D (F5) is for (`no_cap_damage`).
- Classical mathematics (tail-sum formula, hockey stick, Chebyshev's sum inequality); no novelty is claimed.
-/
import ControlStack.Families.F6.ReservedRecall
import Mathlib.Algebra.Order.Chebyshev

namespace ControlStack.DamageBound

open Finset ControlStack.Leakage ControlStack.Covert ControlStack.ReservedAudit ControlStack.ReservedRecall

/-! ## Generic `val` lemmas -/

section ValLemmas

variable {Y O : Type} [Fintype Y] [Fintype O]

theorem val_le_const (K : List (Y × O) → Y × O → ℝ) (pay : List O → ℝ) (M : ℝ)
    (hK0 : ∀ h z, 0 ≤ K h z) (hK1 : ∀ h, ∑ z, K h z ≤ 1) (hM : 0 ≤ M) (hpay : ∀ t, pay t ≤ M) :
    ∀ n h, val K pay n h ≤ M := by
  intro n; induction n with
  | zero => intro h; exact hpay _
  | succ n ih =>
    intro h
    simp only [Leakage.val]
    calc ∑ y, ∑ o, K h (y, o) * val K pay n (h ++ [(y, o)]) ≤ ∑ y, ∑ o, K h (y, o) * M := by
          apply Finset.sum_le_sum; intro y _; apply Finset.sum_le_sum; intro o _
          exact mul_le_mul_of_nonneg_left (ih _) (hK0 h (y, o))
      _ = M * ∑ z, K h z := by
          rw [Fintype.sum_prod_type, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro y _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro o _; ring
      _ ≤ M * 1 := mul_le_mul_of_nonneg_left (hK1 h) hM
      _ = M := mul_one M

/-- payoff monotonicity on a set of transcripts closed under the kernel's possible steps -/
theorem val_mono_on (K : List (Y × O) → Y × O → ℝ) (P : List O → Prop) (pay pay' : List O → ℝ)
    (hK0 : ∀ h z, 0 ≤ K h z)
    (hP : ∀ h y o, K h (y, o) ≠ 0 → P (h.map Prod.snd) → P (h.map Prod.snd ++ [o]))
    (hle : ∀ t, P t → pay t ≤ pay' t) :
    ∀ n h, P (h.map Prod.snd) → val K pay n h ≤ val K pay' n h := by
  intro n; induction n with
  | zero => intro h hh; exact hle _ hh
  | succ n ih =>
    intro h hh
    simp only [Leakage.val]
    apply Finset.sum_le_sum; intro y _
    apply Finset.sum_le_sum; intro o _
    by_cases hK : K h (y, o) = 0
    · simp [hK]
    · exact mul_le_mul_of_nonneg_left (ih _ (by simpa using hP h y o hK hh)) (hK0 h (y, o))

theorem val_smul (K : List (Y × O) → Y × O → ℝ) (c : ℝ) (pay : List O → ℝ) :
    ∀ n h, val K (fun t => c * pay t) n h = c * val K pay n h := by
  intro n; induction n with
  | zero => intro h; rfl
  | succ n ih =>
    intro h
    simp only [Leakage.val, ih, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro y _
    apply Finset.sum_congr rfl; intro o _; ring

theorem val_add (K : List (Y × O) → Y × O → ℝ) (p q : List O → ℝ) :
    ∀ n h, val K (fun t => p t + q t) n h = val K p n h + val K q n h := by
  intro n; induction n with
  | zero => intro h; rfl
  | succ n ih =>
    intro h
    simp only [Leakage.val, ih, mul_add, Finset.sum_add_distrib]

theorem val_finsum {ι : Type} (s : Finset ι) (K : List (Y × O) → Y × O → ℝ) (f : ι → List O → ℝ) :
    ∀ n h, val K (fun t => ∑ j ∈ s, f j t) n h = ∑ j ∈ s, val K (f j) n h := by
  intro n; induction n with
  | zero => intro h; rfl
  | succ n ih =>
    intro h
    simp only [Leakage.val, ih, Finset.mul_sum]
    have e : ∀ y, ∑ o, ∑ j ∈ s, K h (y, o) * val K (f j) n (h ++ [(y, o)])
        = ∑ j ∈ s, ∑ o, K h (y, o) * val K (f j) n (h ++ [(y, o)]) := fun y => Finset.sum_comm
    simp_rw [e]
    exact Finset.sum_comm

/-- a deterministic kernel replays its single output -/
theorem val_det [DecidableEq Y] [DecidableEq O] (z0 : Y × O) (pay : List O → ℝ) :
    ∀ n h, val (fun _ z => if z = z0 then (1 : ℝ) else 0) pay n h = pay (h.map Prod.snd ++ List.replicate n z0.2) := by
  intro n; induction n with
  | zero => intro h; simp [Leakage.val]
  | succ n ih =>
    intro h
    simp only [Leakage.val]
    have e : ∑ y, ∑ o, (if (y, o) = z0 then (1 : ℝ) else 0) *
          val (fun _ z => if z = z0 then (1 : ℝ) else 0) pay n (h ++ [(y, o)])
        = ∑ z : Y × O, (if z = z0 then (1 : ℝ) else 0) *
          val (fun _ z => if z = z0 then (1 : ℝ) else 0) pay n (h ++ [z]) :=
      (Fintype.sum_prod_type (f := fun z : Y × O => (if z = z0 then (1 : ℝ) else 0) *
          val (fun _ z => if z = z0 then (1 : ℝ) else 0) pay n (h ++ [z]))).symm
    rw [e]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [ih]
    simp [List.replicate_succ]

end ValLemmas

/-! ## Attack rounds before the first catch -/

section Count

/-- the transcript up to (excluding) the first catch flag -/
def pre (t : List (AOut Unit)) : List (AOut Unit) := t.takeWhile (fun o => !caughtFlag o)

/-- X(t): attack rounds before the first catch -/
def ucX (N : ℕ) (t : List (AOut Unit)) : ℕ := (attackSet (N := N) (pre t)).card

theorem pre_all (g : List (AOut Unit)) (hg : (g.all fun o => !caughtFlag o) = true) : pre g = g := by
  induction g with
  | nil => rfl
  | cons x g ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hg
    have := ih hg.2
    simp only [pre] at this ⊢
    rw [List.takeWhile_cons, if_pos hg.1, this]

theorem pre_snoc (g : List (AOut Unit)) (o : AOut Unit) :
    pre (g ++ [o]) = if (g.all fun o => !caughtFlag o) = true then (if caughtFlag o = true then g else g ++ [o])
      else pre g := by
  induction g with
  | nil => cases h : caughtFlag o <;> simp [pre, h]
  | cons x g ih =>
    simp only [pre] at ih ⊢
    rw [List.cons_append, List.takeWhile_cons, List.all_cons]
    cases hx : caughtFlag x
    · simp only [Bool.not_false, if_true, Bool.true_and]
      rw [ih]
      by_cases hg : (g.all fun o => !caughtFlag o) = true
      · rw [if_pos hg, if_pos hg]; split_ifs <;> rfl
      · rw [if_neg hg, if_neg hg, List.takeWhile_cons]; simp [hx]
    · simp [hx]

theorem attacked_snoc (g : List (AOut Unit)) (o : AOut Unit) (i : ℕ) (h : attacked g i = true) :
    attacked (g ++ [o]) i = true := by
  unfold attacked at h ⊢
  cases hg : g[i]? with
  | none => rw [hg] at h; exact absurd h (by simp)
  | some x =>
    have hi : i < g.length := by
      by_contra hc; rw [List.getElem?_eq_none (by omega)] at hg; cases hg
    rw [List.getElem?_append_left hi, hg]; rw [hg] at h; exact h

theorem attackSet_snoc {N : ℕ} (g : List (AOut Unit)) (o : AOut Unit) :
    attackSet (N := N) g ⊆ attackSet (N := N) (g ++ [o]) := by
  intro i hi
  simp only [attackSet, mem_filter, mem_univ, true_and] at hi ⊢
  exact attacked_snoc g o i hi

theorem ucX_mono (N : ℕ) (g : List (AOut Unit)) (o : AOut Unit) : ucX N g ≤ ucX N (g ++ [o]) := by
  unfold ucX
  rw [pre_snoc]
  split_ifs with h1 h2
  · rw [pre_all g h1]
  · rw [pre_all g h1]; exact card_le_card (attackSet_snoc g o)
  · exact le_rfl

theorem ucX_stuck (N : ℕ) (g : List (AOut Unit)) (o : AOut Unit)
    (h : (g.all fun o => !caughtFlag o) = false ∨ caughtFlag o = true) : ucX N (g ++ [o]) = ucX N g := by
  unfold ucX
  rw [pre_snoc]
  rcases h with h | h
  · simp [h]
  · split_ifs with h1
    · rw [pre_all g h1]
    · rfl

theorem ucX_le (N : ℕ) (t : List (AOut Unit)) : ucX N t ≤ N := by
  unfold ucX
  simpa using card_le_univ (attackSet (N := N) (pre t))

/-- tail-sum formula, pointwise: X = Σ_{j=1}^{N} [X ≥ j] -/
theorem ucX_tail (N : ℕ) (t : List (AOut Unit)) :
    (ucX N t : ℝ) = ∑ j ∈ range N, (if j + 1 ≤ ucX N t then (1 : ℝ) else 0) := by
  rw [Finset.sum_boole]
  have : (range N).filter (fun j => j + 1 ≤ ucX N t) = range (ucX N t) := by
    ext j; simp only [mem_filter, mem_range]
    have := ucX_le N t
    omega
  rw [this, card_range]

end Count

/-! ## 1. Tail bound for adaptive attackers: P(X ≥ j) ≤ hypMiss N Bh j r -/

section Tail

variable {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]

def o0 : AOut Unit := (false, (), false)

/-- the attacker frozen after its j-th uncaught attack: from then on, no attack and no flag -/
noncomputable def freezeK (N j : ℕ) (y0 : Y) (Kx : List (Y × AOut Unit) → Y × AOut Unit → ℝ) :
    List (Y × AOut Unit) → Y × AOut Unit → ℝ :=
  fun h z => if j ≤ ucX N (h.map Prod.snd) then (if z = (y0, o0) then 1 else 0) else Kx h z

noncomputable def pX (N j : ℕ) (t : List (AOut Unit)) : ℝ := if j ≤ ucX N t then 1 else 0

theorem sum_point (z0 : Y × AOut Unit) (F : Y × AOut Unit → ℝ) :
    ∑ y, ∑ o, (if (y, o) = z0 then (1 : ℝ) else 0) * F (y, o) = F z0 := by
  have e := (Fintype.sum_prod_type (f := fun z : Y × AOut Unit => (if z = z0 then (1 : ℝ) else 0) * F z)).symm
  rw [e]
  simp

theorem val_frozen (j : ℕ) (y0 : Y) (Kx : List (Y × AOut Unit) → Y × AOut Unit → ℝ) :
    ∀ n h, j ≤ ucX N (h.map Prod.snd) → val (freezeK N j y0 Kx) (pX N j) n h = 1 := by
  intro n; induction n with
  | zero => intro h hfr; simp [Leakage.val, pX, hfr]
  | succ n ih =>
    intro h hfr
    simp only [Leakage.val]
    have e : ∀ y o, freezeK N j y0 Kx h (y, o) = if (y, o) = (y0, o0) then 1 else 0 := by
      intro y o; simp [freezeK, hfr]
    simp_rw [e]
    rw [sum_point (y0, o0) (fun z => val (freezeK N j y0 Kx) (pX N j) n (h ++ [z]))]
    apply ih
    rw [List.map_append]
    exact le_trans hfr (ucX_mono N _ _)

/-- freezing after the j-th uncaught attack does not lower P(X ≥ j) -/
theorem freeze_le (j : ℕ) (y0 : Y) (Kx : List (Y × AOut Unit) → Y × AOut Unit → ℝ)
    (hK0 : ∀ h z, 0 ≤ Kx h z) (hK1 : ∀ h, ∑ z, Kx h z ≤ 1) :
    ∀ n h, val Kx (pX N j) n h ≤ val (freezeK N j y0 Kx) (pX N j) n h := by
  intro n; induction n with
  | zero => intro h; exact le_rfl
  | succ n ih =>
    intro h
    by_cases hfr : j ≤ ucX N (h.map Prod.snd)
    · rw [val_frozen j y0 Kx (n + 1) h hfr]
      exact val_le_const Kx _ 1 hK0 hK1 zero_le_one (fun t => by unfold pX; split_ifs <;> norm_num) (n + 1) h
    · simp only [Leakage.val]
      have e : ∀ z, freezeK N j y0 Kx h z = Kx h z := fun z => by simp [freezeK, hfr]
      simp_rw [e]
      apply Finset.sum_le_sum; intro y _
      apply Finset.sum_le_sum; intro o _
      exact mul_le_mul_of_nonneg_left (ih _) (hK0 h (y, o))

/-- on transcripts the frozen kernel can produce, X ≥ j means "≥ j attacks and never caught" -/
theorem pX_le_succ (j : ℕ) (y0 : Y) (Kx : List (Y × AOut Unit) → Y × AOut Unit → ℝ)
    (hK0 : ∀ h z, 0 ≤ Kx h z) (n : ℕ) :
    val (freezeK N j y0 Kx) (pX N j) n [] ≤ val (freezeK N j y0 Kx) (recallSucc (N := N) j) n [] := by
  have hK0' : ∀ h z, 0 ≤ freezeK N j y0 Kx h z := fun h z => by
    unfold freezeK; split_ifs <;> first | exact hK0 h z | norm_num
  refine val_mono_on _ (fun t => j ≤ ucX N t → (t.all fun o => !caughtFlag o) = true) _ _ hK0' ?_ ?_ n [] ?_
  · intro h y o hK hPg
    by_cases hfr : j ≤ ucX N (h.map Prod.snd)
    · have ho : o = o0 := by
        by_contra hne
        apply hK
        simp [freezeK, hfr, hne]
      intro _
      subst ho
      rw [List.all_append, hPg hfr]; rfl
    · intro hj
      have hall : ((h.map Prod.snd).all fun o => !caughtFlag o) = true := by
        by_contra hc
        have := ucX_stuck N (h.map Prod.snd) o (Or.inl (Bool.eq_false_iff.mpr hc))
        omega
      have hco : caughtFlag o = false := by
        by_contra hc
        have := ucX_stuck N (h.map Prod.snd) o (Or.inr (by revert hc; cases caughtFlag o <;> simp))
        omega
      rw [List.all_append, hall]; simp [hco]
  · intro t hPt
    unfold pX recallSucc liveInd
    by_cases hj : j ≤ ucX N t
    · have hall := hPt hj
      have hcard : j ≤ (attackSet (N := N) t).card := by unfold ucX at hj; rwa [pre_all t hall] at hj
      simp [hj, hall, hcard]
    · simp only [hj, if_false]
      split_ifs <;> norm_num
  · intro _; simp

/-- **Tail bound.** Adversary class: ADAPTIVE_FEEDBACK (premises of `adaptive_recall_bound`). The number X of attack
rounds before the first catch satisfies P(X ≥ j) ≤ hypMiss N Bh j r. -/
theorem tail_bound (y0 : Y) (j Bh : ℕ) (hB : Bh ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ)
    (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h z, 0 ≤ K S h z)
    (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h, ∑ z, K S h z ≤ 1)
    (hrec : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h (a : Bool),
      ∑ y, K S h (y, (a, (), false)) ≤
        σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1)) :
    ∑ S : Finset (Fin N), pU N Bh S * val (K S) (pX N j) N [] ≤ hypMiss N Bh j r := by
  have hstep : ∀ S : Finset (Fin N), pU N Bh S * val (K S) (pX N j) N []
      ≤ pU N Bh S * val (freezeK N j y0 (K S)) (recallSucc (N := N) j) N [] := by
    intro S
    by_cases hS : S ∈ AuditBudget.randomSchedules N Bh
    · exact mul_le_mul_of_nonneg_left
        ((freeze_le j y0 (K S) (hK0 S hS) (hK1 S hS) N []).trans (pX_le_succ j y0 (K S) (hK0 S hS) N))
        (pU_nonneg N Bh S)
    · simp [pU, hS]
  refine (Finset.sum_le_sum fun S _ => hstep S).trans ?_
  set σ' : List (AOut Unit) → Bool → ℝ := fun g => if j ≤ ucX N g then (fun a => if a then 0 else 1) else σ g
  refine adaptive_recall_bound j Bh hB r hr0 hr1 (fun S => freezeK N j y0 (K S)) σ' ?_ ?_ ?_ ?_
  · intro g
    by_cases hfr : j ≤ ucX N g
    · simp only [σ', hfr, if_true]
      refine ⟨fun a => by cases a <;> simp, by simp⟩
    · simp only [σ', hfr, if_false]; exact hσ g
  · intro S hS h z
    unfold freezeK; split_ifs <;> first | exact hK0 S hS h z | norm_num
  · intro S hS h
    by_cases hfr : j ≤ ucX N (h.map Prod.snd)
    · simp [freezeK, hfr]
    · simp only [freezeK, hfr, if_false]; exact hK1 S hS h
  · intro S hS h a
    by_cases hfr : j ≤ ucX N (h.map Prod.snd)
    · cases a <;> simp [freezeK, hfr, σ', o0, Finset.sum_ite_eq']
    · simp only [freezeK, hfr, if_false, σ']; exact hrec S hS h a

end Tail

/-! ## 2. Expected attack rounds before the first catch, and expected damage -/

section Damage

variable {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y]

/-- **E[X] ≤ Σ_{j=1}^{N} hypMiss N Bh j r.** Adversary class: ADAPTIVE_FEEDBACK. -/
theorem expected_uc (y0 : Y) (Bh : ℕ) (hB : Bh ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ)
    (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h z, 0 ≤ K S h z)
    (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h, ∑ z, K S h z ≤ 1)
    (hrec : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h (a : Bool),
      ∑ y, K S h (y, (a, (), false)) ≤
        σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1)) :
    ∑ S : Finset (Fin N), pU N Bh S * val (K S) (fun t => (ucX N t : ℝ)) N []
      ≤ ∑ j ∈ range N, hypMiss N Bh (j + 1) r := by
  have e : ∀ S : Finset (Fin N), val (K S) (fun t => (ucX N t : ℝ)) N [] = ∑ j ∈ range N, val (K S) (pX N (j + 1)) N [] := by
    intro S
    rw [← val_finsum]
    congr 1; funext t; rw [ucX_tail]; rfl
  simp_rw [e, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun j _ => tail_bound y0 (j + 1) Bh hB r hr0 hr1 K σ hσ hK0 hK1 hrec

/-- **Expected damage, halt-on-catch.** Adversary class: ADAPTIVE_FEEDBACK. Each uncaught attack round before the
first catch deals damage ≤ D (per-step cap, F5); the first catch halts (F3), so the damage of any transcript is at
most D · X. Then E[damage] ≤ D · Σ_{j=1}^{N} hypMiss N Bh j r. -/
theorem damage_bound (y0 : Y) (Bh : ℕ) (hB : Bh ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ)
    (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h z, 0 ≤ K S h z)
    (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h, ∑ z, K S h z ≤ 1)
    (hrec : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h (a : Bool),
      ∑ y, K S h (y, (a, (), false)) ≤
        σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1))
    (D : ℝ) (hD : 0 ≤ D) (dmg : List (AOut Unit) → ℝ) (hdD : ∀ t, dmg t ≤ D * ucX N t) :
    ∑ S : Finset (Fin N), pU N Bh S * val (K S) dmg N [] ≤ D * ∑ j ∈ range N, hypMiss N Bh (j + 1) r := by
  have hstep : ∀ S : Finset (Fin N), pU N Bh S * val (K S) dmg N []
      ≤ D * (pU N Bh S * val (K S) (fun t => (ucX N t : ℝ)) N []) := by
    intro S
    by_cases hS : S ∈ AuditBudget.randomSchedules N Bh
    · have := val_mono_on (K S) (fun _ => True) dmg (fun t => D * ucX N t) (hK0 S hS) (fun _ _ _ _ _ => trivial)
        (fun t _ => hdD t) N [] trivial
      rw [val_smul] at this
      calc pU N Bh S * val (K S) dmg N [] ≤ pU N Bh S * (D * val (K S) (fun t => (ucX N t : ℝ)) N []) :=
            mul_le_mul_of_nonneg_left this (pU_nonneg N Bh S)
        _ = _ := by ring
    · simp [pU, hS]
  calc _ ≤ ∑ S : Finset (Fin N), D * (pU N Bh S * val (K S) (fun t => (ucX N t : ℝ)) N []) :=
        Finset.sum_le_sum fun S _ => hstep S
    _ = D * ∑ S : Finset (Fin N), pU N Bh S * val (K S) (fun t => (ucX N t : ℝ)) N [] := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (expected_uc y0 Bh hB r hr0 hr1 K σ hσ hK0 hK1 hrec) hD

/-- **Global cap (F5) and in-flight budget (F3).** If the damage of every transcript is ≤ D · X + F (F: effects
already dispatched when the halt lands) and ≤ G (global cap), then
E[damage] ≤ min(G, D · Σ_{j=1}^{N} hypMiss N Bh j r + F). Adversary class: ADAPTIVE_FEEDBACK. -/
theorem damage_cap_inflight (y0 : Y) (Bh : ℕ) (hB : Bh ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (K : Finset (Fin N) → List (Y × AOut Unit) → Y × AOut Unit → ℝ)
    (σ : List (AOut Unit) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (hK0 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h z, 0 ≤ K S h z)
    (hK1 : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h, ∑ z, K S h z ≤ 1)
    (hrec : ∀ S, S ∈ AuditBudget.randomSchedules N Bh → ∀ h (a : Bool),
      ∑ y, K S h (y, (a, (), false)) ≤
        σ (h.map Prod.snd) a * (if memN S (h.map Prod.snd).length ∧ a = true then 1 - r else 1))
    (D F G : ℝ) (hD : 0 ≤ D) (hF : 0 ≤ F) (hG : 0 ≤ G) (dmg : List (AOut Unit) → ℝ)
    (hdD : ∀ t, dmg t ≤ D * ucX N t + F) (hdG : ∀ t, dmg t ≤ G) :
    ∑ S : Finset (Fin N), pU N Bh S * val (K S) dmg N [] ≤
      min G (D * ∑ j ∈ range N, hypMiss N Bh (j + 1) r + F) := by
  apply le_min
  · calc _ ≤ ∑ S : Finset (Fin N), pU N Bh S * G := by
          apply Finset.sum_le_sum; intro S _
          by_cases hS : S ∈ AuditBudget.randomSchedules N Bh
          · exact mul_le_mul_of_nonneg_left (val_le_const (K S) dmg G (hK0 S hS) (hK1 S hS) hG hdG N [])
              (pU_nonneg N Bh S)
          · simp [pU, hS]
      _ = G := by rw [← Finset.sum_mul, sum_pU Bh hB, one_mul]
  · -- split the damage into the halt-coupled part and the in-flight part
    have hsplit : ∀ S : Finset (Fin N), S ∈ AuditBudget.randomSchedules N Bh →
        val (K S) dmg N [] ≤ D * val (K S) (fun t => (ucX N t : ℝ)) N [] + F := by
      intro S hS
      have h1 := val_mono_on (K S) (fun _ => True) dmg (fun t => D * ucX N t + F) (hK0 S hS)
        (fun _ _ _ _ _ => trivial) (fun t _ => hdD t) N [] trivial
      rw [val_add, val_smul] at h1
      have h2 := val_le_const (K S) (fun _ => F) F (hK0 S hS) (hK1 S hS) hF (fun _ => le_rfl) N []
      linarith
    calc _ ≤ ∑ S : Finset (Fin N), (D * (pU N Bh S * val (K S) (fun t => (ucX N t : ℝ)) N []) + pU N Bh S * F) := by
          apply Finset.sum_le_sum; intro S _
          by_cases hS : S ∈ AuditBudget.randomSchedules N Bh
          · have := mul_le_mul_of_nonneg_left (hsplit S hS) (pU_nonneg N Bh S)
            linarith
          · simp [pU, hS]
      _ = D * ∑ S : Finset (Fin N), pU N Bh S * val (K S) (fun t => (ucX N t : ℝ)) N [] + F := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, sum_pU Bh hB, one_mul]
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left (expected_uc y0 Bh hB r hr0 hr1 K σ hσ hK0 hK1 hrec) hD
          linarith

end Damage

/-! ## 3. Closed forms -/

section Closed

variable {N : ℕ}

/-- with perfect recall only j = 0 survives: hypMiss N B k 1 = C(N−k,B)/C(N,B) -/
theorem hypMiss_one (B k : ℕ) : hypMiss N B k 1 = (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) := by
  unfold hypMiss
  rw [Finset.sum_eq_single 0]
  · simp
  · intro j _ hj; simp [hj]
  · intro h; exact absurd (by simp) h

/-- hockey stick: Σ_{m<n} C(m,B) = C(n,B+1) -/
theorem sum_range_choose_succ (B : ℕ) : ∀ n, ∑ m ∈ range n, Nat.choose m B = Nat.choose n (B + 1) := by
  intro n; induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, Nat.choose_succ_succ', add_comm]

/-- **Perfect recall, exact:** Σ_{j=1}^{N} C(N−j,B)/C(N,B) = (N − B)/(B + 1). -/
theorem expected_r1 (B : ℕ) (hB : B ≤ N) :
    ∑ j ∈ range N, hypMiss N B (j + 1) 1 = ((N : ℝ) - B) / (B + 1) := by
  have hC : (0 : ℝ) < Nat.choose N B := by exact_mod_cast Nat.choose_pos hB
  simp_rw [hypMiss_one]
  rw [← Finset.sum_div]
  have e : ∑ j ∈ range N, (Nat.choose (N - (j + 1)) B : ℝ) = (Nat.choose N (B + 1) : ℝ) := by
    have := sum_range_choose_succ B N
    rw [← Finset.sum_range_reflect] at this
    rw [← this]
    push_cast
    apply Finset.sum_congr rfl; intro j hj
    rw [mem_range] at hj
    congr 2; omega
  rw [e, div_eq_div_iff hC.ne' (by positivity)]
  have key := Nat.choose_succ_right_eq N B
  have : ((Nat.choose N (B + 1) * (B + 1) : ℕ) : ℝ) = ((Nat.choose N B * (N - B) : ℕ) : ℝ) := by rw [key]
  push_cast [Nat.cast_sub hB] at this
  linarith

/-- uniform sums as RS sums -/
theorem sum_pU_eq (B : ℕ) (X : Finset (Fin N) → ℝ) :
    ∑ S : Finset (Fin N), pU N B S * X S
      = (Nat.choose N B : ℝ)⁻¹ * ∑ S ∈ AuditBudget.randomSchedules N B, X S := by
  unfold pU
  simp_rw [ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]

/-- number of B-subsets containing a fixed round: C(N−1, B−1) -/
theorem count_mem (B : ℕ) (hB1 : 1 ≤ B) (a : Fin N) :
    ((AuditBudget.randomSchedules N B).filter (fun S => a ∈ S)).card = Nat.choose (N - 1) (B - 1) := by
  have h := count_inter B 1 1 {a} (card_singleton a) hB1
  rw [Nat.choose_one_right, one_mul] at h
  rw [← h]
  congr 1
  apply Finset.filter_congr
  intro S _
  by_cases ha : a ∈ S
  · simp [ha, Finset.inter_singleton_of_mem ha]
  · simp [ha, Finset.inter_singleton_of_notMem ha]

/-- **One step of the geometric domination** (Chebyshev's sum inequality). For k < N:
hypMiss N B (k+1) r ≤ (1 − rB/N) · hypMiss N B k r. -/
theorem hyp_step (B k : ℕ) (hB : B ≤ N) (hk : k < N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    hypMiss N B (k + 1) r ≤ (1 - r * B / N) * hypMiss N B k r := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  obtain ⟨A, -, hA⟩ := exists_subset_card_eq (show k ≤ (univ : Finset (Fin N)).card by simp; omega)
  -- B = 0: monotonicity suffices
  rcases Nat.eq_zero_or_pos B with hB0 | hBpos
  · subst hB0
    obtain ⟨a, ha⟩ : ∃ a, a ∉ A := by
      by_contra hc; push Not at hc
      have : A = univ := Finset.eq_univ_of_forall hc
      rw [this, card_univ, Fintype.card_fin] at hA; omega
    have hc : (insert a A).card = k + 1 := by rw [card_insert_of_notMem ha, hA]
    rw [← missRecall_closed 0 (k + 1) (insert a A) hc r]
    simp only [Nat.cast_zero, mul_zero, zero_div, sub_zero, one_mul]
    exact miss_ge_k 0 k (insert a A) (by omega) r hr0 hr1
  set C := (Nat.choose N B : ℝ)
  have hC : 0 < C := by show (0 : ℝ) < (Nat.choose N B : ℝ); exact_mod_cast Nat.choose_pos hB
  set RS := AuditBudget.randomSchedules N B
  set f : Finset (Fin N) → ℝ := fun S => (1 - r) ^ (S ∩ A).card
  set g : Finset (Fin N) → ℝ := fun S => ((S \ A).card : ℝ)
  have hT : (Aᶜ).card = N - k := by rw [card_compl, Fintype.card_fin, hA]
  have hfilt : ∀ S : Finset (Fin N), (Aᶜ.filter (fun a => a ∈ S)) = S \ A := by
    intro S; ext x; simp [mem_sdiff]; tauto
  -- hyp(k) = C⁻¹ Σ f
  have hk' : hypMiss N B k r = C⁻¹ * ∑ S ∈ RS, f S := by
    rw [← missRecall_closed B k A hA r, missRecall_const, sum_pU_eq]
  -- (N−k)·hyp(k+1) = C⁻¹ Σ f · ((N−k) − r g)
  have hk1 : ((N - k : ℕ) : ℝ) * hypMiss N B (k + 1) r = C⁻¹ * ∑ S ∈ RS, f S * (((N - k : ℕ) : ℝ) - r * g S) := by
    have h1 : ((N - k : ℕ) : ℝ) * hypMiss N B (k + 1) r = ∑ a ∈ Aᶜ, missRecall B (insert a A) (fun _ => r) := by
      rw [← hT, ← nsmul_eq_mul, ← Finset.sum_const]
      apply Finset.sum_congr rfl; intro a ha
      rw [mem_compl] at ha
      rw [missRecall_closed B (k + 1) (insert a A) (by rw [card_insert_of_notMem ha, hA]) r]
    rw [h1]
    have h2 : ∀ a ∈ Aᶜ, missRecall B (insert a A) (fun _ => r)
        = C⁻¹ * ∑ S ∈ RS, f S * (if a ∈ S then 1 - r else 1) := by
      intro a ha
      rw [mem_compl] at ha
      rw [missRecall_const, sum_pU_eq]
      congr 1
      apply Finset.sum_congr rfl; intro S _
      by_cases haS : a ∈ S
      · rw [Finset.inter_insert_of_mem haS, card_insert_of_notMem (fun h => ha (mem_inter.1 h).2)]
        simp [f, haS, pow_succ]
      · rw [Finset.inter_insert_of_notMem haS]; simp [f, haS]
    rw [Finset.sum_congr rfl h2, ← Finset.mul_sum, Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl; intro S hS
    rw [← Finset.mul_sum]
    congr 1
    have e1 : ∀ a, (if a ∈ S then 1 - r else (1 : ℝ)) = 1 - r * (if a ∈ S then 1 else 0) := by
      intro a; split_ifs <;> ring
    simp_rw [e1]
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, hT, ← Finset.mul_sum, Finset.sum_boole,
      hfilt S]
  -- Σ_{RS} g = (N−k) · B · C / N
  have hg : ∑ S ∈ RS, g S * N = ((N - k : ℕ) : ℝ) * B * C := by
    have e1 : ∀ S, g S = ∑ a ∈ Aᶜ, (if a ∈ S then (1 : ℝ) else 0) := by
      intro S
      rw [Finset.sum_boole, hfilt S]
    rw [← Finset.sum_mul]
    simp_rw [e1]
    rw [Finset.sum_comm]
    have e2 : ∀ a ∈ Aᶜ, ∑ S ∈ RS, (if a ∈ S then (1 : ℝ) else 0) = (Nat.choose (N - 1) (B - 1) : ℝ) := by
      intro a _
      rw [Finset.sum_boole, count_mem B hBpos a]
    rw [Finset.sum_congr rfl e2, Finset.sum_const, nsmul_eq_mul, hT]
    have key := Nat.add_one_mul_choose_eq (N - 1) (B - 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ N), Nat.sub_add_cancel hBpos] at key
    have key' : (N : ℝ) * (Nat.choose (N - 1) (B - 1) : ℝ) = C * B := by
      show (N : ℝ) * (Nat.choose (N - 1) (B - 1) : ℝ) = (Nat.choose N B : ℝ) * B; exact_mod_cast key
    rw [mul_assoc, mul_comm (Nat.choose (N - 1) (B - 1) : ℝ) (N : ℝ), key']
    ring
  -- Chebyshev
  have hmono : MonovaryOn f g (RS : Set (Finset (Fin N))) := by
    intro S1 hS1 S2 hS2 hlt
    rw [mem_coe] at hS1 hS2
    simp only [RS, AuditBudget.randomSchedules, mem_powersetCard, subset_univ, true_and] at hS1 hS2
    have e1 := card_sdiff_add_card_inter S1 A
    have e2 := card_sdiff_add_card_inter S2 A
    simp only [g] at hlt
    have hlt' : (S1 \ A).card < (S2 \ A).card := by exact_mod_cast hlt
    simp only [f]
    apply pow_le_pow_of_le_one (by linarith) (by linarith)
    omega
  have hcheb := hmono.sum_mul_sum_le_card_mul_sum
  have hcardRS : (RS.card : ℝ) = C := by simp [RS, AuditBudget.randomSchedules, card_powersetCard, C]
  rw [hcardRS] at hcheb
  -- Σ f g ≥ (N−k)·B/N · Σ f
  have hfg : ((N - k : ℕ) : ℝ) * B / N * ∑ S ∈ RS, f S ≤ ∑ S ∈ RS, f S * g S := by
    have hsg : ∑ S ∈ RS, g S = ((N - k : ℕ) : ℝ) * B * C / N := by
      rw [eq_div_iff hN.ne', ← hg, Finset.sum_mul]
    rw [hsg] at hcheb
    have h2 : C * (((N - k : ℕ) : ℝ) * B / N * ∑ S ∈ RS, f S) ≤ C * ∑ S ∈ RS, f S * g S := by
      calc C * (((N - k : ℕ) : ℝ) * B / N * ∑ S ∈ RS, f S)
          = (∑ S ∈ RS, f S) * (((N - k : ℕ) : ℝ) * B * C / N) := by ring
        _ ≤ _ := hcheb
    exact le_of_mul_le_mul_left h2 hC
  have hNk : (0 : ℝ) < ((N - k : ℕ) : ℝ) := by exact_mod_cast (show 0 < N - k by omega)
  have hmain : ((N - k : ℕ) : ℝ) * hypMiss N B (k + 1) r ≤ ((N - k : ℕ) : ℝ) * ((1 - r * B / N) * hypMiss N B k r) := by
    rw [hk1, hk']
    have hexp : ∑ S ∈ RS, f S * (((N - k : ℕ) : ℝ) - r * g S)
        = ((N - k : ℕ) : ℝ) * ∑ S ∈ RS, f S - r * ∑ S ∈ RS, f S * g S := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro S _; ring
    rw [hexp]
    have hCi : 0 < C⁻¹ := inv_pos.2 hC
    have : r * (((N - k : ℕ) : ℝ) * B / N * ∑ S ∈ RS, f S) ≤ r * ∑ S ∈ RS, f S * g S :=
      mul_le_mul_of_nonneg_left hfg hr0
    have hgoal : C⁻¹ * (((N - k : ℕ) : ℝ) * ∑ S ∈ RS, f S - r * ∑ S ∈ RS, f S * g S)
        ≤ C⁻¹ * (((N - k : ℕ) : ℝ) * ∑ S ∈ RS, f S - r * (((N - k : ℕ) : ℝ) * B / N * ∑ S ∈ RS, f S)) :=
      mul_le_mul_of_nonneg_left (by linarith) hCi.le
    refine hgoal.trans (le_of_eq ?_)
    field_simp
  exact le_of_mul_le_mul_left hmain hNk

theorem hypMiss_zero (B : ℕ) (hB : B ≤ N) (r : ℝ) : hypMiss N B 0 r = 1 := by
  have hC : (Nat.choose N B : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hB).ne'
  simp [hypMiss, hC]

/-- **Geometric domination:** hypMiss N B k r ≤ (1 − rB/N)^k for k ≤ N (sampling audit rounds without replacement
is at least as good as independent per-round catching with probability rB/N). -/
theorem hyp_geom (B : ℕ) (hB : B ≤ N) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ∀ k, k ≤ N → hypMiss N B k r ≤ (1 - r * B / N) ^ k := by
  intro k
  induction k with
  | zero => intro _; rw [hypMiss_zero B hB, pow_zero]
  | succ k ih =>
    intro hk
    have hq : 0 ≤ 1 - r * B / N := by
      rcases Nat.eq_zero_or_pos N with h0 | hpos
      · omega
      · have hN : (0 : ℝ) < N := by exact_mod_cast hpos
        have : r * B / N ≤ 1 := by
          rw [div_le_one hN]
          have : (B : ℝ) ≤ N := by exact_mod_cast hB
          nlinarith
        linarith
    calc hypMiss N B (k + 1) r ≤ (1 - r * B / N) * hypMiss N B k r := hyp_step B k hB (by omega) r hr0 hr1
      _ ≤ (1 - r * B / N) * (1 - r * B / N) ^ k := mul_le_mul_of_nonneg_left (ih (by omega)) hq
      _ = _ := by ring

/-- **E[X] ≤ (N − rB)/(rB)** for 0 < r ≤ 1, 0 < B ≤ N. -/
theorem expected_geom (B : ℕ) (hB : B ≤ N) (hB0 : 0 < B) (r : ℝ) (hr0 : 0 < r) (hr1 : r ≤ 1) :
    ∑ j ∈ range N, hypMiss N B (j + 1) r ≤ ((N : ℝ) - r * B) / (r * B) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hBr : (0 : ℝ) < r * B := mul_pos hr0 (by exact_mod_cast hB0)
  set q := 1 - r * B / N with hq
  have hq1 : q < 1 := by rw [hq]; have : 0 < r * B / N := div_pos hBr hN; linarith
  have hq0 : 0 ≤ q := by
    rw [hq]
    have : r * B / N ≤ 1 := by
      rw [div_le_one hN]
      have : (B : ℝ) ≤ N := by exact_mod_cast hB
      nlinarith
    linarith
  have hgeo : ∀ n, (∑ j ∈ range n, q ^ (j + 1)) * (1 - q) = q - q ^ (n + 1) := by
    intro n; induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, add_mul, ih]; ring
  calc ∑ j ∈ range N, hypMiss N B (j + 1) r ≤ ∑ j ∈ range N, q ^ (j + 1) := by
        apply Finset.sum_le_sum; intro j hj
        rw [mem_range] at hj
        exact hyp_geom B hB r hr0.le hr1 (j + 1) (by omega)
    _ ≤ q / (1 - q) := by
        rw [le_div_iff₀ (by linarith), hgeo]
        have : 0 ≤ q ^ (N + 1) := pow_nonneg hq0 _
        linarith
    _ = _ := by
        rw [hq]; field_simp; ring

end Closed

/-! ## 4. Witnesses -/

section Witnesses

/-- **Halt coupling is necessary.** An attacker that attacks every round and is CAUGHT every round: if catches are
only logged, it deals damage in all N rounds (N·D at per-step damage D), while the halt-coupled count X is 0. -/
theorem no_halt_damage (N : ℕ) (D : ℝ) :
    val (fun (_ : List (Unit × AOut Unit)) z => if z = ((), ((true, (), true) : AOut Unit)) then (1 : ℝ) else 0)
        (fun t => D * (attackSet (N := N) t).card) N [] = N * D ∧
    val (fun (_ : List (Unit × AOut Unit)) z => if z = ((), ((true, (), true) : AOut Unit)) then (1 : ℝ) else 0)
        (fun t => D * ucX N t) N [] = 0 := by
  constructor
  · rw [val_det]
    simp only [List.map_nil, List.nil_append]
    have : attackSet (N := N) (List.replicate N ((true, (), true) : AOut Unit)) = univ := by
      ext i; simp [attackSet, attacked]
    rw [this, card_univ, Fintype.card_fin]; ring
  · rw [val_det]
    simp only [List.map_nil, List.nil_append]
    have : pre (List.replicate N ((true, (), true) : AOut Unit)) = [] := by
      cases N with
      | zero => rfl
      | succ n => simp [pre, List.replicate_succ, caughtFlag]
    have h0 : ucX N (List.replicate N ((true, (), true) : AOut Unit)) = 0 := by
      unfold ucX; rw [this]
      simp [attackSet, attacked]
    rw [h0]; simp

/-- **The per-step cap is necessary.** One round, never audited, the attacker attacks once: with per-step damage M
the expected damage is M, for every M (no bound independent of the per-step cap). -/
theorem no_cap_damage (M : ℝ) :
    val (fun (_ : List (Unit × AOut Unit)) z => if z = ((), ((true, (), false) : AOut Unit)) then (1 : ℝ) else 0)
        (fun t => M * ucX 1 t) 1 [] = M := by
  rw [val_det]
  have h1 : ucX 1 (List.replicate 1 ((true, (), false) : AOut Unit)) = 1 := by decide
  simp only [List.map_nil, List.nil_append]
  rw [h1]; simp

end Witnesses

/-! ## 5. Numbers: N = 100, Bh = 10 -/

/-- perfect recall: E[attack rounds before the first catch] ≤ 90/11 ≈ 8.18 for every adaptive attacker -/
theorem example_r1 : ∑ j ∈ range 100, hypMiss 100 10 (j + 1) 1 = 90 / 11 := by
  rw [expected_r1 10 (by norm_num)]; norm_num

/-- recall 1/2: E[attack rounds before the first catch] ≤ 19 -/
theorem example_r_half : ∑ j ∈ range 100, hypMiss 100 10 (j + 1) (1 / 2) ≤ 19 := by
  have h := expected_geom (N := 100) 10 (by norm_num) (by norm_num) (1 / 2) (by norm_num) (by norm_num)
  refine h.trans (le_of_eq ?_)
  norm_num

end ControlStack.DamageBound

#print axioms ControlStack.DamageBound.tail_bound
#print axioms ControlStack.DamageBound.expected_uc
#print axioms ControlStack.DamageBound.damage_bound
#print axioms ControlStack.DamageBound.damage_cap_inflight
#print axioms ControlStack.DamageBound.hypMiss_one
#print axioms ControlStack.DamageBound.expected_r1
#print axioms ControlStack.DamageBound.hyp_step
#print axioms ControlStack.DamageBound.hyp_geom
#print axioms ControlStack.DamageBound.expected_geom
#print axioms ControlStack.DamageBound.no_halt_damage
#print axioms ControlStack.DamageBound.no_cap_damage
#print axioms ControlStack.DamageBound.example_r1
#print axioms ControlStack.DamageBound.example_r_half
