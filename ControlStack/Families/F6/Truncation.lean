/-
F6: the truncation argument for the split-audit game. The bounds of `SplitAudit` are stated for the event
`FlagBudget.totSucc k` = "at least k attack rounds and never caught by round N". The event a designer cares about is
`prefSucc k` = "k attacks were released before the first catch" (the harm is done even if the attacker is caught
later). `prefSucc` is the larger event (`totSucc_le_prefSucc`).

Result. `prefix_eq_truncated`: for every schedule S, flag law τ and attacker σ,
  P_σ(k attacks released before the first catch) = P_{stopAfter k σ}(≥ k attacks, never caught),
where `stopAfter k σ` plays σ until the transcript holds k attack rounds and never attacks afterwards. Since
`stopAfter k σ` is again an attacker (`stopAfter_isDist`), every bound proved for `totSucc` against all attackers
holds for `prefSucc`: `split_hidden_bound_prefix`, `split_flag_bound_prefix`, `split_product_bound_prefix`.

Proof. Write `lp t` for the longest catch-free prefix of t; then `prefReach k t ↔ k ≤ attackCount (lp t)`
(`prefReach_eq`).
A. `val_stop_eq`: stopping does not change the prefix event. While the transcript holds fewer than k attacks the two
   attackers are the same law. Once it holds k attacks the prefix event is decided (`prefSucc_stable`), and a kernel
   whose rows sum to 1 gives a decided event its value (`val_const`).
B. `val_stop_pref_eq_tot`: on the transcripts the stopped attacker can produce (every caught round is an attack
   round, at most k attack rounds, length ≤ N) the two events coincide (`prefSucc_eq_totSucc`).

Limits (what is NOT claimed).
- Only the split kernel `SplitAudit.splitK` is covered (catch is a deterministic function of schedule, history,
  attack bit and flag, and a non-attack round is never caught). No statement is made for an arbitrary kernel.
- A caught attack is not counted as released: `prefSucc k` needs k attack rounds strictly before the first catch.
- Classical mathematics (a stopping argument). No novelty is claimed.
-/
import ControlStack.Families.F6.SplitAudit

namespace ControlStack.Truncation

open Finset ControlStack.Leakage ControlStack.Covert ControlStack.ReservedAudit ControlStack.FlagBudget
  ControlStack.SplitAudit

/-! ## 1. Definitions -/

section Defs

/-- number of attack rounds in a transcript -/
def attackCount (t : List (AOut Bool)) : ℕ := t.countP (fun o => o.1)

/-- k attacks were released before the first catch (c = attacks released so far). A caught round ends the scan
without counting its attack. -/
def prefReachAux (k : ℕ) : ℕ → List (AOut Bool) → Bool
  | c, [] => decide (k ≤ c)
  | c, o :: t => if k ≤ c then true else if o.2.2 then false else prefReachAux k (c + (if o.1 then 1 else 0)) t

def prefReach (k : ℕ) (t : List (AOut Bool)) : Bool := prefReachAux k 0 t

/-- the prefix event: k attacks released before the first catch -/
noncomputable def prefSucc (k : ℕ) (t : List (AOut Bool)) : ℝ := if prefReach k t then 1 else 0

/-- the attacker σ, stopped after its k-th attack -/
noncomputable def stopAfter (k : ℕ) (σ : List (AOut Bool) → Bool → ℝ) : List (AOut Bool) → Bool → ℝ :=
  fun g a => if k ≤ attackCount g then (if a then 0 else 1) else σ g a

/-- no round of the transcript is caught -/
def liveB (t : List (AOut Bool)) : Bool := t.all (fun o => !o.2.2)

/-- the longest catch-free prefix -/
def lp (t : List (AOut Bool)) : List (AOut Bool) := t.takeWhile (fun o => !o.2.2)

end Defs

/-! ## 2. Bookkeeping on transcripts -/

section Book

theorem attackCount_snoc (t : List (AOut Bool)) (o : AOut Bool) :
    attackCount (t ++ [o]) = attackCount t + (if o.1 then 1 else 0) := by
  unfold attackCount
  rw [List.countP_append]
  cases h : o.1 <;> simp [h]

theorem attackCount_append (t u : List (AOut Bool)) : attackCount (t ++ u) = attackCount t + attackCount u := by
  unfold attackCount
  rw [List.countP_append]

theorem liveInd_eq (t : List (AOut Bool)) : liveInd caughtFlag t = if liveB t then 1 else 0 := rfl

theorem lp_of_live (t : List (AOut Bool)) (h : liveB t = true) : lp t = t := by
  induction t with
  | nil => rfl
  | cons o t ih =>
    have h' : o.2.2 = false ∧ liveB t = true := by simpa [liveB] using h
    have := ih h'.2
    simp only [lp] at this ⊢
    simp [h'.1, this]

theorem lp_append_of_live (g u : List (AOut Bool)) (h : liveB g = true) : lp (g ++ u) = g ++ lp u :=
  List.takeWhile_append_of_pos (List.all_eq_true.1 h)

theorem lp_append_of_dead (g u : List (AOut Bool)) (h : liveB g = false) : lp (g ++ u) = lp g := by
  induction g with
  | nil => simp [liveB] at h
  | cons o g ih =>
    cases hc : o.2.2
    · have hg : liveB g = false := by simpa [liveB, hc] using h
      have := ih hg
      simp only [lp] at this ⊢
      simp [hc, this]
    · simp [lp, hc]

/-- the scan, in closed form: k attacks released before the first catch iff the catch-free prefix holds k attacks -/
theorem prefReachAux_eq (k : ℕ) (t : List (AOut Bool)) :
    ∀ c, prefReachAux k c t = decide (k ≤ c + attackCount (lp t)) := by
  induction t with
  | nil => intro c; simp [prefReachAux, lp, attackCount]
  | cons o t ih =>
    intro c
    obtain ⟨a, f, d⟩ := o
    by_cases hk : k ≤ c
    · have : k ≤ c + attackCount (lp ((a, f, d) :: t)) := by omega
      simp [prefReachAux, hk, this]
    · cases d
      · have e : attackCount (lp ((a, f, false) :: t)) = (if a then 1 else 0) + attackCount (lp t) := by
          cases a <;> simp [lp, attackCount]
          omega
        simp only [prefReachAux, hk, ite_false, Bool.false_eq_true, ih, e, Nat.add_assoc]
      · simp [prefReachAux, hk, lp, attackCount]

theorem prefReach_eq (k : ℕ) (t : List (AOut Bool)) : prefReach k t = decide (k ≤ attackCount (lp t)) := by
  unfold prefReach
  rw [prefReachAux_eq, Nat.zero_add]

/-- once the transcript holds k attack rounds, the prefix event is decided -/
theorem prefSucc_stable (k : ℕ) (g u : List (AOut Bool)) (hk : k ≤ attackCount g) :
    prefSucc k (g ++ u) = prefSucc k g := by
  unfold prefSucc
  rw [prefReach_eq, prefReach_eq]
  cases hl : liveB g
  · rw [lp_append_of_dead g u hl]
  · rw [lp_append_of_live g u hl, lp_of_live g hl, attackCount_append]
    have : k ≤ attackCount g + attackCount (lp u) := by omega
    simp [hk, this]

/-- if every caught round is an attack round, a caught transcript has an attack outside its catch-free prefix -/
theorem attackCount_lp_lt (t : List (AOut Bool)) (hc : ∀ o ∈ t, o.2.2 = true → o.1 = true)
    (hl : liveB t = false) : attackCount (lp t) < attackCount t := by
  induction t with
  | nil => simp [liveB] at hl
  | cons o t ih =>
    obtain ⟨a, f, d⟩ := o
    cases d
    · have hg : liveB t = false := by simpa [liveB] using hl
      have := ih (fun o ho => hc o (List.mem_cons_of_mem _ ho)) hg
      have e1 : attackCount (lp ((a, f, false) :: t)) = (if a then 1 else 0) + attackCount (lp t) := by
        cases a <;> simp [lp, attackCount]
        omega
      have e2 : attackCount ((a, f, false) :: t) = (if a then 1 else 0) + attackCount t := by
        cases a <;> simp [attackCount]
        omega
      omega
    · have ha : a = true := hc (a, f, true) (List.mem_cons_self) rfl
      subst ha
      simp [lp, attackCount]

variable {N : ℕ}

theorem attacked_of_ge (t : List (AOut Bool)) (i : ℕ) (h : t.length ≤ i) : attacked t i = false := by
  unfold attacked
  rw [List.getElem?_eq_none (by omega)]

/-- on a transcript of length ≤ N, `attackSet` counts every attack round -/
theorem card_attackSet_eq (t : List (AOut Bool)) (ht : t.length ≤ N) :
    (attackSet (N := N) t).card = attackCount t := by
  induction t using List.reverseRecOn with
  | nil => simp [attackSet_nil, attackCount]
  | append_singleton t o ih =>
    have hlen : t.length < N := by simpa using ht
    have ih' := ih (by omega)
    rw [attackCount_snoc, ← ih']
    cases ho : o.1
    · have e : attackSet (N := N) (t ++ [o]) = attackSet (N := N) t := by
        ext i
        simp only [attackSet, mem_filter, mem_univ, true_and]
        rw [attacked_snoc]
        by_cases h1 : (i : ℕ) < t.length
        · simp [h1]
        · have := attacked_of_ge t i (by omega)
          by_cases h2 : (i : ℕ) = t.length
          · simp [h2, ho, attacked_of_ge t t.length le_rfl]
          · simp [h1, h2, this]
      simp [e]
    · have hnot : (⟨t.length, hlen⟩ : Fin N) ∉ attackSet (N := N) t := by
        simp [attackSet, attacked_of_ge t t.length le_rfl]
      have e : attackSet (N := N) (t ++ [o]) = insert (⟨t.length, hlen⟩ : Fin N) (attackSet (N := N) t) := by
        ext i
        simp only [attackSet, mem_filter, mem_univ, true_and, mem_insert]
        rw [attacked_snoc]
        by_cases h1 : (i : ℕ) < t.length
        · have hne : i ≠ (⟨t.length, hlen⟩ : Fin N) := fun h => by rw [h] at h1; simp at h1
          simp [h1, hne]
        · have := attacked_of_ge t i (by omega)
          by_cases h2 : (i : ℕ) = t.length
          · have : i = (⟨t.length, hlen⟩ : Fin N) := Fin.ext h2
            simp [ho, this]
          · have hne : i ≠ (⟨t.length, hlen⟩ : Fin N) := fun h => h2 (by rw [h])
            simp [h1, h2, hne, this]
      rw [e, card_insert_of_notMem hnot]
      simp

/-- on the transcripts a stopped attacker can produce, the two events coincide -/
theorem prefSucc_eq_totSucc (k : ℕ) (t : List (AOut Bool)) (ht : t.length ≤ N)
    (hc : ∀ o ∈ t, o.2.2 = true → o.1 = true) (hk : attackCount t ≤ k) :
    prefSucc k t = totSucc (N := N) k t := by
  unfold prefSucc totSucc
  rw [prefReach_eq, card_attackSet_eq t ht, liveInd_eq]
  cases hl : liveB t
  · have := attackCount_lp_lt t hc hl
    have hn : ¬ k ≤ attackCount (lp t) := by omega
    simp [hn]
  · rw [lp_of_live t hl]
    by_cases h : k ≤ attackCount t <;> simp [h]

/-- the event is at least as large as the one already bounded -/
theorem totSucc_le_prefSucc (k : ℕ) (t : List (AOut Bool)) (ht : t.length ≤ N) :
    totSucc (N := N) k t ≤ prefSucc k t := by
  unfold prefSucc totSucc
  rw [prefReach_eq, card_attackSet_eq t ht, liveInd_eq]
  cases hl : liveB t
  · by_cases h : k ≤ attackCount (lp t) <;> simp [h]
  · rw [lp_of_live t hl]
    by_cases h : k ≤ attackCount t <;> simp [h]

end Book

/-! ## 3. The stopped attacker -/

section Stop

variable {N : ℕ}

theorem stopAfter_isDist (k : ℕ) (σ : List (AOut Bool) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g)) :
    ∀ g, IsDist (stopAfter k σ g) := by
  intro g
  by_cases hk : k ≤ attackCount g
  · have e : stopAfter k σ g = fun a => if a then 0 else 1 := by
      funext a; simp [stopAfter, hk]
    rw [e]
    exact ⟨fun a => by cases a <;> simp, by simp⟩
  · have e : stopAfter k σ g = σ g := by
      funext a; simp [stopAfter, hk]
    rw [e]
    exact hσ g

/-- the rows of the split kernel sum to exactly 1 -/
theorem splitK_row (σ : List (AOut Bool) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (τ : Finset (Fin N) → List (AOut Bool) → Bool → Bool → ℝ) (hτ : ∀ S g a, IsDist (τ S g a))
    (S : Finset (Fin N)) (g : List (AOut Bool)) : ∑ a : Bool, ∑ f : Bool, σ g a * τ S g a f = 1 := by
  simp only [← Finset.mul_sum, (hτ _ _ _).2, mul_one]
  exact (hσ g).2

/-- a payoff that is already decided at the current history has that value -/
theorem val_const (Bf : ℕ) (σ : List (AOut Bool) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (τ : Finset (Fin N) → List (AOut Bool) → Bool → Bool → ℝ) (hτ : ∀ S g a, IsDist (τ S g a))
    (S : Finset (Fin N)) (pay : List (AOut Bool) → ℝ) (c : ℝ) :
    ∀ n (h : List (Unit × AOut Bool)), (∀ u, pay (h.map Prod.snd ++ u) = c) →
      val (splitK Bf σ τ S) pay n h = c := by
  intro n; induction n with
  | zero => intro h hp; simpa [Leakage.val] using hp []
  | succ n ih =>
    intro h hp
    rw [splitK_val_succ]
    have hc : ∀ a f, val (splitK Bf σ τ S) pay n
        (h ++ [((), (a, f, catchRule Bf S (h.map Prod.snd) a f))]) = c := by
      intro a f
      apply ih
      intro u
      simpa using hp ((a, f, catchRule Bf S (h.map Prod.snd) a f) :: u)
    simp only [hc, ← Finset.sum_mul]
    rw [splitK_row σ hσ τ hτ S, one_mul]

/-- **Step A.** Stopping after the k-th attack does not change the probability of the prefix event. -/
theorem val_stop_eq (k Bf : ℕ) (σ : List (AOut Bool) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (τ : Finset (Fin N) → List (AOut Bool) → Bool → Bool → ℝ) (hτ : ∀ S g a, IsDist (τ S g a))
    (S : Finset (Fin N)) :
    ∀ n (h : List (Unit × AOut Bool)),
      val (splitK Bf σ τ S) (prefSucc k) n h = val (splitK Bf (stopAfter k σ) τ S) (prefSucc k) n h := by
  intro n; induction n with
  | zero => intro h; rfl
  | succ n ih =>
    intro h
    by_cases hk : k ≤ attackCount (h.map Prod.snd)
    · rw [val_const Bf σ hσ τ hτ S (prefSucc k) (prefSucc k (h.map Prod.snd)) (n + 1) h
          (fun u => prefSucc_stable k _ u hk),
        val_const Bf (stopAfter k σ) (stopAfter_isDist k σ hσ) τ hτ S (prefSucc k) (prefSucc k (h.map Prod.snd))
          (n + 1) h (fun u => prefSucc_stable k _ u hk)]
    · have e : ∀ a, stopAfter k σ (h.map Prod.snd) a = σ (h.map Prod.snd) a := fun a => by
        simp [stopAfter, hk]
      rw [splitK_val_succ, splitK_val_succ]
      simp only [e, ih]

/-- **Step B.** Against the stopped attacker the prefix event and "≥ k attacks, never caught" have the same
probability: it never attacks once k attack rounds are on the transcript, and a non-attack round is never caught. -/
theorem val_stop_pref_eq_tot (k Bf : ℕ) (σ : List (AOut Bool) → Bool → ℝ)
    (τ : Finset (Fin N) → List (AOut Bool) → Bool → Bool → ℝ) (S : Finset (Fin N)) :
    ∀ n (h : List (Unit × AOut Bool)), h.length + n ≤ N →
      (∀ o ∈ h.map Prod.snd, o.2.2 = true → o.1 = true) → attackCount (h.map Prod.snd) ≤ k →
      val (splitK Bf (stopAfter k σ) τ S) (prefSucc k) n h =
        val (splitK Bf (stopAfter k σ) τ S) (totSucc (N := N) k) n h := by
  intro n; induction n with
  | zero =>
    intro h hl hc hk
    simp only [Leakage.val]
    exact prefSucc_eq_totSucc k _ (by simpa using hl) hc hk
  | succ n ih =>
    intro h hl hc hk
    rw [splitK_val_succ, splitK_val_succ]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro f _
    by_cases hz : stopAfter k σ (h.map Prod.snd) a = 0
    · rw [hz]; simp
    · congr 1
      apply ih
      · simp only [List.length_append, List.length_singleton]; omega
      · intro o ho
        simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_singleton] at ho
        rcases ho with ho | rfl
        · exact hc o ho
        · intro hcr
          simp only [catchRule, Bool.and_eq_true] at hcr
          exact hcr.1
      · simp only [List.map_append, List.map_cons, List.map_nil, attackCount_snoc]
        cases a
        · simpa using hk
        · have hlt : ¬ k ≤ attackCount (h.map Prod.snd) := by
            intro hge; apply hz; simp [stopAfter, hge]
          simp only [ite_true]; omega

/-- **Truncation.** For every schedule S, flag law τ and attacker σ, the probability that k attacks are released
before the first catch equals the probability that the stopped attacker makes ≥ k attacks and is never caught. -/
theorem prefix_eq_truncated (k Bf : ℕ) (σ : List (AOut Bool) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (τ : Finset (Fin N) → List (AOut Bool) → Bool → Bool → ℝ) (hτ : ∀ S g a, IsDist (τ S g a))
    (S : Finset (Fin N)) :
    val (splitK Bf σ τ S) (prefSucc k) N [] = val (splitK Bf (stopAfter k σ) τ S) (totSucc (N := N) k) N [] := by
  rw [val_stop_eq k Bf σ hσ τ hτ S N []]
  exact val_stop_pref_eq_tot k Bf σ τ S N [] (by simp) (by simp) (by simp [attackCount])

end Stop

/-! ## 4. The SplitAudit bounds for the prefix event -/

section Bounds

variable {N : ℕ}

/-- **Hidden reserved audits, prefix event.** `SplitAudit.split_hidden_bound` for "k attacks released before the
first catch". -/
theorem split_hidden_bound_prefix (k Bh Bf : ℕ) (hB : Bh ≤ N) (σ : List (AOut Bool) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (τ₀ : List (AOut Bool) → Bool → Bool → ℝ) (hτ : ∀ g a, IsDist (τ₀ g a)) :
    ∑ S : Finset (Fin N), pU N Bh S * val (splitK Bf σ (fun _ => τ₀) S) (prefSucc k) N []
      ≤ (Nat.choose (N - k) Bh : ℝ) / (Nat.choose N Bh : ℝ) := by
  have e : ∀ S : Finset (Fin N), val (splitK Bf σ (fun _ => τ₀) S) (prefSucc k) N [] =
      val (splitK Bf (stopAfter k σ) (fun _ => τ₀) S) (totSucc (N := N) k) N [] :=
    fun S => prefix_eq_truncated k Bf σ hσ (fun _ => τ₀) (fun _ => hτ) S
  simp_rw [e]
  exact split_hidden_bound k Bh Bf hB (stopAfter k σ) (stopAfter_isDist k σ hσ) τ₀ hτ

/-- **Flag-triggered audits, prefix event, every fixed schedule.** `SplitAudit.split_flag_bound` for "k attacks
released before the first catch". -/
theorem split_flag_bound_prefix (k Bf : ℕ) (ρ α : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (σ : List (AOut Bool) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (τ : Finset (Fin N) → List (AOut Bool) → Bool → Bool → ℝ) (hτ : ∀ S g a, IsDist (τ S g a))
    (hrec : ∀ S g, flagCount g < Bf → ρ ≤ τ S g true true)
    (hfp : ∀ S g, flagCount g < Bf → τ S g false true ≤ α) (S : Finset (Fin N)) :
    val (splitK Bf σ τ S) (prefSucc k) N [] ≤ (1 - ρ) ^ k + binTail α Bf N 0 := by
  rw [prefix_eq_truncated k Bf σ hσ τ hτ S]
  exact split_flag_bound k Bf ρ α hρ0 hρ1 hα0 hα1 (stopAfter k σ) (stopAfter_isDist k σ hσ) τ hτ hrec hfp S

/-- **Composition, prefix event.** `SplitAudit.split_product_bound` for "k attacks released before the first
catch". -/
theorem split_product_bound_prefix (k Bh Bf : ℕ) (hB : Bh ≤ N) (ρ α : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hα0 : 0 ≤ α)
    (hα1 : α ≤ 1) (σ : List (AOut Bool) → Bool → ℝ) (hσ : ∀ g, IsDist (σ g))
    (τ₀ : List (AOut Bool) → Bool → Bool → ℝ) (hτ : ∀ g a, IsDist (τ₀ g a))
    (hrec : ∀ g, flagCount g < Bf → ρ ≤ τ₀ g true true)
    (hfp : ∀ g, flagCount g < Bf → τ₀ g false true ≤ α) :
    ∑ S : Finset (Fin N), pU N Bh S * val (splitK Bf σ (fun _ => τ₀) S) (prefSucc k) N []
      ≤ (Nat.choose (N - k) Bh : ℝ) / (Nat.choose N Bh : ℝ) * (1 - ρ) ^ k + binTail α Bf N 0 := by
  have e : ∀ S : Finset (Fin N), val (splitK Bf σ (fun _ => τ₀) S) (prefSucc k) N [] =
      val (splitK Bf (stopAfter k σ) (fun _ => τ₀) S) (totSucc (N := N) k) N [] :=
    fun S => prefix_eq_truncated k Bf σ hσ (fun _ => τ₀) (fun _ => hτ) S
  simp_rw [e]
  exact split_product_bound k Bh Bf hB ρ α hρ0 hρ1 hα0 hα1 (stopAfter k σ) (stopAfter_isDist k σ hσ) τ₀ hτ hrec hfp

end Bounds

end ControlStack.Truncation

#print axioms ControlStack.Truncation.stopAfter_isDist
#print axioms ControlStack.Truncation.prefix_eq_truncated
#print axioms ControlStack.Truncation.totSucc_le_prefSucc
#print axioms ControlStack.Truncation.split_hidden_bound_prefix
#print axioms ControlStack.Truncation.split_flag_bound_prefix
#print axioms ControlStack.Truncation.split_product_bound_prefix
