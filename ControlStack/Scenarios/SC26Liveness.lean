/-
SC-26 LIVENESS: the formal counterpart of usefulness. Every result before this file is a safety property; here the
honest path makes progress, and the only things that can stop it are the prices of safety.

Abstract model (`ControlStack.SC26`, deployed checks `full`):
- `honest_progress`: from any invariant (reachable) state that is not halted, for a request `k` with an approval of
  exactly its payload by an approver other than the requester, not yet reserved, and within the cap, the honest
  continuation [execute, deliver, arrive] pays it: `(k, tx) ∈ bank`, exactly once (`paid_once`).
- `progress_interleaved`: arbitrary legal adversary operations interleaved before, between and after the three honest
  steps (requests, approvals, executions, deliveries, arrivals, direct bank calls, halts). At the end, either the
  payment is in the bank, or the gate is halted, or, at the moment of the honest `execute`, `k` was unreserved and
  the cap was exhausted. If someone else executed `k` first, the honest deliver and arrive still pay it. Nothing else
  blocks progress.
- Availability prices of safety:
  - `halted_blocks`: once halted, a request with nothing in the bank and nothing in flight is never paid;
  - `cap_exhausted_blocks`: once the remaining cap is below a request's amount and it is unreserved, it is never
    reserved and never paid. Spending is never refunded.

Concrete machine (`SC26Refinement`, crashes and re-transmission):
- `crash_tolerant_progress`: from a reachable concrete state with a logged intent for key `k`, any trace of the form
  pre ++ [recover] ++ mid ++ [bankProcess k] ++ post (any legal operations, any number of crashes anywhere), where the
  gate is not halted when `recover` runs, ends with `k` paid, exactly once. The FAIRNESS premise is that a recover and
  a later bank processing of `k` occur (cf. `HaltLiveness.DeliveredWithin`).
- `crashes_forever_no_progress`: without such a recover (crashes only), a logged intent is never paid. Liveness needs
  the fairness premise.

Adversary class: TRACE_ARBITRARY under `legal` (no forged gate credential). Premises: the scheduler premise above for
the concrete result; the honest approver approves (an `Approved` record must exist). No new mathematics.
-/
import Mathlib.Tactic
import ControlStack.Scenarios.SC26Transaction
import ControlStack.Scenarios.SC26Refinement

namespace ControlStack.SC26Liveness

open ControlStack.SC26

/-! ## Monotonicity of the abstract model -/

/-- `t` extends `s`: tables only grow, spending never decreases, halting is sticky -/
structure Mono (s t : St) : Prop where
  reqs : s.reqs <+: t.reqs
  appr : s.approvals <+: t.approvals
  res : s.reserved <+: t.reserved
  spent : s.spent ≤ t.spent
  net : s.net <+: t.net
  bank : s.bank <+: t.bank
  halt : s.halted = true → t.halted = true

theorem Mono.refl (s : St) : Mono s s :=
  ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _, le_rfl, List.prefix_refl _, List.prefix_refl _, id⟩

theorem Mono.trans {s t u : St} (h1 : Mono s t) (h2 : Mono t u) : Mono s u :=
  ⟨h1.reqs.trans h2.reqs, h1.appr.trans h2.appr, h1.res.trans h2.res, h1.spent.trans h2.spent,
    h1.net.trans h2.net, h1.bank.trans h2.bank, fun h => h2.halt (h1.halt h)⟩

theorem bankAppend_mono (C : Checks) (s : St) (k : ℕ) (tx : Tx) : Mono s (bankAppend C s k tx) := by
  unfold bankAppend
  split_ifs
  · exact Mono.refl s
  · exact ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _, le_rfl, List.prefix_refl _,
      List.prefix_append _ _, id⟩

theorem step_mono (R : Roles) (cap : ℕ) (s : St) (o : Op) : Mono s (step R cap full s o) := by
  cases o with
  | arrive key =>
    simp only [step]
    split
    · exact Mono.refl s
    · exact bankAppend_mono _ _ _ _
  | bankCall c key tx =>
    simp only [step]
    split_ifs
    · exact Mono.refl s
    · exact bankAppend_mono _ _ _ _
  | halt c =>
    simp only [step]
    split_ifs
    · exact ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _, le_rfl, List.prefix_refl _,
        List.prefix_refl _, fun _ => rfl⟩
    · exact Mono.refl s
  | _ =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals first
      | exact Mono.refl s
      | exact ⟨List.prefix_append _ _, List.prefix_refl _, List.prefix_refl _, le_rfl, List.prefix_refl _,
          List.prefix_refl _, id⟩
      | exact ⟨List.prefix_refl _, List.prefix_append _ _, List.prefix_refl _, le_rfl, List.prefix_refl _,
          List.prefix_refl _, id⟩
      | exact ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_append _ _, Nat.le_add_right _ _,
          List.prefix_refl _, List.prefix_refl _, id⟩
      | exact ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _, le_rfl, List.prefix_append _ _,
          List.prefix_refl _, id⟩

theorem run_mono (R : Roles) (cap : ℕ) (s : St) (ops : List Op) : Mono s (run R cap full s ops) := by
  induction ops generalizing s with
  | nil => exact Mono.refl s
  | cons o ops ih => rw [run_cons]; exact (step_mono R cap s o).trans (ih _)

theorem Mono.reqOf {s t : St} (h : Mono s t) {k : ℕ} {r : Req} (hr : reqOf s k = some r) : reqOf t k = some r := by
  obtain ⟨l, hl⟩ := h.reqs
  simp only [ControlStack.SC26.reqOf] at hr ⊢
  rw [← hl, List.find?_append, hr]
  rfl

theorem not_halted_of {s t : St} (h : Mono s t) (ht : t.halted = false) : s.halted = false := by
  cases hs : s.halted
  · rfl
  · have := h.halt hs; rw [ht] at this; exact absurd this (by decide)

/-! ## The three honest steps -/

theorem execute_reserves (R : Roles) (cap : ℕ) (s : St) (c k : ℕ) (r : Req) (hh : s.halted = false)
    (hr : reqOf s k = some r) (happ : ∃ ap ∈ s.approvals, ap.1 = k)
    (hok : ¬ (k ∉ s.reserved ∧ cap < s.spent + r.tx.amount)) :
    k ∈ (step R cap full s (.execute c k)).reserved := by
  by_cases hk : k ∈ s.reserved
  · exact (step_mono R cap s _).res.subset hk
  · have hcap : s.spent + r.tx.amount ≤ cap := by
      by_contra hc; exact hok ⟨hk, by omega⟩
    simp only [step, hh, full, Bool.false_eq_true, false_and, ite_false, hr]
    rw [ite_eq_left ⟨happ, fun _ => hk, fun _ => hcap⟩]
    simp

theorem deliver_sends (R : Roles) (cap : ℕ) (s : St) (k : ℕ) (r : Req) (hh : s.halted = false)
    (hk : k ∈ s.reserved) (hr : reqOf s k = some r) : (k, r.tx) ∈ (step R cap full s (.deliver k)).net := by
  simp [step, hh, full, hk, hr]

theorem arrive_pays (R : Roles) (cap : ℕ) (s : St) (h : Inv R cap s) (k : ℕ) (r : Req) (tx : Tx)
    (hm : (k, tx) ∈ s.net) (hr : reqOf s k = some r) : (k, r.tx) ∈ (step R cap full s (.arrive k)).bank := by
  obtain ⟨m, hfind⟩ : ∃ m, s.net.find? (fun m => m.1 = k) = some m := by
    cases hf : s.net.find? (fun m => m.1 = k) with
    | some m => exact ⟨m, rfl⟩
    | none => rw [List.find?_eq_none] at hf; exact absurd (by simp) (hf _ hm)
  have hmem := List.mem_of_find?_eq_some hfind
  have hk : m.1 = k := by simpa using List.find?_some hfind
  obtain ⟨_, r', hr', htx⟩ := h.net_ok m hmem
  rw [hk, hr] at hr'
  cases hr'
  simp only [step, hfind]
  unfold bankAppend
  split_ifs with hb
  · obtain ⟨e, he, hek⟩ := List.mem_map.1 hb.2
    obtain ⟨_, r'', hr'', htx'⟩ := h.bank_ok e he
    rw [hek, hk, hr] at hr''
    cases hr''
    have : e = (k, r.tx) := Prod.ext (hek.trans hk) htx'.symm
    rw [← this]; exact he
  · simp only [List.mem_append, List.mem_singleton]
    right
    exact Prod.ext hk.symm htx

/-- **Honest progress.** From an invariant state that is not halted, a request with an independent exact approval,
unreserved and within the cap, is paid by the honest continuation [execute, deliver, arrive]. -/
theorem honest_progress (R : Roles) (cap : ℕ) (s : St) (h : Inv R cap s) (c k : ℕ) (r : Req)
    (hh : s.halted = false) (hr : reqOf s k = some r) (happ : Approved R s k r) (_hres : k ∉ s.reserved)
    (hcap : s.spent + r.tx.amount ≤ cap) :
    (k, r.tx) ∈ (run R cap full s [.execute c k, .deliver k, .arrive k]).bank := by
  obtain ⟨a, ha, _, _⟩ := happ
  set s1 := step R cap full s (.execute c k)
  have h1 : k ∈ s1.reserved :=
    execute_reserves R cap s c k r hh hr ⟨(k, a, r.tx), ha, rfl⟩ (fun hc => by omega)
  have hm1 := step_mono R cap s (.execute c k)
  have hh1 : s1.halted = false := by
    simp only [s1, step, hh, full, Bool.false_eq_true, false_and, ite_false, hr]; split_ifs <;> simp [hh]
  set s2 := step R cap full s1 (.deliver k)
  have h2 : (k, r.tx) ∈ s2.net := deliver_sends R cap s1 k r hh1 h1 (hm1.reqOf hr)
  have hi2 : Inv R cap s2 := step_inv R cap sound_full s1 _ trivial (step_inv R cap sound_full s _ trivial h)
  exact arrive_pays R cap s2 hi2 k r r.tx h2 ((hm1.trans (step_mono R cap s1 _)).reqOf hr)

/-- **Paid exactly once**: in any invariant state, a paid key occurs once in the bank. -/
theorem paid_once (R : Roles) (cap : ℕ) (s : St) (h : Inv R cap s) (k : ℕ) (tx : Tx) (hk : (k, tx) ∈ s.bank) :
    (s.bank.map Prod.fst).count k = 1 :=
  List.count_eq_one_of_mem h.bank_nodup (List.mem_map.2 ⟨(k, tx), hk, rfl⟩)

/-- **Progress under adversarial interleaving.** Arbitrary legal operations `a0, a1, a2, a3` are interleaved around the
honest [execute, deliver, arrive]. At the end, the gate is halted, or the payment is in the bank, or, at the moment
of the honest execute, `k` was unreserved and the cap was exhausted. A competing execution of `k` does not block
progress. -/
theorem progress_interleaved (R : Roles) (cap : ℕ) (s : St) (h : Inv R cap s) (c k : ℕ) (r : Req)
    (hr : reqOf s k = some r) (happ : Approved R s k r) (a0 a1 a2 a3 : List Op)
    (hleg : ∀ o ∈ a0 ++ a1 ++ a2 ++ a3, legal R o) :
    let t := run R cap full s (a0 ++ .execute c k :: a1 ++ .deliver k :: a2 ++ .arrive k :: a3)
    t.halted = true ∨ (k, r.tx) ∈ t.bank ∨
      (k ∉ (run R cap full s a0).reserved ∧ cap < (run R cap full s a0).spent + r.tx.amount) := by
  intro t
  have hl0 : ∀ o ∈ a0, legal R o := fun o ho => hleg o (by simp [ho])
  have hl1 : ∀ o ∈ a1, legal R o := fun o ho => hleg o (by simp [ho])
  have hl2 : ∀ o ∈ a2, legal R o := fun o ho => hleg o (by simp [ho])
  set s0 := run R cap full s a0
  set s1 := step R cap full s0 (.execute c k)
  set s1' := run R cap full s1 a1
  set s2 := step R cap full s1' (.deliver k)
  set s2' := run R cap full s2 a2
  set s3 := step R cap full s2' (.arrive k)
  have ht : t = run R cap full s3 a3 := by
    simp only [t, SC26Refinement.run_append, run_cons]
    rfl
  have m0 := run_mono R cap s a0
  have m1 := step_mono R cap s0 (.execute c k)
  have m1' := run_mono R cap s1 a1
  have m2 := step_mono R cap s1' (.deliver k)
  have m2' := run_mono R cap s2 a2
  have m3 := step_mono R cap s2' (.arrive k)
  have m3' := run_mono R cap s3 a3
  rw [ht]
  cases hT : (run R cap full s3 a3).halted
  · right
    have hh3 := not_halted_of m3' hT
    have hh2' := not_halted_of m3 hh3
    have hh2 := not_halted_of m2' hh2'
    have hh1' := not_halted_of m2 hh2
    have hh1 := not_halted_of m1' hh1'
    have hh0 := not_halted_of m1 hh1
    by_cases hblock : k ∉ s0.reserved ∧ cap < s0.spent + r.tx.amount
    · exact Or.inr hblock
    · left
      obtain ⟨a, ha, _, _⟩ := happ
      have hk1 : k ∈ s1.reserved := execute_reserves R cap s0 c k r hh0 (m0.reqOf hr)
        ⟨(k, a, r.tx), m0.appr.subset ha, rfl⟩ hblock
      have hk1' : k ∈ s1'.reserved := m1'.res.subset hk1
      have hn2 : (k, r.tx) ∈ s2.net :=
        deliver_sends R cap s1' k r hh1' hk1' ((m0.trans (m1.trans m1')).reqOf hr)
      have hn2' : (k, r.tx) ∈ s2'.net := m2'.net.subset hn2
      have hi : Inv R cap s2' := by
        have hi0 : Inv R cap s0 := run_inv R cap sound_full s a0 hl0 h
        have hi1 : Inv R cap s1 := step_inv R cap sound_full s0 _ trivial hi0
        have hi1' : Inv R cap s1' := run_inv R cap sound_full s1 a1 hl1 hi1
        have hi2 : Inv R cap s2 := step_inv R cap sound_full s1' _ trivial hi1'
        exact run_inv R cap sound_full s2 a2 hl2 hi2
      have hb3 := arrive_pays R cap s2' hi k r r.tx hn2'
        ((m0.trans (m1.trans (m1'.trans (m2.trans m2')))).reqOf hr)
      exact m3'.bank.subset hb3
  · left; rfl

/-! ## The availability prices of safety -/

/-- **Halted ⇒ no new payment.** Once halted, a key with nothing in the bank and nothing in flight is never paid. -/
theorem halted_blocks (R : Roles) (cap : ℕ) (s : St) (ops : List Op) (hops : ∀ o ∈ ops, legal R o)
    (hh : s.halted = true) (k : ℕ) (hb : k ∉ s.bank.map Prod.fst) (hn : k ∉ s.net.map Prod.fst) :
    k ∉ (run R cap full s ops).bank.map Prod.fst := by
  intro hk
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hk
  rcases (halt_freezes R cap s ops hops hh).2 e he with h | h
  · exact hb (List.mem_map.2 ⟨e, h, rfl⟩)
  · exact hn (List.mem_map.2 ⟨e, h, rfl⟩)

theorem unreserved_step (R : Roles) (cap : ℕ) (s : St) (o : Op) (k : ℕ) (r : Req) (hk : k ∉ s.reserved)
    (hr : reqOf s k = some r) (hc : cap < s.spent + r.tx.amount) : k ∉ (step R cap full s o).reserved := by
  cases o with
  | execute c id =>
    simp only [step]
    split_ifs
    · exact hk
    · split
      · exact hk
      · rename_i r' hr'
        split_ifs with h3
        · intro hm
          rcases List.mem_append.1 hm with hm | hm
          · exact hk hm
          · simp at hm; subst hm
            rw [hr] at hr'; cases hr'
            have := h3.2.2 rfl; omega
        · exact hk
  | arrive key =>
    simp only [step]
    split
    · exact hk
    · rw [bankAppend_reserved]; exact hk
  | bankCall c key tx =>
    simp only [step]
    split_ifs
    · exact hk
    · rw [bankAppend_reserved]; exact hk
  | _ =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals exact hk

/-- **Cap exhausted ⇒ no progress.** If the remaining cap is below an unreserved request's amount, it is never
reserved and never paid, whatever happens next (spending is never refunded). -/
theorem cap_exhausted_blocks (R : Roles) (cap : ℕ) (s : St) (h : Inv R cap s) (ops : List Op)
    (hops : ∀ o ∈ ops, legal R o) (k : ℕ) (r : Req) (hr : reqOf s k = some r) (hk : k ∉ s.reserved)
    (hc : cap < s.spent + r.tx.amount) :
    k ∉ (run R cap full s ops).reserved ∧ k ∉ (run R cap full s ops).bank.map Prod.fst := by
  have hres : k ∉ (run R cap full s ops).reserved := by
    induction ops generalizing s with
    | nil => exact hk
    | cons o ops ih =>
      rw [run_cons]
      have m := step_mono R cap s o
      exact ih _ (step_inv R cap sound_full s o (hops o List.mem_cons_self) h)
        (fun o' ho' => hops o' (List.mem_cons_of_mem o ho')) (m.reqOf hr) (unreserved_step R cap s o k r hk hr hc)
        (by have := m.spent; omega)
  refine ⟨hres, fun hb => ?_⟩
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hb
  exact hres ((run_inv R cap sound_full s ops hops h).bank_ok e he).1

/-! ## Crash-tolerant progress on the concrete machine -/

namespace Concrete

open ControlStack.SC26Refinement

theorem bankApply_keys (b : List (ℕ × Tx)) (k : ℕ) (tx : Tx) :
    (∀ x ∈ b.map Prod.fst, x ∈ (bankApply b k tx).map Prod.fst) ∧ k ∈ (bankApply b k tx).map Prod.fst := by
  unfold bankApply
  split_ifs with h
  · exact ⟨fun x hx => hx, h⟩
  · exact ⟨fun x hx => by simp only [List.map_append, List.mem_append]; exact Or.inl hx, by simp⟩

/-- concrete progress-relevant monotonicity: delivery rows persist (by id and payload), the wire and the bank's keys
only grow, halting is sticky -/
structure CMono (s t : CSt) : Prop where
  rows : ∀ d ∈ s.delivery, ∃ d' ∈ t.delivery, d'.id = d.id ∧ d'.tx = d.tx
  wire : s.wire <+: t.wire
  bank : ∀ x ∈ s.bank.map Prod.fst, x ∈ t.bank.map Prod.fst
  halt : s.halted = true → t.halted = true

theorem CMono.refl (s : CSt) : CMono s s :=
  ⟨fun d hd => ⟨d, hd, rfl, rfl⟩, List.prefix_refl _, fun _ h => h, id⟩

theorem CMono.trans {s t u : CSt} (h1 : CMono s t) (h2 : CMono t u) : CMono s u := by
  refine ⟨fun d hd => ?_, h1.wire.trans h2.wire, fun x hx => h2.bank x (h1.bank x hx), fun h => h2.halt (h1.halt h)⟩
  obtain ⟨d', hd', e1, e2⟩ := h1.rows d hd
  obtain ⟨d'', hd'', e3, e4⟩ := h2.rows d' hd'
  exact ⟨d'', hd'', e3.trans e1, e4.trans e2⟩

theorem set_persist (l : List DRow) (i : ℕ) (d : DRow) (hd : l[i]? = some d) :
    ∀ x ∈ l, ∃ y ∈ l.set i { d with acked := true }, y.id = x.id ∧ y.tx = x.tx := by
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  obtain ⟨hi, hdi⟩ := List.getElem?_eq_some_iff.1 hd
  by_cases hij : i = j
  · subst hij
    refine ⟨{ d with acked := true }, ?_, by simp [hdi], by simp [hdi]⟩
    exact List.mem_iff_getElem.2 ⟨i, by simpa using hi, by simp⟩
  · refine ⟨l[j], ?_, rfl, rfl⟩
    exact List.mem_iff_getElem.2 ⟨j, by simpa using hj, by rw [List.getElem_set_ne hij]⟩

theorem step_cmono (R : Roles) (cap : ℕ) (s : CSt) (o : COp) (ho : legalC R o) : CMono s (stepC R cap true s o) := by
  have hdel : ∀ (row : DRow), CMono s { s with delivery := s.delivery ++ [row] } := fun row =>
    ⟨fun d hd => ⟨d, List.mem_append_left _ hd, rfl, rfl⟩, List.prefix_refl _, fun _ h => h, id⟩
  cases o with
  | deliver id =>
    simp only [stepC]
    split_ifs
    · exact CMono.refl s
    · split
      · exact CMono.refl s
      · exact hdel _
    · exact CMono.refl s
  | transmit i =>
    simp only [stepC]
    split_ifs
    · exact CMono.refl s
    · split
      · exact CMono.refl s
      · split_ifs
        · exact CMono.refl s
        · exact ⟨fun d hd => ⟨d, hd, rfl, rfl⟩, List.prefix_append _ _, fun _ h => h, id⟩
  | bankProcess key =>
    simp only [stepC]
    split
    · exact CMono.refl s
    · exact ⟨fun d hd => ⟨d, hd, rfl, rfl⟩, List.prefix_refl _, fun x hx => (bankApply_keys _ _ _).1 x hx, id⟩
  | ack i =>
    simp only [stepC]
    split
    · exact CMono.refl s
    · rename_i d hd
      split_ifs
      · exact ⟨set_persist s.delivery i d hd, List.prefix_refl _, fun _ h => h, id⟩
      · exact CMono.refl s
  | crash => exact ⟨fun d hd => ⟨d, hd, rfl, rfl⟩, List.prefix_refl _, fun _ h => h, id⟩
  | recover =>
    simp only [stepC]
    split_ifs
    · exact CMono.refl s
    · exact ⟨fun d hd => ⟨d, hd, rfl, rfl⟩, List.prefix_append _ _, fun _ h => h, id⟩
  | halt c =>
    simp only [stepC]
    split_ifs
    · exact ⟨fun d hd => ⟨d, hd, rfl, rfl⟩, List.prefix_refl _, fun _ h => h, fun _ => rfl⟩
    · exact CMono.refl s
  | bankCall c key tx =>
    simp only [legalC] at ho
    simp only [stepC, ho, ite_true, ne_eq, not_false_eq_true]
    exact CMono.refl s
  | _ =>
    simp only [stepC]
    repeat' (first | split | split_ifs)
    all_goals first
      | exact CMono.refl s
      | exact ⟨fun d hd => ⟨d, hd, rfl, rfl⟩, List.prefix_refl _, fun _ h => h, id⟩

theorem run_cmono (R : Roles) (cap : ℕ) (s : CSt) (ops : List COp) (hops : ∀ o ∈ ops, legalC R o) :
    CMono s (runC R cap true s ops) := by
  induction ops generalizing s with
  | nil => exact CMono.refl s
  | cons o ops ih =>
    exact (step_cmono R cap s o (hops o List.mem_cons_self)).trans
      (ih _ (fun o' ho' => hops o' (List.mem_cons_of_mem o ho')))

/-- the ack invariant: an acknowledged row's key is in the bank -/
def AckInv (s : CSt) : Prop := ∀ d ∈ s.delivery, d.acked = true → d.id ∈ s.bank.map Prod.fst

theorem ackinv_same {s t : CSt} (h : AckInv s) (hd : t.delivery = s.delivery) (hb : t.bank = s.bank) : AckInv t := by
  intro d hdm hacked
  rw [hd] at hdm; rw [hb]; exact h d hdm hacked

theorem step_ackinv (R : Roles) (cap : ℕ) (s : CSt) (o : COp) (ho : legalC R o) (h : AckInv s) :
    AckInv (stepC R cap true s o) := by
  have m := step_cmono R cap s o ho
  cases o with
  | deliver id =>
    intro d hd hacked
    simp only [stepC] at hd ⊢
    split_ifs at hd ⊢
    · exact h d hd hacked
    · split at hd
      · exact h d hd hacked
      · rcases List.mem_append.1 hd with hd | hd
        · exact h d hd hacked
        · simp at hd; subst hd; simp at hacked
    · exact h d hd hacked
  | ack i =>
    intro d hd hacked
    simp only [stepC] at hd ⊢
    split at hd
    · exact h d hd hacked
    · rename_i d0 hd0
      split_ifs at hd ⊢ with hin
      · rcases List.mem_or_eq_of_mem_set hd with hd | rfl
        · exact h d hd hacked
        · exact hin
      · exact h d hd hacked
  | bankProcess key =>
    intro d hd hacked
    have hd' : d ∈ s.delivery := by
      simp only [stepC] at hd; split at hd <;> exact hd
    exact m.bank _ (h d hd' hacked)
  | bankCall c key tx =>
    simp only [legalC] at ho
    simp only [stepC, ho, ite_true, ne_eq, not_false_eq_true]
    exact h
  | request c tx => exact ackinv_same h (by simp only [stepC]; split_ifs <;> rfl) (by simp only [stepC]; split_ifs <;> rfl)
  | approve c id tx =>
    exact ackinv_same h (by simp only [stepC]; repeat' (first | split | split_ifs)
                            all_goals rfl)
      (by simp only [stepC]; repeat' (first | split | split_ifs)
          all_goals rfl)
  | execute c id =>
    exact ackinv_same h (by simp only [stepC]; repeat' (first | split | split_ifs)
                            all_goals rfl)
      (by simp only [stepC]; repeat' (first | split | split_ifs)
          all_goals rfl)
  | transmit i =>
    exact ackinv_same h (by simp only [stepC]; repeat' (first | split | split_ifs)
                            all_goals rfl)
      (by simp only [stepC]; repeat' (first | split | split_ifs)
          all_goals rfl)
  | crash => exact h
  | recover => exact ackinv_same h (by simp only [stepC]; split_ifs <;> rfl) (by simp only [stepC]; split_ifs <;> rfl)
  | halt c => exact ackinv_same h (by simp only [stepC]; split_ifs <;> rfl) (by simp only [stepC]; split_ifs <;> rfl)

theorem runC_append (R : Roles) (cap : ℕ) (s : CSt) (a b : List COp) :
    runC R cap true s (a ++ b) = runC R cap true (runC R cap true s a) b := by
  simp [runC, List.foldl_append]

theorem runC_cons (R : Roles) (cap : ℕ) (s : CSt) (o : COp) (ops : List COp) :
    runC R cap true s (o :: ops) = runC R cap true (stepC R cap true s o) ops := rfl

theorem run_ackinv (R : Roles) (cap : ℕ) (s : CSt) (ops : List COp) (hops : ∀ o ∈ ops, legalC R o) (h : AckInv s) :
    AckInv (runC R cap true s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih =>
    exact ih _ (fun o' ho' => hops o' (List.mem_cons_of_mem o ho')) (step_ackinv R cap s o (hops o List.mem_cons_self) h)

theorem ackinv_init : AckInv cinit := by simp [AckInv, cinit]

/-- **Crash-tolerant progress.** From a reachable concrete state with a logged delivery intent for key `k`, any legal
trace pre ++ [recover] ++ mid ++ [bankProcess k] ++ post, with any crashes anywhere and the gate not halted when
`recover` runs (the fairness premise: a recovery and a later bank processing of `k` happen), ends with `k` paid,
exactly once. -/
theorem crash_tolerant_progress (R : Roles) (cap : ℕ) (ops0 : List COp) (hops0 : ∀ o ∈ ops0, legalC R o)
    (k : ℕ) (d : DRow) (hd : d ∈ (runC R cap true cinit ops0).delivery) (hk : d.id = k)
    (pre mid post : List COp) (hleg : ∀ o ∈ pre ++ mid ++ post, legalC R o)
    (hh : (runC R cap true (runC R cap true cinit ops0) pre).halted = false) :
    k ∈ (runC R cap true (runC R cap true cinit ops0) (pre ++ .recover :: mid ++ .bankProcess k :: post)).bank.map
        Prod.fst ∧
      ((runC R cap true (runC R cap true cinit ops0) (pre ++ .recover :: mid ++ .bankProcess k :: post)).bank.map
        Prod.fst).count k = 1 := by
  set s := runC R cap true cinit ops0
  have hpre : ∀ o ∈ pre, legalC R o := fun o ho => hleg o (by simp [ho])
  have hmid : ∀ o ∈ mid, legalC R o := fun o ho => hleg o (by simp [ho])
  have hpost : ∀ o ∈ post, legalC R o := fun o ho => hleg o (by simp [ho])
  set s1 := runC R cap true s pre
  set s2 := stepC R cap true s1 .recover
  set s2' := runC R cap true s2 mid
  set s3 := stepC R cap true s2' (.bankProcess k)
  have hrun : runC R cap true s (pre ++ .recover :: mid ++ .bankProcess k :: post) = runC R cap true s3 post := by
    simp only [runC_append, runC_cons]; rfl
  rw [hrun]
  have m1 := run_cmono R cap s pre hpre
  have m2' := run_cmono R cap s2 mid hmid
  have m3 := run_cmono R cap s3 post hpost
  have hack : AckInv s1 := run_ackinv R cap s pre hpre (run_ackinv R cap cinit ops0 hops0 ackinv_init)
  obtain ⟨d1, hd1, hid1, _⟩ := m1.rows d hd
  have hpaid3 : k ∈ s3.bank.map Prod.fst := by
    cases hacked : d1.acked
    · -- unacknowledged: recover re-transmits it, bankProcess k applies some message with key k
      have hw2 : (d1.id, d1.tx) ∈ s2.wire := by
        simp only [s2, stepC, hh, Bool.false_eq_true, and_false, ite_false, List.mem_append]
        right
        simp only [unacked, List.mem_map, List.mem_filter]
        exact ⟨d1, ⟨hd1, by simp [hacked]⟩, rfl⟩
      have hk1 : d1.id = k := hid1.trans hk
      rw [hk1] at hw2
      have hw2' : (k, d1.tx) ∈ s2'.wire := m2'.wire.subset hw2
      obtain ⟨m, hm⟩ : ∃ m, s2'.wire.find? (fun m => m.1 = k) = some m := by
        cases hf : s2'.wire.find? (fun m => m.1 = k) with
        | some m => exact ⟨m, rfl⟩
        | none => rw [List.find?_eq_none] at hf; exact absurd (by simp) (hf _ hw2')
      have hmk : m.1 = k := by simpa using List.find?_some hm
      simp only [s3, stepC, hm]
      rw [← hmk]
      exact (bankApply_keys _ _ _).2
    · -- already acknowledged: its key is already in the bank
      have hb1 := hack d1 hd1 hacked
      rw [hid1, hk] at hb1
      have m12 : CMono s1 s2 := step_cmono R cap s1 .recover trivial
      have m33 : CMono s2' s3 := step_cmono R cap s2' (.bankProcess k) trivial
      exact m33.bank _ (m2'.bank _ (m12.bank _ hb1))
  have hpaid : k ∈ (runC R cap true s3 post).bank.map Prod.fst := m3.bank _ hpaid3
  refine ⟨hpaid, List.count_eq_one_of_mem ?_ hpaid⟩
  have hall : ∀ o ∈ ops0 ++ (pre ++ .recover :: mid ++ .bankProcess k :: post), legalC R o := by
    intro o ho
    cases o with
    | bankCall c key tx =>
      simp at ho
      rcases ho with h | h | h | h
      · exact hops0 _ h
      · exact hpre _ h
      · exact hmid _ h
      · exact hpost _ h
    | _ => trivial
  have hg := concrete_safe R cap _ hall
  rw [runC_append, hrun] at hg
  exact hg.2.1

/-- a gate (not halted) with one logged intent that is not on the wire -/
def loggedState : CSt := ⟨1, [⟨0, 1, wTx⟩], [(0, 2, wTx)], [0], 10, false, [⟨0, wTx, false⟩], none, [], []⟩

/-- **Liveness needs the fairness premise.** With crashes and bank processing but no recovery or transmission after
the last crash, the logged intent is never paid; adding one `recover` pays it. -/
theorem crashes_forever_no_progress :
    (runC R0 10 true loggedState [.crash, .bankProcess 0, .crash, .bankProcess 0, .crash]).bank = [] ∧
    (runC R0 10 true loggedState [.crash, .recover, .crash, .bankProcess 0]).bank = [(0, wTx)] := by
  decide

/-- **HALT stops concrete progress** (an availability price of safety): a halted gate's stranded intent is not
re-transmitted by recovery and is never paid. -/
theorem halted_concrete_no_progress :
    (runC R0 10 true strandedState [.recover, .bankProcess 0, .crash, .recover, .bankProcess 0]).bank = [] := by
  decide

end Concrete

end ControlStack.SC26Liveness

#print axioms ControlStack.SC26Liveness.honest_progress
#print axioms ControlStack.SC26Liveness.paid_once
#print axioms ControlStack.SC26Liveness.progress_interleaved
#print axioms ControlStack.SC26Liveness.halted_blocks
#print axioms ControlStack.SC26Liveness.cap_exhausted_blocks
#print axioms ControlStack.SC26Liveness.Concrete.crash_tolerant_progress
#print axioms ControlStack.SC26Liveness.Concrete.crashes_forever_no_progress
#print axioms ControlStack.SC26Liveness.Concrete.halted_concrete_no_progress
