/-
SC-28: several agents, each within its own limits, must not jointly exceed the global budget.

One JOINT shared-state transition system (pattern of `SC26Transaction.lean`) for families F3/F5/F8:
- a global cap `G` and per-lease budgets, charged in ONE shared durable ledger;
- workers hold leases (newest assignment wins); a `fork` gives the child its parent's lease account (descendant
  attribution), so a lineage shares one budget and one revocation;
- revocation is sticky per lease; an absorbing HALT issued by an admin freezes all work;
- cost is charged by a TRUSTED meter: the charge is the actual usage, at least one unit per work step, not a number the
  agent reports.

The external effect log `usage` records actual consumption (worker, lease, units). The gate's durable counters are the
`ledger`. The adversary chooses ANY finite sequence of operations (any callers, any actual usage, any reported cost,
forks, restarts) except a storage rollback, which is excluded by the anti-rollback premise (`legal`).

Main results:
- `sc28_safe`: from `init`, after any legal trace, total actual usage ≤ G, actual usage under each lease ≤ its budget,
  and the number of work steps ≤ G;
- `revoked_lease_stops`: once a lease is revoked, no trace (legal or not) adds usage under it;
- `fork_shares_lease`: an accepted fork puts the child on its parent's lease;
- `halt_freezes`: once halted, no trace changes the usage log;
- `sys`/`spec`: a client of the shared gate interface (`Core/Gate.lean`).

Necessity witnesses: `no_global_counter_breaks` (two agents within their own budgets exceed G),
`fresh_fork_exceeds_parent` and `fresh_fork_escapes_revocation` (fork without descendant attribution),
`reported_cost_breaks` (agent-reported zero cost: unbounded work), `rollback_double_spends` (the anti-rollback
premise cannot be dropped), `no_halt_check_breaks`. Non-vacuity: `honest_trace_works`.

Adversary class (ADVERSARY-CLASSES.md): TRACE_ARBITRARY over this transition system, minus storage rollback.
Premises outside the model: the meter is trusted and sees all consumption of every descendant (cgroup or gateway
accounting), the ledger store is not rolled back (an external monotonic anchor), admin credentials are not held by
agents. Not modelled: concurrency below the step granularity (each step is atomic), clocks/expiry, resource kinds.
No new mathematics: each theorem is an induction over the trace.
-/
import Mathlib.Tactic
import ControlStack.Core.Gate

namespace ControlStack.SC28

open ControlStack.Gate

structure St where
  /-- (lease id, budget) -/
  leases : List (ℕ × ℕ)
  /-- (worker, lease id), newest assignment first -/
  assign : List (ℕ × ℕ)
  revoked : List ℕ
  /-- the gate's durable counters: (lease id, charge) -/
  ledger : List (ℕ × ℕ)
  /-- the external effect log of actual consumption: (worker, lease id, units) -/
  usage : List (ℕ × ℕ × ℕ)
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | issue (caller lid budget : ℕ)
  | assignTo (caller worker lid : ℕ)
  /-- `parent` forks `child`; `newLid` is used only by the unsafe fresh-lease design -/
  | fork (caller parent child newLid : ℕ)
  | revoke (caller lid : ℕ)
  /-- worker `w` consumes `actual` units and reports `reported` -/
  | work (w actual reported : ℕ)
  /-- a crash/restart: volatile state is lost, durable counters are re-read (a no-op on the durable state) -/
  | restart
  /-- restore a stale snapshot of the counters (privileged storage rollback; excluded by `legal`) -/
  | rollback (n : ℕ)
  | halt (caller : ℕ)
deriving DecidableEq, Repr

/-- implementation checks; `full` is the deployed configuration -/
structure Checks where
  share : Bool
  meter : Bool
  global : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true⟩

def init : St := ⟨[], [], [], [], [], false⟩

def budgetOf (s : St) (lid : ℕ) : Option ℕ := (s.leases.find? (fun e => e.1 = lid)).map Prod.snd

def leaseOf (s : St) (w : ℕ) : Option ℕ := (s.assign.find? (fun e => e.1 = w)).map Prod.snd

def spentL (s : St) (lid : ℕ) : ℕ := ((s.ledger.filter (fun e => e.1 = lid)).map Prod.snd).sum
def spentT (s : St) : ℕ := (s.ledger.map Prod.snd).sum
def usedL (s : St) (lid : ℕ) : ℕ := ((s.usage.filter (fun e => e.2.1 = lid)).map (fun e => e.2.2)).sum
def usedT (s : St) : ℕ := (s.usage.map (fun e => e.2.2)).sum

/-- the charge for one work step -/
def charge (C : Checks) (actual reported : ℕ) : ℕ := if C.meter then max actual 1 else reported

/-- the (leases, assignments) after `p` forks `ch`: with `share`, the child joins its parent's lease; without it, the
child gets a FRESH lease `nl` with a copy of the parent's budget (the unsafe design) -/
def forkUpd (C : Checks) (s : St) (p ch nl : ℕ) : List (ℕ × ℕ) × List (ℕ × ℕ) :=
  match leaseOf s p with
  | none => (s.leases, s.assign)
  | some lid =>
    if ch ∈ s.assign.map Prod.fst then (s.leases, s.assign)
    else if C.share then (s.leases, (ch, lid) :: s.assign)
    else if budgetOf s nl = none then (s.leases ++ [(nl, (budgetOf s lid).getD 0)], (ch, nl) :: s.assign)
    else (s.leases, s.assign)

theorem forkUpd_full_leases (s : St) (p ch nl : ℕ) : (forkUpd full s p ch nl).1 = s.leases := by
  unfold forkUpd
  split
  · rfl
  · split_ifs <;> simp_all [full]

def step (admins : List ℕ) (G : ℕ) (C : Checks) (s : St) : Op → St
  | .issue c lid b =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ admins ∧ budgetOf s lid = none then { s with leases := s.leases ++ [(lid, b)] } else s
  | .assignTo c w lid =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ admins ∧ budgetOf s lid ≠ none then { s with assign := (w, lid) :: s.assign } else s
  | .fork _ p ch nl =>
    if s.halted ∧ C.haltCheck then s
    else { s with leases := (forkUpd C s p ch nl).1, assign := (forkUpd C s p ch nl).2 }
  | .revoke c lid => if c ∈ admins then { s with revoked := s.revoked ++ [lid] } else s
  | .work w a r =>
    if s.halted ∧ C.haltCheck then s
    else match leaseOf s w with
      | none => s
      | some lid =>
        match budgetOf s lid with
        | none => s
        | some b =>
          if lid ∉ s.revoked ∧ spentL s lid + charge C a r ≤ b ∧ (C.global → spentT s + charge C a r ≤ G) then
            { s with ledger := s.ledger ++ [(lid, charge C a r)], usage := s.usage ++ [(w, lid, a)] }
          else s
  | .restart => s
  | .rollback n => { s with ledger := s.ledger.take n }
  | .halt c => if c ∈ admins then { s with halted := true } else s

def run (admins : List ℕ) (G : ℕ) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step admins G C) s

theorem run_cons (admins : List ℕ) (G : ℕ) (C : Checks) (s : St) (o : Op) (ops : List Op) :
    run admins G C s (o :: ops) = run admins G C (step admins G C s o) ops := rfl

/-- anti-rollback premise: no storage rollback of the counters -/
def legal : Op → Prop
  | .rollback _ => False
  | _ => True

/-! ## Invariant and safety -/

structure Inv (G : ℕ) (s : St) : Prop where
  tot : usedT s ≤ spentT s
  cap : spentT s ≤ G
  per : ∀ lid, usedL s lid ≤ spentL s lid
  budget : ∀ lid, spentL s lid ≤ (budgetOf s lid).getD 0
  count : s.usage.length ≤ spentT s

/-- the safety property: total actual usage within G, per-lease usage within its budget, at most G work steps -/
def Good (G : ℕ) (s : St) : Prop :=
  usedT s ≤ G ∧ (∀ lid, usedL s lid ≤ (budgetOf s lid).getD 0) ∧ s.usage.length ≤ G

theorem Inv.good {G : ℕ} {s : St} (h : Inv G s) : Good G s :=
  ⟨h.tot.trans h.cap, fun lid => (h.per lid).trans (h.budget lid), h.count.trans h.cap⟩

theorem inv_init (G : ℕ) : Inv G init :=
  ⟨by simp [init, usedT, spentT], by simp [init, spentT], fun _ => by simp [init, usedL, spentL],
    fun _ => by simp [init, spentL], by simp [init, spentT]⟩

theorem budgetOf_append (s : St) (lid b : ℕ) (hfresh : budgetOf s lid = none) (l : ℕ) :
    budgetOf { s with leases := s.leases ++ [(lid, b)] } l = if l = lid then some b else budgetOf s l := by
  simp only [budgetOf] at hfresh ⊢
  rw [List.find?_append]
  by_cases hl : l = lid
  · subst hl
    simp only [Option.map_eq_none_iff] at hfresh
    simp [hfresh]
  · cases hf : s.leases.find? (fun e => e.1 = l) <;> simp [hl, Ne.symm hl]

/-- steps that leave the ledger and usage unchanged and do not shrink any budget keep the invariant -/
theorem inv_of_same {G : ℕ} {s t : St} (h : Inv G s) (hl : t.ledger = s.ledger) (hu : t.usage = s.usage)
    (hb : ∀ lid, (budgetOf s lid).getD 0 ≤ (budgetOf t lid).getD 0 ∨ spentL s lid = 0) : Inv G t := by
  have e1 : spentT t = spentT s := by simp [spentT, hl]
  have e2 : usedT t = usedT s := by simp [usedT, hu]
  have e3 : ∀ lid, spentL t lid = spentL s lid := fun lid => by simp [spentL, hl]
  have e4 : ∀ lid, usedL t lid = usedL s lid := fun lid => by simp [usedL, hu]
  refine ⟨by rw [e1, e2]; exact h.tot, by rw [e1]; exact h.cap, fun lid => by rw [e3, e4]; exact h.per lid,
    fun lid => ?_, by rw [hu, e1]; exact h.count⟩
  rw [e3]
  rcases hb lid with hb | hb
  · exact (h.budget lid).trans hb
  · rw [hb]; exact Nat.zero_le _

theorem work_inv {G : ℕ} {s : St} (h : Inv G s) (w lid a b ch : ℕ) (hch : a ≤ ch) (h1 : 1 ≤ ch)
    (hb : budgetOf s lid = some b) (hcl : spentL s lid + ch ≤ b) (hcg : spentT s + ch ≤ G) :
    Inv G { s with ledger := s.ledger ++ [(lid, ch)], usage := s.usage ++ [(w, lid, a)] } := by
  have ht := h.tot
  have hc := h.count
  have hcap := h.cap
  simp only [usedT, spentT] at ht hc hcap hcg
  refine ⟨?_, ?_, fun l => ?_, fun l => ?_, ?_⟩
  · simp only [usedT, spentT, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero]
    omega
  · simp only [spentT, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      add_zero]
    omega
  · have hp := h.per l
    simp only [usedL, spentL] at hp ⊢
    by_cases hl : lid = l
    · subst hl; simp; omega
    · simp [hl]; omega
  · show spentL _ l ≤ (budgetOf s l).getD 0
    have hp := h.budget l
    by_cases hl : lid = l
    · subst hl
      rw [hb] at hp ⊢
      simp only [spentL] at hp hcl ⊢
      simp
      simpa using hcl
    · simp only [spentL] at hp ⊢
      simp [hl]
      exact hp
  · simp only [spentT, List.length_append, List.length_singleton, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    omega

theorem step_inv (admins : List ℕ) (G : ℕ) (s : St) (o : Op) (ho : legal o) (h : Inv G s) :
    Inv G (step admins G full s o) := by
  cases o with
  | issue c lid b =>
    simp only [step]
    split_ifs with h1 h2
    · exact h
    · refine inv_of_same h rfl rfl (fun l => ?_)
      rw [budgetOf_append s lid b h2.2]
      by_cases hl : l = lid
      · subst hl; right
        have := h.budget l
        rw [h2.2] at this
        simpa using this
      · left; simp [hl]
    · exact h
  | assignTo c w lid =>
    simp only [step]
    split_ifs
    · exact h
    · exact inv_of_same h rfl rfl (fun _ => Or.inl le_rfl)
    · exact h
  | fork c p ch nl =>
    simp only [step]
    split_ifs
    · exact h
    · refine inv_of_same h rfl rfl (fun l => Or.inl (le_of_eq ?_))
      simp only [budgetOf, forkUpd_full_leases]
  | revoke c lid =>
    simp only [step]
    split_ifs
    · exact inv_of_same h rfl rfl (fun _ => Or.inl le_rfl)
    · exact h
  | work w a r =>
    simp only [step]
    by_cases hh : s.halted = true
    · simp only [hh, show full.haltCheck = true from rfl, and_self, ite_true]; exact h
    · rw [ite_eq_right_iff.2 (fun hc => absurd hc.1 hh)]
      cases hl : leaseOf s w with
      | none => exact h
      | some lid =>
        dsimp only
        cases hb : budgetOf s lid with
        | none => exact h
        | some b =>
          dsimp only
          split_ifs with hc
          · obtain ⟨_, hcl, hcg⟩ := hc
            exact work_inv h w lid a b _ (le_max_left _ _) (le_max_right _ _) hb hcl (hcg rfl)
          · exact h
  | restart => exact h
  | rollback n => exact absurd ho (by simp [legal])
  | halt c =>
    simp only [step]
    split_ifs
    · exact inv_of_same h rfl rfl (fun _ => Or.inl le_rfl)
    · exact h

theorem run_inv (admins : List ℕ) (G : ℕ) (s : St) (ops : List Op) (hops : ∀ o ∈ ops, legal o) (h : Inv G s) :
    Inv G (run admins G full s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih =>
    rw [run_cons]
    exact ih _ (fun o' ho' => hops o' (List.mem_cons_of_mem o ho')) (step_inv admins G s o (hops o List.mem_cons_self) h)

/-- **SC-28 safety.** After any legal trace from `init` (any agents, forks, restarts, actual usages and reported
costs; no storage rollback), total actual usage ≤ G, usage under each lease ≤ its budget, and at most G work steps
happened. Adversary: TRACE_ARBITRARY minus rollback. -/
theorem sc28_safe (admins : List ℕ) (G : ℕ) (ops : List Op) (hops : ∀ o ∈ ops, legal o) :
    Good G (run admins G full init ops) :=
  (run_inv admins G init ops hops (inv_init G)).good

/-! ## Revocation, lineage, halt -/

theorem step_revoked (admins : List ℕ) (G : ℕ) (C : Checks) (s : St) (o : Op) (lid : ℕ) (hr : lid ∈ s.revoked) :
    lid ∈ (step admins G C s o).revoked ∧ usedL (step admins G C s o) lid = usedL s lid := by
  cases o with
  | work w a r =>
    simp only [step]
    split_ifs
    · exact ⟨hr, rfl⟩
    · split
      · exact ⟨hr, rfl⟩
      · rename_i l _
        split
        · exact ⟨hr, rfl⟩
        · split_ifs with hc
          · refine ⟨hr, ?_⟩
            have hne : l ≠ lid := fun he => hc.1 (he ▸ hr)
            simp [usedL, List.filter_append, hne]
          · exact ⟨hr, rfl⟩
  | revoke c l => simp only [step]; split_ifs <;> simp [hr, usedL]
  | issue c l b => simp only [step]; split_ifs <;> exact ⟨hr, rfl⟩
  | assignTo c w l => simp only [step]; split_ifs <;> exact ⟨hr, rfl⟩
  | fork c p ch nl => simp only [step]; split_ifs <;> exact ⟨hr, rfl⟩
  | restart => exact ⟨hr, rfl⟩
  | rollback n => exact ⟨hr, rfl⟩
  | halt c => simp only [step]; split_ifs <;> exact ⟨hr, rfl⟩

/-- **Revocation is sticky**: after a lease is revoked, no trace (in any configuration) adds usage under it. -/
theorem revoked_lease_stops (admins : List ℕ) (G : ℕ) (C : Checks) (s : St) (ops : List Op) (lid : ℕ)
    (hr : lid ∈ s.revoked) : usedL (run admins G C s ops) lid = usedL s lid := by
  induction ops generalizing s with
  | nil => rfl
  | cons o ops ih =>
    rw [run_cons]
    obtain ⟨h1, h2⟩ := step_revoked admins G C s o lid hr
    rw [ih _ h1, h2]

/-- **Descendant attribution**: an accepted fork puts the child on its parent's lease, so the lineage shares one
budget and one revocation. -/
theorem fork_shares_lease (admins : List ℕ) (G : ℕ) (s : St) (c p ch nl lid : ℕ) (hh : s.halted = false)
    (hp : leaseOf s p = some lid) (hfresh : ch ∉ s.assign.map Prod.fst) :
    leaseOf (step admins G full s (.fork c p ch nl)) ch = some lid := by
  have hf : forkUpd full s p ch nl = (s.leases, (ch, lid) :: s.assign) := by
    simp [forkUpd, hp, hfresh, full]
  simp only [step, hh, Bool.false_eq_true, false_and, ite_false]
  rw [hf]
  simp [leaseOf]

theorem step_halted (admins : List ℕ) (G : ℕ) (s : St) (o : Op) (hh : s.halted = true) :
    (step admins G full s o).usage = s.usage ∧ (step admins G full s o).halted = true := by
  cases o with
  | revoke c l => simp only [step]; split_ifs <;> simp [hh]
  | halt c => simp only [step]; split_ifs <;> simp [hh]
  | rollback n => simp [step, hh]
  | restart => simp [step, hh]
  | _ => simp [step, full, hh]

/-- **Halt freezes work**: once halted, no trace changes the usage log. -/
theorem halt_freezes (admins : List ℕ) (G : ℕ) (s : St) (ops : List Op) (hh : s.halted = true) :
    (run admins G full s ops).usage = s.usage := by
  induction ops generalizing s with
  | nil => rfl
  | cons o ops ih =>
    rw [run_cons]
    obtain ⟨h1, h2⟩ := step_halted admins G s o hh
    rw [ih _ h2, h1]

/-! ## Client of the shared gate interface -/

theorem usage_prefix (admins : List ℕ) (G : ℕ) (C : Checks) (s : St) (o : Op) :
    s.usage <+: (step admins G C s o).usage := by
  cases o with
  | work w a r =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals first | exact List.prefix_refl _ | exact List.prefix_append _ _
  | restart => exact List.prefix_refl _
  | rollback n => exact List.prefix_refl _
  | _ => simp only [step]; split_ifs <;> exact List.prefix_refl _

/-- one usage entry is within its lease's budget -/
def EntryOk (s : St) (e : ℕ × ℕ × ℕ) : Prop := e.2.2 ≤ (budgetOf s e.2.1).getD 0

theorem Good.entry {G : ℕ} {s : St} (h : Good G s) (e : ℕ × ℕ × ℕ) (he : e ∈ s.usage) : EntryOk s e := by
  refine le_trans ?_ (h.2.1 e.2.1)
  apply List.le_sum_of_mem
  exact List.mem_map.2 ⟨e, List.mem_filter.2 ⟨he, by simp⟩, rfl⟩

def sys (admins : List ℕ) (G : ℕ) : System St {o : Op // legal o} (ℕ × ℕ × ℕ) where
  step := fun s o => step admins G full s o.1
  effects := St.usage

def spec (admins : List ℕ) (G : ℕ) : Spec (sys admins G) where
  Inv := Inv G
  ok := EntryOk
  step_inv := fun s o h => step_inv admins G s o.1 o.2 h
  log_prefix := fun s o => usage_prefix admins G full s o.1
  inv_ok := fun _ h e he => h.good.entry e he

/-! ## Non-vacuity and necessity witnesses

Admin 9; workers 1, 2. -/

/-- **Non-vacuity**: honest work within budget happens. -/
theorem honest_trace_works :
    (run [9] 10 full init [.issue 9 0 10, .assignTo 9 1 0, .work 1 3 3, .restart, .work 1 4 4]).usage =
      [(1, 0, 3), (1, 0, 4)] := by
  decide

/-- per-lease budgets without the global counter: two agents, each within its own budget, exceed G = 10 -/
theorem no_global_counter_breaks :
    usedT (run [9] 10 { full with global := false } init
      [.issue 9 0 10, .issue 9 1 10, .assignTo 9 1 0, .assignTo 9 2 1, .work 1 10 0, .work 2 10 0]) = 20 ∧
    usedT (run [9] 10 full init
      [.issue 9 0 10, .issue 9 1 10, .assignTo 9 1 0, .assignTo 9 2 1, .work 1 10 0, .work 2 10 0]) = 10 := by
  decide

/-- a fork that gets a FRESH lease (no descendant attribution): the lineage of a 10-unit lease consumes 20 -/
theorem fresh_fork_exceeds_parent :
    (run [9] 100 { full with share := false } init
      [.issue 9 0 10, .assignTo 9 1 0, .fork 1 1 2 5, .work 1 10 0, .work 2 10 0]).usage =
      [(1, 0, 10), (2, 5, 10)] ∧
    (run [9] 100 full init
      [.issue 9 0 10, .assignTo 9 1 0, .fork 1 1 2 5, .work 1 10 0, .work 2 10 0]).usage = [(1, 0, 10)] := by
  decide

/-- a fork with a fresh lease escapes the revocation of its parent's lease; with descendant attribution it does not -/
theorem fresh_fork_escapes_revocation :
    (run [9] 100 { full with share := false } init
      [.issue 9 0 10, .assignTo 9 1 0, .fork 1 1 2 5, .revoke 9 0, .work 2 5 0]).usage = [(2, 5, 5)] ∧
    (run [9] 100 full init
      [.issue 9 0 10, .assignTo 9 1 0, .fork 1 1 2 5, .revoke 9 0, .work 2 5 0]).usage = [] := by
  decide

/-- agent-reported cost: reporting 0 for 5 units of real work, three times, under G = budget = 1 -/
theorem reported_cost_breaks :
    let s := run [9] 1 { full with meter := false } init
      [.issue 9 0 1, .assignTo 9 1 0, .work 1 5 0, .work 1 5 0, .work 1 5 0]
    usedT s = 15 ∧ s.usage.length = 3 := by
  decide

/-- a storage rollback of the counters double-spends: the anti-rollback premise (`legal`) cannot be dropped -/
theorem rollback_double_spends :
    usedT (run [9] 10 full init [.issue 9 0 10, .assignTo 9 1 0, .work 1 10 0, .rollback 0, .work 1 10 0]) = 20 := by
  decide

/-- without the halt check, work continues after the halt -/
theorem no_halt_check_breaks :
    (run [9] 10 { full with haltCheck := false } init [.issue 9 0 10, .assignTo 9 1 0, .halt 9, .work 1 3 3]).usage =
      [(1, 0, 3)] ∧
    (run [9] 10 full init [.issue 9 0 10, .assignTo 9 1 0, .halt 9, .work 1 3 3]).usage = [] := by
  decide

end ControlStack.SC28

#print axioms ControlStack.SC28.sc28_safe
#print axioms ControlStack.SC28.revoked_lease_stops
#print axioms ControlStack.SC28.fork_shares_lease
#print axioms ControlStack.SC28.halt_freezes
#print axioms ControlStack.SC28.spec
#print axioms ControlStack.SC28.honest_trace_works
#print axioms ControlStack.SC28.no_global_counter_breaks
#print axioms ControlStack.SC28.fresh_fork_exceeds_parent
#print axioms ControlStack.SC28.fresh_fork_escapes_revocation
#print axioms ControlStack.SC28.reported_cost_breaks
#print axioms ControlStack.SC28.rollback_double_spends
#print axioms ControlStack.SC28.no_halt_check_breaks
