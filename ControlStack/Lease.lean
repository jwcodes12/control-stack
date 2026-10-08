/-
F5 quotas, leases and revocation as a gate client (SC-14 runaway resources; SC-28 agents that individually satisfy
limits but jointly exceed them).

A trusted controller issues leases (id, budget, expiry) to workers and can revoke a lease. Workers (agents) may fork
helpers: a fork inherits its parent's LEASE, not a fresh budget. A unit of work names a worker and a cost. The gate
admits it only if:
- the worker holds a lease that is not revoked and not expired;
- the lease's total spend stays within its budget;
- the global spend stays within a cap.

Proved (`lease_safe`, from the initial state, for any interleaving):
1. every work effect ran under an issued lease, no later than that lease's expiry;
2. every lease's total spend is ≤ its budget, however many workers were forked onto it;
3. total spend over all workers is ≤ the global cap.

`revoke_absorbing`: after a lease is revoked, no later operation appends work under it. `fork_without_lease_accounting`
(necessity): if budgets are charged per WORKER, one fork doubles the work done under one lease.

Also proved:
- `work_count_le`: every admitted unit costs at least 1, so the NUMBER of work units per lease is ≤ its budget, and
  ≤ cap overall.
- `agent_cannot_issue`: agent operations (fork, work, restart) never change the lease table or the revocation list.
- `revoked_worker_stays_stopped`: forks may only create FRESH workers, so a revoked worker cannot be re-pointed onto
  another lease.

Premises (not modelled):
- every resource use goes through the gate;
- the counters live in the trusted controller and survive restarts. Restart is a no-op on this state, so durability
  holds by definition, the same pattern as EgressGate's policy integrity (`LifetimeLedger.restore_breaks` shows
  rollback matters);
- worker identities cannot be forged;
- the cost of a unit is metered by the gate. The agent's declared cost could under-report, but `work_count_le`
  bounds the number of units regardless.

Revocation stops a lease, not a worker identity: re-issuing a lease to the same worker is a trusted controller
decision. Adversarial review 2026-10-08: D1, D2 fixed; reviews/adversarial-2026-10-08/.
-/
import ControlStack.Gate

namespace ControlStack.Lease

open ControlStack.Gate

structure LeaseRec where
  id : ℕ
  budget : ℕ
  expiry : ℕ
  deriving DecidableEq

structure St where
  now : ℕ
  leases : List LeaseRec
  revoked : List ℕ
  holder : List (ℕ × ℕ)          -- (worker, lease id), newest first: the newest assignment wins
  work : List (ℕ × ℕ × ℕ)        -- effect log: (lease id, cost, time)

inductive Op where
  | tick                         -- trusted clock
  | issue (l : LeaseRec) (w : ℕ)    -- trusted controller
  | revoke (id : ℕ)              -- trusted controller
  | fork (w w' : ℕ)              -- agent: a FRESH worker w' inherits w's lease
  | restart                      -- infrastructure: counters are durable
  | work (w cost : ℕ)            -- agent: request a unit of work

/-- total spend under lease id -/
def spent (work : List (ℕ × ℕ × ℕ)) (id : ℕ) : ℕ := ((work.filter (fun e => e.1 = id)).map (fun e => e.2.1)).sum

/-- total spend -/
def total (work : List (ℕ × ℕ × ℕ)) : ℕ := (work.map (fun e => e.2.1)).sum

def leaseOf (s : St) (w : ℕ) : Option ℕ := (s.holder.find? (fun p => p.1 = w)).map Prod.snd

def step (cap : ℕ) (s : St) : Op → St
  | .tick => { s with now := s.now + 1 }
  | .issue l w =>
    if l.id ∈ s.leases.map LeaseRec.id then s
    else { s with leases := s.leases ++ [l], holder := (w, l.id) :: s.holder }
  | .revoke id => { s with revoked := s.revoked ++ [id] }
  | .fork w w' =>
    match leaseOf s w with
    | some id => if w' ∈ s.holder.map Prod.fst then s else { s with holder := (w', id) :: s.holder }
    | none => s
  | .restart => s
  | .work w c =>
    match leaseOf s w with
    | none => s
    | some id =>
      match s.leases.find? (fun l => l.id = id) with
      | none => s
      | some l =>
        if id ∉ s.revoked ∧ s.now ≤ l.expiry ∧ spent s.work id + c ≤ l.budget ∧ total s.work + c ≤ cap ∧ 1 ≤ c then
          { s with work := s.work ++ [(id, c, s.now)] }
        else s

def sys (cap : ℕ) : System St Op (ℕ × ℕ × ℕ) where
  step := step cap
  effects := fun s => s.work

def Inv (cap : ℕ) (s : St) : Prop :=
  (s.leases.map LeaseRec.id).Nodup ∧
  (∀ e ∈ s.work, ∃ l ∈ s.leases, l.id = e.1 ∧ e.2.2 ≤ l.expiry) ∧
  (∀ l ∈ s.leases, spent s.work l.id ≤ l.budget) ∧
  total s.work ≤ cap ∧
  ∀ e ∈ s.work, 1 ≤ e.2.1

theorem spent_append (work : List (ℕ × ℕ × ℕ)) (e : ℕ × ℕ × ℕ) (id : ℕ) :
    spent (work ++ [e]) id = spent work id + (if e.1 = id then e.2.1 else 0) := by
  unfold spent; split_ifs with h <;> simp [List.filter_append, h]

theorem total_append (work : List (ℕ × ℕ × ℕ)) (e : ℕ × ℕ × ℕ) : total (work ++ [e]) = total work + e.2.1 := by
  simp [total]

theorem spent_eq_zero_of_absent (work : List (ℕ × ℕ × ℕ)) (id : ℕ) (h : ∀ e ∈ work, e.1 ≠ id) :
    spent work id = 0 := by
  unfold spent
  rw [List.filter_eq_nil_iff.2 (fun e he => by simpa using h e he)]
  rfl

theorem step_inv (cap : ℕ) (s : St) (o : Op) (h : Inv cap s) : Inv cap (step cap s o) := by
  obtain ⟨hn, hw, hb, ht, hp⟩ := h
  cases o with
  | tick => exact ⟨hn, hw, hb, ht, hp⟩
  | revoke id => exact ⟨hn, hw, hb, ht, hp⟩
  | restart => exact ⟨hn, hw, hb, ht, hp⟩
  | fork w w' =>
    simp only [step]; split <;> (try split_ifs) <;> exact ⟨hn, hw, hb, ht, hp⟩
  | issue l w =>
    simp only [step]
    split_ifs with hfresh
    · exact ⟨hn, hw, hb, ht, hp⟩
    · refine ⟨?_, ?_, ?_, ht, hp⟩
      · rw [List.map_append, List.nodup_append]
        refine ⟨hn, List.nodup_singleton _, ?_⟩
        intro a ha b hb'; simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb'
        subst hb'; intro hab; subst hab; exact hfresh ha
      · intro e he
        obtain ⟨l', hl', h1, h2⟩ := hw e he
        exact ⟨l', List.mem_append_left _ hl', h1, h2⟩
      · intro l' hl'
        rcases List.mem_append.1 hl' with hl' | hl'
        · exact hb l' hl'
        · simp only [List.mem_singleton] at hl'; subst hl'
          rw [spent_eq_zero_of_absent]
          · exact Nat.zero_le _
          · intro e he heq
            obtain ⟨l'', hl'', h1, -⟩ := hw e he
            exact hfresh (List.mem_map.2 ⟨l'', hl'', h1.trans heq⟩)
  | work w c =>
    simp only [step]
    split
    · exact ⟨hn, hw, hb, ht, hp⟩
    · rename_i id _
      split
      · exact ⟨hn, hw, hb, ht, hp⟩
      · rename_i l0 hf
        have hl0 : l0 ∈ s.leases := List.mem_of_find?_eq_some hf
        have hid : l0.id = id := by simpa using List.find?_some hf
        split_ifs with hc
        · refine ⟨hn, ?_, ?_, ?_, ?_⟩
          · intro e he
            rcases List.mem_append.1 he with he | he
            · exact hw e he
            · simp only [List.mem_singleton] at he; subst he
              exact ⟨l0, hl0, hid, hc.2.1⟩
          · intro l hl
            rw [spent_append]
            split_ifs with hli
            · have : l = l0 := List.inj_on_of_nodup_map hn hl hl0 (by simp at hli; rw [hid]; exact hli.symm)
              subst this
              rw [hid]; exact hc.2.2.1
            · simpa using hb l hl
          · rw [total_append]; exact hc.2.2.2.1
          · intro e he
            rcases List.mem_append.1 he with he | he
            · exact hp e he
            · simp only [List.mem_singleton] at he; subst he; exact hc.2.2.2.2
        · exact ⟨hn, hw, hb, ht, hp⟩

theorem prefix_step (cap : ℕ) (s : St) (o : Op) : s.work <+: (step cap s o).work := by
  cases o with
  | issue l w => simp only [step]; split_ifs <;> simp
  | fork w w' => simp only [step]; split <;> (try split_ifs) <;> simp
  | work w c =>
    simp only [step]; split
    · exact List.prefix_refl _
    · split
      · exact List.prefix_refl _
      · split_ifs <;> simp [List.prefix_append]
  | _ => simp [step]

def spec (cap : ℕ) : Spec (sys cap) where
  Inv := Inv cap
  ok := fun s e => ∃ l ∈ s.leases, l.id = e.1 ∧ e.2.2 ≤ l.expiry
  step_inv := step_inv cap
  log_prefix := prefix_step cap
  inv_ok := fun _ h e he => h.2.1 e he

def init : St := ⟨0, [], [], [], []⟩

/-- **Lease safety.** After any interleaving of controller, clock, fork, restart and work operations: every work unit
ran under an issued lease before its expiry; each lease's spend, summed over all workers forked onto it, is within
its budget; and the global spend is within the cap. -/
theorem lease_safe (cap : ℕ) (ops : List Op) :
    let s := (sys cap).run init ops
    (∀ e ∈ s.work, ∃ l ∈ s.leases, l.id = e.1 ∧ e.2.2 ≤ l.expiry) ∧
    (∀ l ∈ s.leases, spent s.work l.id ≤ l.budget) ∧ total s.work ≤ cap := by
  have h := ((spec cap).trace_safe init ops ⟨List.nodup_nil, by simp [init], by simp [init],
    by simp [init, total], by simp [init]⟩).1
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- **Revocation is absorbing.** Once lease id is revoked, no operation appends work under it, and it stays revoked. -/
theorem revoke_step (cap : ℕ) (s : St) (o : Op) (id : ℕ) (hr : id ∈ s.revoked) :
    id ∈ (step cap s o).revoked ∧ ∃ δ, (step cap s o).work = s.work ++ δ ∧ ∀ e ∈ δ, e.1 ≠ id := by
  cases o with
  | tick => exact ⟨hr, [], by simp [step], by simp⟩
  | revoke id' => exact ⟨List.mem_append_left _ hr, [], by simp [step], by simp⟩
  | restart => exact ⟨hr, [], by simp [step], by simp⟩
  | issue l w =>
    refine ⟨?_, [], ?_, by simp⟩ <;> simp only [step] <;> split_ifs <;> simp [hr]
  | fork w w' =>
    refine ⟨?_, [], ?_, by simp⟩ <;> simp only [step] <;> split <;> (try split_ifs) <;> simp [hr]
  | work w c =>
    simp only [step]
    split
    · exact ⟨hr, [], by simp, by simp⟩
    · rename_i id' _
      split
      · exact ⟨hr, [], by simp, by simp⟩
      · split_ifs with hc
        · refine ⟨hr, [(id', c, s.now)], rfl, ?_⟩
          intro e he; simp only [List.mem_singleton] at he; subst he
          intro h
          have h' : id' = id := h
          subst h'; exact hc.1 hr
        · exact ⟨hr, [], by simp, by simp⟩

theorem revoke_absorbing (cap : ℕ) (s : St) (ops : List Op) (id : ℕ) (hr : id ∈ s.revoked) :
    ∃ δ, ((sys cap).run s ops).work = s.work ++ δ ∧ ∀ e ∈ δ, e.1 ≠ id := by
  induction ops generalizing s with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons o ops ih =>
    obtain ⟨hr', δ1, h1, h1'⟩ := revoke_step cap s o id hr
    obtain ⟨δ2, h2, h2'⟩ := ih (step cap s o) hr'
    refine ⟨δ1 ++ δ2, ?_, ?_⟩
    · simp only [System.run_cons]; change ((sys cap).run (step cap s o) ops).work = _
      rw [h2, h1, List.append_assoc]
    · intro e he; rcases List.mem_append.1 he with he | he
      · exact h1' e he
      · exact h2' e he

theorem length_le_sum (L : List (ℕ × ℕ × ℕ)) (h : ∀ e ∈ L, 1 ≤ e.2.1) : L.length ≤ (L.map (fun e => e.2.1)).sum := by
  induction L with
  | nil => simp
  | cons e L ih =>
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    have h1 := h e List.mem_cons_self
    have h2 := ih (fun e' he' => h e' (List.mem_cons_of_mem e he'))
    omega

/-- **The number of work units is bounded** (adversarial review D1): every admitted unit costs at least 1, so a lease
admits at most `budget` units, summed over all workers on it, and the whole system at most `cap`. A zero-cost request
is refused. -/
theorem work_count_le (cap : ℕ) (ops : List Op) :
    let s := (sys cap).run init ops
    (∀ l ∈ s.leases, (s.work.filter (fun e => e.1 = l.id)).length ≤ l.budget) ∧ s.work.length ≤ cap := by
  have h := ((spec cap).trace_safe init ops ⟨List.nodup_nil, by simp [init], by simp [init],
    by simp [init, total], by simp [init]⟩).1
  obtain ⟨-, -, hb, ht, hp⟩ := h
  refine ⟨fun l hl => le_trans (length_le_sum _ (fun e he => hp e (List.mem_of_mem_filter he))) (hb l hl),
    le_trans (length_le_sum _ hp) ht⟩

/-- operations the AGENT can issue (the clock, issue and revoke belong to the trusted controller) -/
def agentOp : Op → Prop
  | .fork _ _ => True
  | .work _ _ => True
  | .restart => True
  | _ => False

/-- **The agent cannot issue or un-revoke leases** (review D9-style actor separation): agent operations leave the
lease table and the revocation list unchanged. -/
theorem agent_cannot_issue (cap : ℕ) (s : St) (o : Op) (ho : agentOp o) :
    (step cap s o).leases = s.leases ∧ (step cap s o).revoked = s.revoked := by
  cases o with
  | fork w w' => simp only [step]; split <;> (try split_ifs) <;> simp
  | work w c =>
    simp only [step]; split
    · simp
    · split
      · simp
      · split_ifs <;> simp
  | restart => simp [step]
  | _ => simp [agentOp] at ho

/-- **A revoked worker stays stopped** (review D2): worker 1's lease is revoked; worker 2 (another lease) tries to fork
onto worker 1's identity; the fork is refused because forks may only create fresh workers, and worker 1's work is not
admitted. -/
theorem revoked_worker_stays_stopped :
    let ops := [Op.issue ⟨0, 5, 100⟩ 1, .issue ⟨1, 5, 100⟩ 2, .revoke 0, .fork 2 1, .work 1 3]
    (ops.foldl (step 100) init).work = [] := by
  decide

/-- zero-cost work is refused (review D1) -/
theorem zero_cost_refused :
    ([Op.issue ⟨0, 0, 100⟩ 1, .work 1 0, .work 1 0].foldl (step 100) init).work = [] := by
  decide

/-! ## Necessity: per-worker accounting lets forks multiply a lease -/

/-- the same gate, but the budget check counts only the requesting WORKER's own spend -/
def stepPerWorker (cap : ℕ) (s : St) : Op → St
  | .work w c =>
    match leaseOf s w with
    | none => s
    | some id =>
      match s.leases.find? (fun l => l.id = id) with
      | none => s
      | some l =>
        -- witness only: the third field records the WORKER (not the time) so that spend can be counted per worker
        if id ∉ s.revoked ∧ s.now ≤ l.expiry ∧ spent (s.work.filter (fun e => e.2.2 = w)) id + c ≤ l.budget ∧
            total s.work + c ≤ cap then
          { s with work := s.work ++ [(id, c, w)] }
        else s
  | o => step cap s o

/-- **Forking multiplies per-worker budgets.** Lease 0 has budget 5. Worker 1 forks worker 2, and each spends 5. Under
per-worker accounting both are admitted (lease total 10 > 5); under per-lease accounting only the first is. -/
theorem fork_without_lease_accounting :
    let ops := [Op.issue ⟨0, 5, 100⟩ 1, .fork 1 2, .work 1 5, .work 2 5]
    spent (ops.foldl (stepPerWorker 100) init).work 0 = 10 ∧
    spent (ops.foldl (step 100) init).work 0 = 5 := by
  decide

/-- newest assignment wins: a reissued lease (or a fork onto an existing worker) takes effect -/
theorem reissue_takes_effect :
    let ops := [Op.issue ⟨0, 5, 100⟩ 1, .issue ⟨1, 5, 100⟩ 1, .work 1 3]
    spent (ops.foldl (step 100) init).work 1 = 3 ∧ spent (ops.foldl (step 100) init).work 0 = 0 := by
  decide

end ControlStack.Lease

#print axioms ControlStack.Lease.lease_safe
#print axioms ControlStack.Lease.revoke_absorbing
#print axioms ControlStack.Lease.fork_without_lease_accounting
#print axioms ControlStack.Lease.reissue_takes_effect
#print axioms ControlStack.Lease.work_count_le
#print axioms ControlStack.Lease.agent_cannot_issue
#print axioms ControlStack.Lease.revoked_worker_stays_stopped
#print axioms ControlStack.Lease.zero_cost_refused
