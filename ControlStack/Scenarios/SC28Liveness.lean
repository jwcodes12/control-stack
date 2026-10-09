/-
SC-28 liveness: the usefulness counterpart of `SC28Budget.sc28_safe`.

Results (deployed configuration `full`):
- `work_accepted`: a work step by a worker whose lease is assigned, issued, unrevoked, and within both its lease
  budget and the global cap (charged at the trusted meter's charge), when not halted, is accepted, and charged exactly
  once to its lease and the global ledger.
- `work_refused_reasons`: conversely, a refused work step has one of exactly these reasons: halted; no lease; the
  lease is not issued; the lease is revoked; the lease budget would be exceeded; the global cap would be exceeded.
- `honest_steps_progress`: a sequence of honest work steps whose total charge fits the lease's remaining budget and the
  remaining global cap is accepted in full.
- `progress_interleaved`: after ANY legal interleaving of other operations, an honest step that was admissible before
  is still accepted, unless one of these happened in between: a halt; revocation of its lease; reassignment of the
  worker; consumption of its lease by a co-holder (a descendant sharing the lease: descendant attribution); or
  consumption of the global cap by anyone. Nothing else blocks it.
- Availability prices (witnesses): `global_cap_blocks_honest` (another agent exhausts the shared global cap, and an
  honest worker with lease budget left is refused; this is the honest cost of a shared budget);
  `descendant_consumes_lease` (a forked child spends the parent's lease); halting is `SC28.halt_freezes`.

Runtime counterparts (prereg/SC28-CGROUP-METER.md, evidence scenarios/SC-28/evidence/run-1):
- H2 (b2), "B gets 3 successes and 9 EAGAIN… the run's cap binding": `global_cap_blocks_honest` is the model's version
  (the joint cap refuses an agent whose own lease would still allow the step); H2 (b1), 7 of 12 forks succeed:
  `honest_steps_progress` / `work_refused_reasons` (accepted while within the lease, refused at the bound);
- H1 attribution: the descendant-attribution premise (`SC28.fork_shares_lease`, `descendant_consumes_lease`);
- H3 revocation: `SC28.revoked_lease_stops` and the revocation blocker here;
- H4 HALT: `SC28.halt_freezes` and the halt blocker here;
- H5 placement is the model's premise that the trusted meter sees all consumption.
Where the runtime measures what the model does not: CPU RATE (CFS bandwidth per 100 ms period, H2(a)) and latencies
of termination and reaping. The model's work units are abstract charges; time and rates are outside it.
No new mathematics.
-/
import Mathlib.Tactic
import ControlStack.Scenarios.SC28Budget

namespace ControlStack.SC28Liveness

open ControlStack.SC28

variable (admins : List ℕ) (G : ℕ)

/-- **An admissible work step is accepted**, charged once to its lease and the global ledger. -/
theorem work_accepted (s : St) (w a r lid b : ℕ) (hh : s.halted = false) (hl : leaseOf s w = some lid)
    (hb : budgetOf s lid = some b) (hr : lid ∉ s.revoked) (hcl : spentL s lid + charge full a r ≤ b)
    (hcg : spentT s + charge full a r ≤ G) :
    step admins G full s (.work w a r) =
      { s with ledger := s.ledger ++ [(lid, charge full a r)], usage := s.usage ++ [(w, lid, a)] } := by
  simp only [step, hh, Bool.false_eq_true, false_and, ite_false, hl, hb]
  rw [ite_eq_left ⟨hr, hcl, fun _ => hcg⟩]

/-- **The only reasons a work step is refused.** -/
theorem work_refused_reasons (s : St) (w a r : ℕ) (href : (step admins G full s (.work w a r)).usage = s.usage) :
    s.halted = true ∨ leaseOf s w = none ∨
      ∃ lid, leaseOf s w = some lid ∧ (budgetOf s lid = none ∨ lid ∈ s.revoked ∨
        ∃ b, budgetOf s lid = some b ∧ (b < spentL s lid + charge full a r ∨ G < spentT s + charge full a r)) := by
  by_contra hcon
  simp only [not_or, not_exists, not_and] at hcon
  obtain ⟨hh, hl, hrest⟩ := hcon
  have hh' : s.halted = false := by cases h : s.halted <;> simp_all
  obtain ⟨lid, hlid⟩ : ∃ lid, leaseOf s w = some lid := by
    cases h : leaseOf s w with
    | none => exact absurd h hl
    | some lid => exact ⟨lid, rfl⟩
  obtain ⟨hb0, hrv, hbud⟩ := hrest lid hlid
  obtain ⟨b, hb⟩ : ∃ b, budgetOf s lid = some b := by
    cases h : budgetOf s lid with
    | none => exact absurd h hb0
    | some b => exact ⟨b, rfl⟩
  obtain ⟨h1, h2⟩ := hbud b hb
  rw [work_accepted admins G s w a r lid b hh' hlid hb hrv (by omega) (by omega)] at href
  simp at href

/-! ## Honest runs and interleavings -/

theorem spentL_append {s t : St} {lid ch : ℕ} (ht : t.ledger = s.ledger ++ [(lid, ch)]) (l : ℕ) :
    spentL t l = spentL s l + (if lid = l then ch else 0) := by
  unfold spentL
  rw [ht]
  by_cases h : lid = l <;> simp [List.filter_append, h]

theorem spentT_append {s t : St} {lid ch : ℕ} (ht : t.ledger = s.ledger ++ [(lid, ch)]) :
    spentT t = spentT s + ch := by
  unfold spentT; rw [ht]; simp

/-- the charges of honest work units -/
def charges (as : List ℕ) : ℕ := (as.map (fun a => charge full a a)).sum

/-- **Honest steps make progress.** A worker with an assigned, issued, unrevoked lease, not halted, whose honest work
units' total charge fits the lease's remaining budget and the remaining global cap, gets every step accepted. -/
theorem honest_steps_progress (s : St) (w lid b : ℕ) (as : List ℕ) (hh : s.halted = false)
    (hl : leaseOf s w = some lid) (hb : budgetOf s lid = some b) (hr : lid ∉ s.revoked)
    (hcl : spentL s lid + charges as ≤ b) (hcg : spentT s + charges as ≤ G) :
    (run admins G full s (as.map (fun a => .work w a a))).usage = s.usage ++ as.map (fun a => (w, lid, a)) := by
  induction as generalizing s with
  | nil => simp [run]
  | cons a as ih =>
    simp only [charges, List.map_cons, List.sum_cons] at hcl hcg
    rw [List.map_cons, run_cons, work_accepted admins G s w a a lid b hh hl hb hr (by omega) (by omega)]
    have := ih { s with ledger := s.ledger ++ [(lid, charge full a a)], usage := s.usage ++ [(w, lid, a)] } hh hl hb hr
      (by rw [spentL_append (s := s) rfl]; simp only [ite_true, charges]; omega)
      (by rw [spentT_append (s := s) rfl]; simp only [charges]; omega)
    rw [this]
    simp

/-- budgets of issued leases never change (leases are only issued fresh; forks with descendant attribution add none) -/
theorem budget_step (s : St) (o : Op) (lid b : ℕ) (hb : budgetOf s lid = some b) :
    budgetOf (step admins G full s o) lid = some b := by
  cases o with
  | issue c l b' =>
    simp only [step]
    split_ifs with h1 h2
    · exact hb
    · rw [budgetOf_append s l b' h2.2]
      have : lid ≠ l := fun he => by rw [he, h2.2] at hb; simp at hb
      simp [this, hb]
    · exact hb
  | fork c p ch nl =>
    simp only [step]
    split_ifs
    · exact hb
    · simp only [budgetOf, forkUpd_full_leases]; exact hb
  | _ =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals exact hb

theorem budget_run (s : St) (ops : List Op) (lid b : ℕ) (hb : budgetOf s lid = some b) :
    budgetOf (run admins G full s ops) lid = some b := by
  induction ops generalizing s with
  | nil => exact hb
  | cons o ops ih => rw [run_cons]; exact ih _ (budget_step admins G s o lid b hb)

/-- **Progress despite any interleaving.** Let a work step be admissible at `s`. After any operations `p`, it is still
accepted unless, in the reached state, the gate is halted, the lease is revoked, the worker was reassigned, the lease
was consumed further (by the worker's lineage), or the global ledger grew (anyone's work). -/
theorem progress_interleaved (s : St) (w a lid b : ℕ) (_hl : leaseOf s w = some lid) (hb : budgetOf s lid = some b)
    (hcl : spentL s lid + charge full a a ≤ b) (hcg : spentT s + charge full a a ≤ G) (p : List Op) :
    let t := run admins G full s p
    (step admins G full t (.work w a a)).usage = t.usage ++ [(w, lid, a)] ∨
      t.halted = true ∨ lid ∈ t.revoked ∨ leaseOf t w ≠ some lid ∨ spentL s lid < spentL t lid ∨
      spentT s < spentT t := by
  intro t
  by_cases hh : t.halted = true
  · exact Or.inr (Or.inl hh)
  by_cases hr : lid ∈ t.revoked
  · exact Or.inr (Or.inr (Or.inl hr))
  by_cases hlt : leaseOf t w ≠ some lid
  · exact Or.inr (Or.inr (Or.inr (Or.inl hlt)))
  by_cases hsl : spentL s lid < spentL t lid
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hsl))))
  by_cases hst : spentT s < spentT t
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hst))))
  left
  simp only [ne_eq, not_not, not_lt] at hlt hsl hst
  have hh' : t.halted = false := by cases h : t.halted <;> simp_all
  rw [work_accepted admins G t w a a lid b hh' hlt (budget_run admins G s p lid b hb) hr (by omega) (by omega)]

/-! ## Availability prices of a shared budget -/

/-- **A shared global cap blocks an honest worker.** Agent 2 spends the whole global cap (10) on its own lease; agent
1's step is refused although its own lease (budget 10) is untouched. -/
theorem global_cap_blocks_honest :
    let s := run [9] 10 full init [.issue 9 0 10, .issue 9 1 10, .assignTo 9 1 0, .assignTo 9 2 1, .work 2 10 10]
    (step [9] 10 full s (.work 1 1 1)).usage = s.usage ∧ spentL s 0 = 0 ∧ s.usage = [(2, 1, 10)] := by
  decide

/-- **Descendant attribution consumes the parent's lease.** A forked child of worker 1 spends lease 0's budget, and
worker 1's next step is refused. -/
theorem descendant_consumes_lease :
    let s := run [9] 100 full init [.issue 9 0 5, .assignTo 9 1 0, .fork 1 1 2 7, .work 2 5 5]
    (step [9] 100 full s (.work 1 1 1)).usage = s.usage ∧ s.usage = [(2, 0, 5)] := by
  decide

/-- **Non-vacuity**: an honest worker's three steps (charges 2 + 3 + 1) within lease 10 and cap 10 are all accepted. -/
theorem honest_example :
    (run [9] 10 full (run [9] 10 full init [.issue 9 0 10, .assignTo 9 1 0]) ([2, 3, 1].map (fun a => .work 1 a a))).usage =
      [(1, 0, 2), (1, 0, 3), (1, 0, 1)] := by
  decide

end ControlStack.SC28Liveness

#print axioms ControlStack.SC28Liveness.work_accepted
#print axioms ControlStack.SC28Liveness.work_refused_reasons
#print axioms ControlStack.SC28Liveness.honest_steps_progress
#print axioms ControlStack.SC28Liveness.progress_interleaved
#print axioms ControlStack.SC28Liveness.global_cap_blocks_honest
#print axioms ControlStack.SC28Liveness.descendant_consumes_lease
#print axioms ControlStack.SC28Liveness.honest_example
