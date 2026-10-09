/-
SC-14: no runaway compute, tokens, network or budget.

Relation to `Scenarios/SC28Budget.lean`: SC-28 proves the shared-ledger part for ONE resource — a global cap and
per-lease budgets across agents, forks charged to their parent's lease, sticky revocation, a trusted meter and the
anti-rollback premise. This file adds the dimensions SC-14 needs on top, for a single shared account: a VECTOR of
resources (compute, tokens, network bytes), each with its own cap and metered separately; a RATE limit per time window
for each resource; and an expiry after which no work is admitted. (Instantiating SC-28 once per resource gives the
per-lineage version of the cap part.)

The model:
- each work step consumes a usage vector measured by a TRUSTED meter (the agent's own report is ignored);
- a step is admitted only if, for EVERY resource, cumulative usage stays within that resource's cap
  (`perResource`; the weaker design checks only the total), the current window's usage stays within the rate limit,
  and the clock is before the expiry an admin set;
- `tick` advances the clock and opens a new window; durable counters survive restarts (a storage `rollback` of the
  counters is excluded by the anti-rollback premise `legal`);
- an absorbing admin HALT.

Main results (deployed configuration `full`; adversary class TRACE_ARBITRARY minus rollback: any usage vectors, any
reports, any interleaving with ticks):
- `sc14_safe`: from `init`, cumulative ACTUAL usage of every resource is within its cap, every window's actual usage of
  every resource is within its rate limit, and every step ran before the expiry in force when it ran;
- `halt_freezes`; `sys`/`spec` (client of `Core/Gate.lean`); non-vacuity `honest_work`.

Necessity witnesses: `aggregate_cap_breaks` (one resource exceeds its own cap under a total-only check),
`reported_cost_breaks`, `rate_burst_breaks`, `no_expiry_breaks`, `rollback_double_spends`, `no_halt_check_breaks`.

Premises outside the model: the meter sees all consumption (including descendants and deputies — SC-28's lineage
attribution); the clock is trusted; the counters cannot be rolled back. No new mathematics.
-/
import Mathlib.Tactic
import ControlStack.Core.Gate

namespace ControlStack.SC14

open ControlStack.Gate

/-- a resource vector: (compute, tokens, network); `+` and `≤` are componentwise -/
abbrev Vec := ℕ × ℕ × ℕ

def total (v : Vec) : ℕ := v.1 + v.2.1 + v.2.2

structure Env where
  cap : Vec
  rate : Vec
  admins : List ℕ

/-- a usage record: actual usage, clock at the step, expiry in force -/
abbrev Use := Vec × ℕ × ℕ

structure St where
  spent : Vec
  window : Vec
  clock : ℕ
  expiry : ℕ
  usage : List Use
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | work (actual reported : Vec)
  | tick
  | setExpiry (caller t : ℕ)
  | rollback
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  meter : Bool
  perResource : Bool
  rate : Bool
  expiry : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true, true⟩

def init (exp : ℕ) : St := ⟨0, 0, 0, exp, [], false⟩

def charge (C : Checks) (actual reported : Vec) : Vec := if C.meter then actual else reported

def capOk (E : Env) (C : Checks) (v : Vec) : Prop := if C.perResource then v ≤ E.cap else total v ≤ total E.cap

instance (E : Env) (C : Checks) (v : Vec) : Decidable (capOk E C v) := by unfold capOk; infer_instance

def step (E : Env) (C : Checks) (s : St) : Op → St
  | .work a r =>
    if s.halted ∧ C.haltCheck then s
    else if (C.expiry = true → s.clock < s.expiry) ∧ capOk E C (s.spent + charge C a r) ∧
        (C.rate = true → s.window + charge C a r ≤ E.rate) then
      { s with spent := s.spent + charge C a r, window := s.window + charge C a r,
               usage := s.usage ++ [(a, s.clock, s.expiry)] }
    else s
  | .tick => if s.halted ∧ C.haltCheck then s else { s with clock := s.clock + 1, window := 0 }
  | .setExpiry c t => if s.halted ∧ C.haltCheck then s else if c ∈ E.admins then { s with expiry := t } else s
  | .rollback => { s with spent := 0 }
  | .halt c => if c ∈ E.admins then { s with halted := true } else s

def run (E : Env) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step E C) s

theorem run_cons (E : Env) (C : Checks) (s : St) (o : Op) (ops : List Op) :
    run E C s (o :: ops) = run E C (step E C s o) ops := rfl

/-- anti-rollback premise -/
def legal : Op → Prop
  | .rollback => False
  | _ => True

/-! ## Invariant and safety -/

/-- actual usage in window `t` -/
def windowSum (s : St) (t : ℕ) : Vec := ((s.usage.filter (fun u => u.2.1 = t)).map Prod.fst).sum

def usedTotal (s : St) : Vec := (s.usage.map Prod.fst).sum

def Good (E : Env) (s : St) : Prop :=
  usedTotal s ≤ E.cap ∧ (∀ t, windowSum s t ≤ E.rate) ∧ ∀ u ∈ s.usage, u.2.1 < u.2.2

structure Inv (E : Env) (s : St) : Prop where
  spent_eq : s.spent = usedTotal s
  spent_le : s.spent ≤ E.cap
  win_eq : s.window = windowSum s s.clock
  win_le : s.window ≤ E.rate
  past : ∀ t, t < s.clock → windowSum s t ≤ E.rate
  clocks : ∀ u ∈ s.usage, u.2.1 ≤ s.clock
  exp_ok : ∀ u ∈ s.usage, u.2.1 < u.2.2

theorem vzero_le (v : Vec) : (0 : Vec) ≤ v := by
  simp only [Prod.le_def]
  exact ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩

theorem inv_init (E : Env) (exp : ℕ) : Inv E (init exp) :=
  ⟨by simp [init, usedTotal], vzero_le _, by simp [init, windowSum], vzero_le _,
    fun t _ => by simp only [init, windowSum, List.filter_nil, List.map_nil, List.sum_nil]; exact vzero_le _,
    by simp [init], by simp [init]⟩

theorem windowSum_append (s : St) (u : Use) (t : ℕ) :
    windowSum { s with usage := s.usage ++ [u] } t = windowSum s t + (if u.2.1 = t then u.1 else 0) := by
  unfold windowSum
  split_ifs with h <;> simp [List.filter_append, h]

theorem windowSum_gt {s : St} (h : ∀ u ∈ s.usage, u.2.1 ≤ s.clock) (t : ℕ) (ht : s.clock < t) : windowSum s t = 0 := by
  unfold windowSum
  rw [List.filter_eq_nil_iff.2 (fun u hu => by have := h u hu; simp; omega)]
  rfl

theorem Inv.good {E : Env} {s : St} (h : Inv E s) : Good E s := by
  refine ⟨h.spent_eq ▸ h.spent_le, fun t => ?_, h.exp_ok⟩
  rcases lt_trichotomy t s.clock with ht | rfl | ht
  · exact h.past t ht
  · rw [← h.win_eq]; exact h.win_le
  · rw [windowSum_gt h.clocks t ht]; exact vzero_le _

theorem step_inv (E : Env) (s : St) (o : Op) (ho : legal o) (h : Inv E s) : Inv E (step E full s o) := by
  cases o with
  | work a r =>
    simp only [step]
    split_ifs with h1 h2
    · exact h
    · obtain ⟨he, hc, hr⟩ := h2
      have hch : charge full a r = a := rfl
      simp only [hch, show full.expiry = true from rfl, show full.rate = true from rfl, true_implies, capOk,
        show full.perResource = true from rfl, ite_true] at he hc hr ⊢
      refine ⟨?_, hc, ?_, hr, fun t ht => ?_, fun u hu => ?_, fun u hu => ?_⟩
      · simp [usedTotal, h.spent_eq]
      · show s.window + a = windowSum { s with usage := s.usage ++ [(a, s.clock, s.expiry)] } s.clock
        rw [windowSum_append, h.win_eq]
        simp
      · change t < s.clock at ht
        show windowSum { s with usage := s.usage ++ [(a, s.clock, s.expiry)] } t ≤ E.rate
        rw [windowSum_append, ite_eq_right (by simp; omega), add_zero]
        exact h.past t ht
      · rcases List.mem_append.1 hu with hu | hu
        · exact h.clocks u hu
        · simp at hu; subst hu; exact le_rfl
      · rcases List.mem_append.1 hu with hu | hu
        · exact h.exp_ok u hu
        · simp at hu; subst hu; exact he
    · exact h
  | tick =>
    simp only [step]
    split_ifs
    · exact h
    · refine ⟨h.spent_eq, h.spent_le, ?_, vzero_le _, fun t ht => ?_, fun u hu => ?_, h.exp_ok⟩
      · exact (windowSum_gt h.clocks _ (Nat.lt_succ_self _)).symm
      · change t < s.clock + 1 at ht
        show windowSum s t ≤ E.rate
        rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | ht
        · exact h.past t ht
        · subst ht; rw [← h.win_eq]; exact h.win_le
      · exact (h.clocks u hu).trans (Nat.le_succ _)
  | setExpiry c t =>
    simp only [step]
    split_ifs
    all_goals first | exact h | exact ⟨h.spent_eq, h.spent_le, h.win_eq, h.win_le, h.past, h.clocks, h.exp_ok⟩
  | rollback => exact absurd ho (by simp [legal])
  | halt c =>
    simp only [step]
    split_ifs
    · exact ⟨h.spent_eq, h.spent_le, h.win_eq, h.win_le, h.past, h.clocks, h.exp_ok⟩
    · exact h

theorem run_inv (E : Env) (s : St) (ops : List Op) (hops : ∀ o ∈ ops, legal o) (h : Inv E s) :
    Inv E (run E full s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih =>
    rw [run_cons]
    exact ih _ (fun o' ho' => hops o' (List.mem_cons_of_mem o ho')) (step_inv E s o (hops o List.mem_cons_self) h)

/-- **SC-14 safety.** After any legal trace from `init`, cumulative actual usage of every resource is within its cap,
every window's actual usage of every resource is within its rate limit, and every step ran before the expiry in force.
Adversary: TRACE_ARBITRARY minus storage rollback. -/
theorem sc14_safe (E : Env) (exp : ℕ) (ops : List Op) (hops : ∀ o ∈ ops, legal o) :
    Good E (run E full (init exp) ops) :=
  (run_inv E _ ops hops (inv_init E exp)).good

/-! ## Halt -/

theorem step_halted (E : Env) (s : St) (o : Op) (hh : s.halted = true) :
    (step E full s o).usage = s.usage ∧ (step E full s o).halted = true := by
  cases o with
  | rollback => simp [step, hh]
  | halt c => simp only [step]; split_ifs <;> simp [hh]
  | _ => simp [step, full, hh]

/-- **Halt freezes work**: once halted, no trace adds usage. -/
theorem halt_freezes (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) :
    (run E full s ops).usage = s.usage := by
  induction ops generalizing s with
  | nil => rfl
  | cons o ops ih =>
    rw [run_cons]
    obtain ⟨h1, h2⟩ := step_halted E s o hh
    rw [ih _ h2, h1]

/-! ## Client of the shared gate interface -/

theorem usage_prefix (E : Env) (C : Checks) (s : St) (o : Op) : s.usage <+: (step E C s o).usage := by
  cases o with
  | work a r =>
    simp only [step]
    split_ifs
    · exact List.prefix_refl _
    · exact List.prefix_append _ _
    · exact List.prefix_refl _
  | rollback => exact List.prefix_refl _
  | _ => simp only [step]; split_ifs <;> exact List.prefix_refl _

def sys (E : Env) : System St {o : Op // legal o} Use where
  step := fun s o => step E full s o.1
  effects := St.usage

def spec (E : Env) : Spec (sys E) where
  Inv := Inv E
  ok := fun _ u => u.2.1 < u.2.2
  step_inv := fun s o h => step_inv E s o.1 o.2 h
  log_prefix := fun s o => usage_prefix E full s o.1
  inv_ok := fun _ h u hu => h.exp_ok u hu

/-! ## Non-vacuity and necessity witnesses

Caps (10, 10, 10), rate (5, 5, 5) per window, admin 9. -/

def E0 : Env := ⟨(10, 10, 10), (5, 5, 5), [9]⟩

/-- **Non-vacuity**: work within caps, rates and expiry runs. -/
theorem honest_work :
    (run E0 full (init 100) [.work (2, 2, 2) (2, 2, 2), .tick, .work (3, 3, 3) (3, 3, 3)]).usage =
      [((2, 2, 2), 0, 100), ((3, 3, 3), 1, 100)] := by
  decide

/-- with only a total cap, network alone reaches 16 > 10 while the total stays within 30 -/
theorem aggregate_cap_breaks :
    let ops := [Op.work (0, 0, 4) 0, .tick, .work (0, 0, 4) 0, .tick, .work (0, 0, 4) 0, .tick, .work (0, 0, 4) 0]
    usedTotal (run E0 { full with perResource := false } (init 100) ops) = (0, 0, 16) ∧
    usedTotal (run E0 full (init 100) ops) = (0, 0, 8) := by
  decide

/-- charging the agent-reported cost (zero) instead of metered usage -/
theorem reported_cost_breaks :
    let ops := [Op.work (0, 0, 9) 0, .tick, .work (0, 0, 9) 0, .tick, .work (0, 0, 9) 0]
    usedTotal (run E0 { full with meter := false } (init 100) ops) = (0, 0, 27) ∧
    usedTotal (run E0 full (init 100) ops) = 0 := by
  decide

/-- without the rate limit, a burst of 9 > 5 units in one window -/
theorem rate_burst_breaks :
    usedTotal (run E0 { full with rate := false } (init 100) [.work (0, 0, 9) 0]) = (0, 0, 9) ∧
    usedTotal (run E0 full (init 100) [.work (0, 0, 9) 0]) = 0 := by
  decide

/-- without the expiry check, work continues after the lease expired -/
theorem no_expiry_breaks :
    (run E0 { full with expiry := false } (init 1) [.tick, .work (1, 1, 1) 0]).usage = [((1, 1, 1), 1, 1)] ∧
    (run E0 full (init 1) [.tick, .work (1, 1, 1) 0]).usage = [] := by
  decide

/-- a storage rollback of the counters double-spends: the anti-rollback premise cannot be dropped -/
theorem rollback_double_spends :
    usedTotal (run E0 full (init 100)
      [.work (0, 0, 5) 0, .tick, .work (0, 0, 5) 0, .rollback, .tick, .work (0, 0, 5) 0]) = (0, 0, 15) := by
  decide

/-- without the halt check, work continues after a halt -/
theorem no_halt_check_breaks :
    (run E0 { full with haltCheck := false } (init 100) [.halt 9, .work (1, 1, 1) 0]).usage = [((1, 1, 1), 0, 100)] ∧
    (run E0 full (init 100) [.halt 9, .work (1, 1, 1) 0]).usage = [] := by
  decide

end ControlStack.SC14

#print axioms ControlStack.SC14.sc14_safe
#print axioms ControlStack.SC14.halt_freezes
#print axioms ControlStack.SC14.spec
#print axioms ControlStack.SC14.honest_work
#print axioms ControlStack.SC14.aggregate_cap_breaks
#print axioms ControlStack.SC14.reported_cost_breaks
#print axioms ControlStack.SC14.rate_burst_breaks
#print axioms ControlStack.SC14.no_expiry_breaks
#print axioms ControlStack.SC14.rollback_double_spends
#print axioms ControlStack.SC14.no_halt_check_breaks
