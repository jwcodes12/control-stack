/-
SC-17 between applies: a bounded DRIFT WINDOW (review packet 2026-10-09 §0.2 / §9, witness W2: `sc17_safe` constrains the
live state only at applies, and out-of-band grants can push live state above the ceiling between reconciles).

This file states what CAN be guaranteed between applies. Out-of-band mutations are reverted, not prevented. So the
honest claim is a bound on how many out-of-band grants can be live at once, and on how long any one lives:
- the live state is the desired state plus out-of-band grants (`oob`), each recorded with its birth time (ghost);
- the environment admits at most `d` out-of-band mutations per tick (an ATTACKER-CAPABILITY premise, enforced in the
  model as a per-tick counter; it is not a gate behaviour);
- a trusted scheduler reconciles at least every `W` ticks (`sched`; `tick` triggers the reconcile when it is due); a
  reconcile resets live to desired; manual reconciles may happen any time.

Main results (adversary class TRACE_ARBITRARY over `oob`, `tick`, `reconcile`; premises `0 < W`):
- `drift_bounded`: at every reachable state, live grants not in the desired state number at most `d · W`;
- `drift_lifetime`: every out-of-band grant currently live was born less than `W` ticks ago;
- `live_eq`: live = (current out-of-band grants) ++ desired; so with the SC-17 ceiling `allowed`, the excess over the
  approved state is at most `d · W` grants for at most `W` ticks. That is NOT "live always within the ceiling":
  `ceiling_exceeded_between_reconciles` is that limit, made explicit.

Witness: `no_schedule_unbounded_lifetime` (no reconcile schedule: an out-of-band grant is still live after any number
of ticks).

Premises outside the model: the reconciler sees the whole live state and its writes succeed; the clock is trusted; the
per-tick bound `d` is an assumption about the attacker's out-of-band write rate (e.g. API rate limits). No new
mathematics.
-/
import Mathlib.Tactic

namespace ControlStack.SC17Drift

structure St where
  desired : List ℕ
  live : List ℕ
  /-- ghost: out-of-band grants since the last reconcile, with birth times -/
  drift : List (ℕ × ℕ)
  clock : ℕ
  lastRec : ℕ
  /-- out-of-band mutations admitted in the current tick -/
  tickOob : ℕ
deriving DecidableEq, Repr

inductive Op where
  | oob (g : ℕ)
  | tick
  | reconcile
deriving DecidableEq, Repr

def init (desired : List ℕ) : St := ⟨desired, desired, [], 0, 0, 0⟩

def doReconcile (s : St) (t : ℕ) : St := { s with live := s.desired, drift := [], lastRec := t }

/-- `d`: out-of-band mutations per tick (environment premise); `W`: reconcile period; `sched`: the scheduler is on -/
def step (d W : ℕ) (sched : Bool) (s : St) : Op → St
  | .oob g =>
    if s.tickOob < d then { s with live := g :: s.live, drift := (g, s.clock) :: s.drift, tickOob := s.tickOob + 1 }
    else s
  | .tick =>
    if sched ∧ s.lastRec + W ≤ s.clock + 1 then { doReconcile s (s.clock + 1) with clock := s.clock + 1, tickOob := 0 }
    else { s with clock := s.clock + 1, tickOob := 0 }
  | .reconcile => doReconcile s s.clock

def run (d W : ℕ) (sched : Bool) (s : St) (ops : List Op) : St := ops.foldl (step d W sched) s

theorem run_cons (d W : ℕ) (sched : Bool) (s : St) (o : Op) (ops : List Op) :
    run d W sched s (o :: ops) = run d W sched (step d W sched s o) ops := rfl

structure Inv (d W : ℕ) (s : St) : Prop where
  live_eq : s.live = s.drift.map Prod.fst ++ s.desired
  births : ∀ p ∈ s.drift, s.lastRec ≤ p.2 ∧ p.2 ≤ s.clock
  rec_le : s.lastRec ≤ s.clock
  period : s.clock < s.lastRec + W
  count : s.drift.length ≤ d * (s.clock - s.lastRec) + s.tickOob
  tick_le : s.tickOob ≤ d

theorem inv_init (d W : ℕ) (hW : 0 < W) (desired : List ℕ) : Inv d W (init desired) :=
  ⟨by simp [init], by simp [init], le_rfl, by simp [init]; omega, by simp [init], by simp [init]⟩

theorem step_inv (d W : ℕ) (hW : 0 < W) (s : St) (o : Op) (h : Inv d W s) : Inv d W (step d W true s o) := by
  cases o with
  | oob g =>
    simp only [step]
    split_ifs with h1
    · refine ⟨by simp [h.live_eq], fun p hp => ?_, h.rec_le, h.period, ?_, by simp only; omega⟩
      · simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact ⟨h.rec_le, le_rfl⟩
        · exact h.births p hp
      · simp only [List.length_cons]; have := h.count; omega
    · exact h
  | tick =>
    simp only [step, true_and]
    split_ifs with h1
    · exact ⟨by simp [doReconcile], by simp [doReconcile], by simp [doReconcile], by simp [doReconcile]; omega,
        by simp [doReconcile], by simp⟩
    · refine ⟨h.live_eq, fun p hp => ?_, by simp only; have := h.rec_le; omega, by simp only; omega, ?_, by simp⟩
      · obtain ⟨a, b⟩ := h.births p hp; exact ⟨a, by simp only; omega⟩
      · simp only
        have hc := h.count
        have ht := h.tick_le
        have hr := h.rec_le
        have : s.clock + 1 - s.lastRec = (s.clock - s.lastRec) + 1 := by omega
        rw [this, Nat.mul_succ]
        omega
  | reconcile =>
    simp only [step]
    exact ⟨by simp [doReconcile], by simp [doReconcile], by simp [doReconcile], by simp [doReconcile]; omega,
      by simp [doReconcile], h.tick_le⟩

theorem run_inv (d W : ℕ) (hW : 0 < W) (s : St) (ops : List Op) (h : Inv d W s) : Inv d W (run d W true s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => rw [run_cons]; exact ih _ (step_inv d W hW s o h)

/-- **Live = out-of-band grants since the last reconcile, plus the desired state.** -/
theorem live_eq (d W : ℕ) (hW : 0 < W) (desired : List ℕ) (ops : List Op) :
    (run d W true (init desired) ops).live =
      (run d W true (init desired) ops).drift.map Prod.fst ++ (run d W true (init desired) ops).desired :=
  (run_inv d W hW _ ops (inv_init d W hW desired)).live_eq

theorem drift_bounded_of_inv (d W : ℕ) (hW : 0 < W) (s : St) (h : Inv d W s) :
    (s.live.filter (fun g => g ∉ s.desired)).length ≤ d * W := by
  have h1 : (s.live.filter (fun g => g ∉ s.desired)).length ≤ s.drift.length := by
    rw [h.live_eq, List.filter_append, List.length_append]
    have : (s.desired.filter (fun g => g ∉ s.desired)).length = 0 := by
      rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]; intro g hg; simp [hg]
    rw [this, add_zero]
    exact (List.length_filter_le _ _).trans (by simp)
  have h2 : s.clock - s.lastRec ≤ W - 1 := by have := h.period; omega
  have h3 : d * (s.clock - s.lastRec) ≤ d * (W - 1) := Nat.mul_le_mul_left d h2
  have h4 : d * (W - 1) + d = d * W := by
    conv_rhs => rw [show W = (W - 1) + 1 by omega]
    rw [Nat.mul_succ]
  have := h.count
  have := h.tick_le
  omega

/-- **Drift is bounded**: at every reachable state, at most `d · W` live grants are outside the desired state. -/
theorem drift_bounded (d W : ℕ) (hW : 0 < W) (desired : List ℕ) (ops : List Op) :
    ((run d W true (init desired) ops).live.filter
      (fun g => g ∉ (run d W true (init desired) ops).desired)).length ≤ d * W :=
  drift_bounded_of_inv d W hW _ (run_inv d W hW _ ops (inv_init d W hW desired))

/-- **Bounded lifetime**: every out-of-band grant currently live was born less than `W` ticks ago. -/
theorem drift_lifetime (d W : ℕ) (hW : 0 < W) (desired : List ℕ) (ops : List Op) :
    ∀ p ∈ (run d W true (init desired) ops).drift, (run d W true (init desired) ops).clock - p.2 < W := by
  intro p hp
  have h := run_inv d W hW _ ops (inv_init d W hW desired)
  have := h.births p hp
  have := h.period
  omega

/-- **The limit, made explicit**: between reconciles the live state is above the desired one (here a grant the
ceiling might forbid is live), even with the scheduler on. -/
theorem ceiling_exceeded_between_reconciles :
    (run 1 3 true (init []) [.oob 7]).live = [7] := by
  decide

/-- **Witness: no reconcile schedule, unbounded lifetime.** Without the scheduler, an out-of-band grant born at time 0
is still live after 10 ticks (and after any number: the scheduler-free `tick` never touches `live`). -/
theorem no_schedule_unbounded_lifetime :
    (run 1 3 false (init []) ([.oob 7] ++ List.replicate 10 .tick)).live = [7] ∧
    (run 1 3 false (init []) ([.oob 7] ++ List.replicate 10 .tick)).clock = 10 ∧
    (run 1 3 true (init []) ([.oob 7] ++ List.replicate 10 .tick)).live = [] := by
  decide

theorem tick_unscheduled_keeps_live (d W : ℕ) (s : St) : (step d W false s .tick).live = s.live := by
  simp [step]

end ControlStack.SC17Drift

#print axioms ControlStack.SC17Drift.live_eq
#print axioms ControlStack.SC17Drift.drift_bounded
#print axioms ControlStack.SC17Drift.drift_lifetime
#print axioms ControlStack.SC17Drift.ceiling_exceeded_between_reconciles
#print axioms ControlStack.SC17Drift.no_schedule_unbounded_lifetime
#print axioms ControlStack.SC17Drift.tick_unscheduled_keeps_live
