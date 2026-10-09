/-
SC-07: a small model of the egress gateway (allowlist, per-window quota `q`, absorbing HALT) with safety AND progress,
connected to the quantitative bound `SC07Exfil`.

Model: every forwarded send is logged (destination, bits, window). A send is forwarded only if the destination is
allowlisted, the gateway is not halted, and the window's bits stay within `q`. A send that would cross the quota is
dropped whole, like the runtime's crossing packet. `tick` opens a new window.

Results (deployed `full`; adversary class TRACE_ARBITRARY: any sends to any destination, any sizes, any ticks):
- `sc07_safe`: from `init`, every forwarded send went to an allowlisted destination, and every window's forwarded bits
  are ≤ q;
- `halt_freezes`: after a halt nothing more is forwarded;
- `upload_completes`: progress. An upload in chunks to an allowlisted destination, while not halted, whose chunks fit
  the window's remaining quota (e.g. ≤ q in a fresh window), is forwarded in full;
- `total_le`: total forwarded bits ≤ q · (windows opened) (the model's own step). So `exfil_needs_windows`: moving S
  bits out requires at least ⌈S/q⌉ windows to have been opened (`SC07Exfil.ceilDiv`), which is the window premise
  of `SC07Exfil.sc07_plan_bound` derived from this gateway's step;
- witnesses: `quota_off_exceeds`, `allowlist_off_leaks`, `shared_quota_blocks` (another job's traffic in the same
  window consumes the quota and blocks an honest upload; this is the availability price of a shared quota).

Runtime counterparts (prereg/SC07-EGRESS-QUOTA.md, evidence scenarios/SC-07/evidence/run-1):
- H1 allowlist (non-allowlisted sink receives 0 bytes): the destination half of `sc07_safe`;
- H2 quota (count ≤ QUOTA + one MTU): the quota half of `sc07_safe`. The runtime quota is per RUN (one window here),
  measured in bytes on the wire, including headers, with TOL margins; the model counts payload bits with no tolerance;
- H3 under-quota usefulness (0.5 × QUOTA completes byte-exact): `upload_completes`;
- H4 HALT (≤ TOL_HALT bytes after HALT took effect): `halt_freezes` (the model has no in-flight bytes or HALT latency;
  the runtime's TOL_HALT covers data already forwarded when `nft` returned);
- H5 no bypass route: the model's premise that the gateway is the only path;
- H6 negative control (no quota object ⇒ upload completes): `quota_off_exceeds`.
No new mathematics.
-/
import Mathlib.Tactic
import ControlStack.Core.Gate
import ControlStack.Scenarios.SC07Exfil

namespace ControlStack.SC07Liveness

open ControlStack.Gate

structure Env where
  allow : List ℕ
  q : ℕ
  admins : List ℕ

/-- a forwarded send -/
structure Fwd where
  dest : ℕ
  bits : ℕ
  window : ℕ
deriving DecidableEq, Repr

structure St where
  window : ℕ
  used : ℕ
  log : List Fwd
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | send (dest n : ℕ)
  | tick
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  allowCheck : Bool
  quotaCheck : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true⟩

def init : St := ⟨0, 0, [], false⟩

def step (E : Env) (C : Checks) (s : St) : Op → St
  | .send d n =>
    if s.halted ∧ C.haltCheck then s
    else if (C.allowCheck = true → d ∈ E.allow) ∧ (C.quotaCheck = true → s.used + n ≤ E.q) then
      { s with used := s.used + n, log := s.log ++ [⟨d, n, s.window⟩] }
    else s
  | .tick => if s.halted ∧ C.haltCheck then s else { s with window := s.window + 1, used := 0 }
  | .halt c => if c ∈ E.admins then { s with halted := true } else s

def run (E : Env) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step E C) s

theorem run_cons (E : Env) (C : Checks) (s : St) (o : Op) (ops : List Op) :
    run E C s (o :: ops) = run E C (step E C s o) ops := rfl

/-! ## Safety -/

/-- bits forwarded in window `w` -/
def wsum (s : St) (w : ℕ) : ℕ := ((s.log.filter (fun e => e.window = w)).map Fwd.bits).sum

def total (s : St) : ℕ := (s.log.map Fwd.bits).sum

structure Inv (E : Env) (s : St) : Prop where
  dests : ∀ e ∈ s.log, e.dest ∈ E.allow
  cur : wsum s s.window = s.used
  used_le : s.used ≤ E.q
  past : ∀ w, w < s.window → wsum s w ≤ E.q
  wins : ∀ e ∈ s.log, e.window ≤ s.window
  tot : total s ≤ E.q * s.window + s.used

theorem inv_init (E : Env) : Inv E init :=
  ⟨by simp [init], by simp [init, wsum], by simp [init], fun w hw => by simp [init] at hw, by simp [init],
    by simp [init, total]⟩

theorem wsum_append (s t : St) (e : Fwd) (ht : t.log = s.log ++ [e]) (w : ℕ) :
    wsum t w = wsum s w + (if e.window = w then e.bits else 0) := by
  unfold wsum; rw [ht]
  by_cases h : e.window = w <;> simp [List.filter_append, h]

theorem wsum_gt (s : St) (h : ∀ e ∈ s.log, e.window ≤ s.window) (w : ℕ) (hw : s.window < w) : wsum s w = 0 := by
  unfold wsum
  rw [List.filter_eq_nil_iff.2 (fun e he => by have := h e he; simp; omega)]
  rfl

theorem step_inv (E : Env) (s : St) (o : Op) (h : Inv E s) : Inv E (step E full s o) := by
  cases o with
  | send d n =>
    simp only [step]
    split_ifs with h1 h2
    · exact h
    · obtain ⟨hd, hq⟩ := h2
      simp only [full, true_implies] at hd hq
      refine ⟨fun e he => ?_, ?_, hq, fun w hw => ?_, fun e he => ?_, ?_⟩
      · rcases List.mem_append.1 he with he | he
        · exact h.dests e he
        · simp at he; subst he; exact hd
      · rw [wsum_append s _ ⟨d, n, s.window⟩ rfl]; simp [h.cur]
      · rw [wsum_append s _ ⟨d, n, s.window⟩ rfl]
        simp only at hw
        have : ¬ (s.window = w) := by omega
        simp [this]; exact h.past w hw
      · rcases List.mem_append.1 he with he | he
        · exact h.wins e he
        · simp at he; subst he; exact le_rfl
      · simp only [total, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
          add_zero]
        have := h.tot; unfold total at this; omega
    · exact h
  | tick =>
    simp only [step]
    split_ifs
    · exact h
    · refine ⟨h.dests, ?_, Nat.zero_le _, fun w hw => ?_, fun e he => ?_, ?_⟩
      · exact wsum_gt s h.wins _ (Nat.lt_succ_self _)
      · simp only at hw
        rcases Nat.lt_succ_iff_lt_or_eq.1 hw with hw | rfl
        · exact h.past w hw
        · show wsum s s.window ≤ E.q; rw [h.cur]; exact h.used_le
      · exact (h.wins e he).trans (Nat.le_succ _)
      · show total s ≤ E.q * (s.window + 1) + 0
        have := h.tot; have := h.used_le
        rw [Nat.mul_succ]; omega
  | halt c =>
    simp only [step]
    split_ifs
    · exact ⟨h.dests, h.cur, h.used_le, h.past, h.wins, h.tot⟩
    · exact h

theorem run_inv (E : Env) (s : St) (ops : List Op) (h : Inv E s) : Inv E (run E full s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => rw [run_cons]; exact ih _ (step_inv E s o h)

/-- **SC-07 gateway safety.** After any trace from `init`, every forwarded send went to an allowlisted destination, and
every window's forwarded bits are at most `q`. -/
theorem sc07_safe (E : Env) (ops : List Op) :
    (∀ e ∈ (run E full init ops).log, e.dest ∈ E.allow) ∧ ∀ w, wsum (run E full init ops) w ≤ E.q := by
  have h := run_inv E init ops (inv_init E)
  refine ⟨h.dests, fun w => ?_⟩
  rcases lt_trichotomy w (run E full init ops).window with hw | hw | hw
  · exact h.past w hw
  · rw [hw, h.cur]; exact h.used_le
  · rw [wsum_gt _ h.wins w hw]; exact Nat.zero_le _

theorem step_halted (E : Env) (s : St) (o : Op) (hh : s.halted = true) : step E full s o = s := by
  cases o with
  | halt c =>
    simp only [step]
    split_ifs
    · cases s; simp_all
    · rfl
  | _ => simp [step, full, hh]

/-- **HALT**: once halted, nothing more is forwarded (the state is frozen). -/
theorem halt_freezes (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s := by
  induction ops with
  | nil => rfl
  | cons o ops ih => rw [run_cons, step_halted E s o hh, ih]

/-! ## Progress -/

/-- **Under-quota uploads complete.** Not halted, an allowlisted destination, and chunks that fit the window's
remaining quota: every chunk is forwarded, in order, in the current window. -/
theorem upload_completes (E : Env) (s : St) (d : ℕ) (chunks : List ℕ) (hh : s.halted = false) (hd : d ∈ E.allow)
    (hq : s.used + chunks.sum ≤ E.q) :
    (run E full s (chunks.map (fun n => .send d n))).log = s.log ++ chunks.map (fun n => ⟨d, n, s.window⟩) := by
  induction chunks generalizing s with
  | nil => simp [run]
  | cons n ns ih =>
    simp only [List.sum_cons] at hq
    rw [List.map_cons, run_cons]
    have hstep : step E full s (.send d n) = { s with used := s.used + n, log := s.log ++ [⟨d, n, s.window⟩] } := by
      simp only [step, hh, Bool.false_eq_true, false_and, ite_false, full, true_implies]
      rw [ite_eq_left ⟨hd, by omega⟩]
    rw [hstep, ih { s with used := s.used + n, log := s.log ++ [⟨d, n, s.window⟩] } hh (by simp only; omega)]
    simp

/-- an upload of at most `q` bits in a fresh window completes -/
theorem fresh_window_upload (E : Env) (s : St) (d : ℕ) (chunks : List ℕ) (hh : s.halted = false) (hd : d ∈ E.allow)
    (hfresh : s.used = 0) (hq : chunks.sum ≤ E.q) :
    (run E full s (chunks.map (fun n => .send d n))).log = s.log ++ chunks.map (fun n => ⟨d, n, s.window⟩) :=
  upload_completes E s d chunks hh hd (by omega)

/-! ## Connection to `SC07Exfil` -/

/-- **Total forwarded bits ≤ q · (windows opened).** -/
theorem total_le (E : Env) (ops : List Op) :
    total (run E full init ops) ≤ E.q * ((run E full init ops).window + 1) := by
  have h := run_inv E init ops (inv_init E)
  have := h.tot; have := h.used_le
  rw [Nat.mul_succ]; omega

/-- **Exfiltration needs ⌈S/q⌉ windows**, derived from this gateway's step: if S bits have been forwarded, at least
⌈S/q⌉ windows have been opened. -/
theorem exfil_needs_windows (E : Env) (hq : 0 < E.q) (S : ℕ) (ops : List Op) (hS : S ≤ total (run E full init ops)) :
    SC07Exfil.ceilDiv S E.q ≤ (run E full init ops).window + 1 :=
  SC07Exfil.ceilDiv_le S E.q _ hq (hS.trans (total_le E ops))

/-! ## Witnesses

Allowlisted destination 10, other destination 20, q = 8, admin 9. -/

def E0 : Env := ⟨[10], 8, [9]⟩

/-- **Non-vacuity**: an 8-bit upload in two chunks to the allowlisted destination completes. -/
theorem honest_upload : (run E0 full init [.send 10 5, .send 10 3]).log = [⟨10, 5, 0⟩, ⟨10, 3, 0⟩] := by
  decide

/-- without the quota check, 24 bits leave in one window (the H6 negative control's shape) -/
theorem quota_off_exceeds :
    wsum (run E0 { full with quotaCheck := false } init [.send 10 8, .send 10 8, .send 10 8]) 0 = 24 ∧
    wsum (run E0 full init [.send 10 8, .send 10 8, .send 10 8]) 0 = 8 := by
  decide

/-- without the allowlist check, bits reach a non-allowlisted destination -/
theorem allowlist_off_leaks :
    (run E0 { full with allowCheck := false } init [.send 20 4]).log = [⟨20, 4, 0⟩] ∧
    (run E0 full init [.send 20 4]).log = [] := by
  decide

/-- **Availability price**: another job's 6 bits in the same window leave only 2, so an honest 4-bit upload is
dropped; in the next window it completes -/
theorem shared_quota_blocks :
    (run E0 full init [.send 10 6, .send 10 4]).log = [⟨10, 6, 0⟩] ∧
    (run E0 full init [.send 10 6, .tick, .send 10 4]).log = [⟨10, 6, 0⟩, ⟨10, 4, 1⟩] := by
  decide

/-- HALT stops forwarding -/
theorem halt_stops : (run E0 full init [.send 10 2, .halt 9, .send 10 2, .tick, .send 10 2]).log = [⟨10, 2, 0⟩] := by
  decide

end ControlStack.SC07Liveness

#print axioms ControlStack.SC07Liveness.sc07_safe
#print axioms ControlStack.SC07Liveness.halt_freezes
#print axioms ControlStack.SC07Liveness.upload_completes
#print axioms ControlStack.SC07Liveness.fresh_window_upload
#print axioms ControlStack.SC07Liveness.total_le
#print axioms ControlStack.SC07Liveness.exfil_needs_windows
#print axioms ControlStack.SC07Liveness.honest_upload
#print axioms ControlStack.SC07Liveness.quota_off_exceeds
#print axioms ControlStack.SC07Liveness.allowlist_off_leaks
#print axioms ControlStack.SC07Liveness.shared_quota_blocks
#print axioms ControlStack.SC07Liveness.halt_stops
