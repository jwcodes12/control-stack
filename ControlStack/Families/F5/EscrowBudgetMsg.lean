/-
F5 escrow across hosts with EXPLICIT MESSAGE PASSING. This answers the Gemini batch-4 review of
`F5/EscrowBudget.lean` (reviews/lean-2026-10-09-batch4/gemini-review.md), which found three modelling gaps:
- settlement read the host's spend instantaneously (shared memory);
- `crash` was a no-op that left the host reachable;
- host clocks were neither stored nor monotone, and had no upper bound.

Model (`MSt`, `MOp`, `step`). Parameters: the budget G, the skew bound σ, and the design flag `aware` (margin σ).
- **Clocks.**
  - True time `now` advances by `tick`.
  - The coordinator's clock `cclk` and each host's clock `hclk h` are STORED. They move only by `cset c` / `hset h c`.
  - `legal` requires each set to be monotone and within σ of true time, both ways.
  - A host acting (`spend`) must have its clock within σ of true time: it may lag by at most σ.
- **Network.** `net` is a list used as a multiset of messages: `poll i` (coordinator → host) and `settle i sp`
  (host → coordinator).
  - `deliver k` hands the k-th message to the coordinator and LEAVES it in the network, so messages may be duplicated.
  - Any index may be delivered, in any order and at any time, so messages may be reordered or delayed.
  - `drop k` loses a message.
  - Nothing forges a message: only `poll` and `reply` add messages, and a reply carries the host's true durable
    counter.
- **Grants and spends.**
  - `grant host amt dur`: the coordinator grants `amt` until `cclk + dur` (on its own clock), only if the accounted
    total stays ≤ G.
  - `spend i x`: grant i's host spends x, only if the host is UP, `hclk + margin < exp` on its own clock, and
    spent + x ≤ amt.
- **Settlement.**
  - `poll i`: once `exp + margin ≤ cclk`, the coordinator asks the host for its final count.
  - `reply i`: an UP host that has a poll for i sends `settle i spent`, its durable counter. A crashed host sends
    nothing.
  - `deliver k` of `settle i sp`: the coordinator settles grant i at sp. This is ONLY from a received message.
    A grant settled conservatively is re-settled down.
  - `close i`: without any message, once `exp + margin ≤ cclk`, the coordinator settles CONSERVATIVELY at the full
    allocation. That returns nothing.
- **Crashes.** `crash h` makes host h unreachable: it neither spends nor replies until `restart h`. The spend
  counter is durable, preserved across crash and restart (an anti-rollback premise: `Core/AntiRollback.lean`).

Results (adversary class TRACE_ARBITRARY over legal traces: any interleaving of ticks, clock updates, grants, spends,
polls, replies, deliveries of any message any number of times, drops, closes, crashes and restarts):
- (1) `escrow_safe`: with `aware`, total spend across hosts ≤ G.
  The core of the argument: a settle message exists only after true time passed the grant's expiry. That holds
  because a poll needs `exp + σ ≤ cclk ≤ now + σ`. After that, a legal spend on the grant needs
  `now ≤ hclk + σ < exp`, which is impossible. So every settle message carries the FINAL count, however late,
  duplicated or reordered its delivery.
- (2) `skew_unaware_overspends`: without the σ margins, a coordinator polling at `cclk = exp` gets a reply from a host
  whose clock lags by σ = 2. The reply is a stale count (0). The coordinator re-grants the escrow, and the host then
  spends: total 20 > G = 10. The aware design refuses.
- (3) Liveness, trace-level:
  - `deliver_returns`: delivering a settle message for i settles i at its spend, so the unused escrow returns;
  - `settled_stable`: that settlement survives every later legal step;
  - `escrow_returns` (FAIRNESS PREMISE: the trace delivers some settle message for i): at the end of every legal
    trace, grant i is settled at exactly its spend;
  - `settle_enabled`: after expiry (`exp + σ ≤ cclk`), with the host UP, [poll, reply, deliver] is legal and settles
    the grant at its spend. So a settle message for i exists to be delivered.
- (4) `crash_holds_escrow`: a crashed host's escrow is closed only conservatively, and a new grant is refused. After
  `restart` the host replies, and the delivery returns the unused escrow, so the new grant is accepted.

Limits:
- Time is discrete.
- σ (clock measurement) and the durable counter (anti-rollback) are premises.
- Message authenticity is the no-forgery premise. With an adversarial network it needs a MAC
  (`Core/Authenticated.lean`).
- Delivery is a fairness premise, not proved.
- Effects in flight to an external sink after expiry need the sink's own fencing (`DistributedHalt`).
Escrow with polled settlement is classical; no novelty is claimed.
-/
import Mathlib.Tactic

namespace ControlStack.EscrowBudgetMsg

open Finset

/-- one grant: host, allocation, expiry (on the coordinator's clock), durable local spend, settled flag, amount -/
structure GS where
  host : ℕ
  amt : ℕ
  exp : ℕ
  spent : ℕ
  settled : Bool
  final : ℕ
deriving DecidableEq

inductive Msg where
  | poll (i : ℕ)
  | settle (i sp : ℕ)
deriving DecidableEq

structure MSt where
  now : ℕ
  cclk : ℕ
  hclk : ℕ → ℕ
  up : ℕ → Bool
  n : ℕ
  g : ℕ → GS
  net : List Msg

inductive MOp where
  | tick
  | cset (c : ℕ)
  | hset (h c : ℕ)
  | grant (host amt dur : ℕ)
  | spend (i x : ℕ)
  | poll (i : ℕ)
  | reply (i : ℕ)
  | deliver (k : ℕ)
  | drop (k : ℕ)
  | close (i : ℕ)
  | crash (h : ℕ)
  | restart (h : ℕ)

structure Cfg where
  G : ℕ
  σ : ℕ
  aware : Bool

def init : MSt := ⟨0, 0, fun _ => 0, fun _ => true, 0, fun _ => ⟨0, 0, 0, 0, false, 0⟩, []⟩

/-- the coordinator's accounted total: outstanding allocations plus settled amounts -/
def acc (s : MSt) : ℕ := ∑ i ∈ range s.n, (if (s.g i).settled then (s.g i).final else (s.g i).amt)

/-- the total (durable) spend across all hosts -/
def total (s : MSt) : ℕ := ∑ i ∈ range s.n, (s.g i).spent

def margin (C : Cfg) : ℕ := if C.aware then C.σ else 0

def upd (s : MSt) (i : ℕ) (v : GS) : MSt := { s with g := Function.update s.g i v }

def add (s : MSt) (v : GS) : MSt := { s with n := s.n + 1, g := Function.update s.g s.n v }

@[simp] theorem upd_n (s : MSt) (i : ℕ) (v : GS) : (upd s i v).n = s.n := rfl
@[simp] theorem upd_now (s : MSt) (i : ℕ) (v : GS) : (upd s i v).now = s.now := rfl
@[simp] theorem upd_net (s : MSt) (i : ℕ) (v : GS) : (upd s i v).net = s.net := rfl
@[simp] theorem upd_cclk (s : MSt) (i : ℕ) (v : GS) : (upd s i v).cclk = s.cclk := rfl
@[simp] theorem upd_hclk (s : MSt) (i : ℕ) (v : GS) : (upd s i v).hclk = s.hclk := rfl
theorem upd_self (s : MSt) (i : ℕ) (v : GS) : (upd s i v).g i = v := by simp [upd]
theorem upd_ne (s : MSt) (i j : ℕ) (v : GS) (h : j ≠ i) : (upd s i v).g j = s.g j := by simp [upd, h]

/-- grant `v` with x more spent -/
def addSpent (v : GS) (x : ℕ) : GS := ⟨v.host, v.amt, v.exp, v.spent + x, v.settled, v.final⟩

/-- grant `v` settled at `f` -/
def settleAt (v : GS) (f : ℕ) : GS := ⟨v.host, v.amt, v.exp, v.spent, true, f⟩

@[simp] theorem addSpent_amt (v : GS) (x : ℕ) : (addSpent v x).amt = v.amt := rfl
@[simp] theorem addSpent_exp (v : GS) (x : ℕ) : (addSpent v x).exp = v.exp := rfl
@[simp] theorem addSpent_spent (v : GS) (x : ℕ) : (addSpent v x).spent = v.spent + x := rfl
@[simp] theorem addSpent_settled (v : GS) (x : ℕ) : (addSpent v x).settled = v.settled := rfl
@[simp] theorem addSpent_final (v : GS) (x : ℕ) : (addSpent v x).final = v.final := rfl
@[simp] theorem settleAt_amt (v : GS) (f : ℕ) : (settleAt v f).amt = v.amt := rfl
@[simp] theorem settleAt_exp (v : GS) (f : ℕ) : (settleAt v f).exp = v.exp := rfl
@[simp] theorem settleAt_spent (v : GS) (f : ℕ) : (settleAt v f).spent = v.spent := rfl
@[simp] theorem settleAt_settled (v : GS) (f : ℕ) : (settleAt v f).settled = true := rfl
@[simp] theorem settleAt_final (v : GS) (f : ℕ) : (settleAt v f).final = f := rfl

/-- the k-th message, if it is a settle message -/
def settleOf (s : MSt) (k : ℕ) : Option (ℕ × ℕ) :=
  match s.net[k]? with
  | some (.settle i sp) => some (i, sp)
  | _ => none

theorem settleOf_mem {s : MSt} {k i sp : ℕ} (h : settleOf s k = some (i, sp)) : Msg.settle i sp ∈ s.net := by
  unfold settleOf at h
  cases hk : s.net[k]? with
  | none => rw [hk] at h; exact absurd h (by simp)
  | some m =>
    rw [hk] at h
    cases m with
    | poll _ => exact absurd h (by simp)
    | settle i' sp' =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact List.mem_of_getElem? hk

def step (C : Cfg) (s : MSt) : MOp → MSt
  | .tick => { s with now := s.now + 1 }
  | .cset c => { s with cclk := c }
  | .hset h c => { s with hclk := Function.update s.hclk h c }
  | .grant host a dur => if acc s + a ≤ C.G then add s ⟨host, a, s.cclk + dur, 0, false, 0⟩ else s
  | .spend i x =>
    if i < s.n ∧ s.up (s.g i).host = true ∧ s.hclk (s.g i).host + margin C < (s.g i).exp ∧
        (s.g i).spent + x ≤ (s.g i).amt then
      upd s i (addSpent (s.g i) x)
    else s
  | .poll i => if i < s.n ∧ (s.g i).exp + margin C ≤ s.cclk then { s with net := s.net ++ [.poll i] } else s
  | .reply i =>
    if i < s.n ∧ s.up (s.g i).host = true ∧ Msg.poll i ∈ s.net then
      { s with net := s.net ++ [.settle i (s.g i).spent] }
    else s
  | .deliver k =>
    match settleOf s k with
    | some (i, sp) => if i < s.n then upd s i (settleAt (s.g i) sp) else s
    | none => s
  | .drop k => { s with net := s.net.eraseIdx k }
  | .close i =>
    if i < s.n ∧ (s.g i).settled = false ∧ (s.g i).exp + margin C ≤ s.cclk then
      upd s i (settleAt (s.g i) (s.g i).amt)
    else s
  | .crash h => { s with up := Function.update s.up h false }
  | .restart h => { s with up := Function.update s.up h true }

def run (C : Cfg) (s : MSt) (ops : List MOp) : MSt := ops.foldl (step C) s

theorem run_cons (C : Cfg) (s : MSt) (o : MOp) (ops : List MOp) : run C s (o :: ops) = run C (step C s o) ops := rfl

theorem run_append (C : Cfg) (s : MSt) (a b : List MOp) : run C s (a ++ b) = run C (run C s a) b := by
  simp [run, List.foldl_append]

/-- clocks: monotone, and within σ of true time when set; a host's clock is within σ of true time when it spends -/
def legal (C : Cfg) (s : MSt) : MOp → Prop
  | .cset c => s.cclk ≤ c ∧ c ≤ s.now + C.σ ∧ s.now ≤ c + C.σ
  | .hset h c => s.hclk h ≤ c ∧ c ≤ s.now + C.σ ∧ s.now ≤ c + C.σ
  | .spend i _ => s.now ≤ s.hclk (s.g i).host + C.σ
  | _ => True

def legalB (C : Cfg) (s : MSt) : MOp → Bool
  | .cset c => decide (s.cclk ≤ c ∧ c ≤ s.now + C.σ ∧ s.now ≤ c + C.σ)
  | .hset h c => decide (s.hclk h ≤ c ∧ c ≤ s.now + C.σ ∧ s.now ≤ c + C.σ)
  | .spend i _ => decide (s.now ≤ s.hclk (s.g i).host + C.σ)
  | _ => true

def LegalTrace (C : Cfg) : MSt → List MOp → Prop
  | _, [] => True
  | s, o :: ops => legal C s o ∧ LegalTrace C (step C s o) ops

def legalTraceB (C : Cfg) : MSt → List MOp → Bool
  | _, [] => true
  | s, o :: ops => legalB C s o && legalTraceB C (step C s o) ops

theorem legalTrace_of_B (C : Cfg) : ∀ (ops : List MOp) (s : MSt), legalTraceB C s ops = true →
    LegalTrace C s ops := by
  intro ops
  induction ops with
  | nil => intro _ _; trivial
  | cons o ops ih =>
    intro s h
    simp only [legalTraceB, Bool.and_eq_true] at h
    refine ⟨?_, ih _ h.2⟩
    have h1 := h.1
    cases o <;> simp_all [legalB, legal]

theorem legalTrace_append (C : Cfg) (s : MSt) (a b : List MOp) :
    LegalTrace C s (a ++ b) ↔ LegalTrace C s a ∧ LegalTrace C (run C s a) b := by
  induction a generalizing s with
  | nil => simp [LegalTrace, run]
  | cons o a ih =>
    simp only [List.cons_append, LegalTrace, ih, run_cons]
    exact and_assoc.symm

/-! ## (1) Safety -/

/-- a message is consistent with the state: polls and settle messages exist only after true time passed expiry;
a settle message carries the grant's durable spend -/
def MsgOk (s : MSt) : Msg → Prop
  | .poll i => i < s.n ∧ (s.g i).exp ≤ s.now
  | .settle i sp => i < s.n ∧ sp = (s.g i).spent ∧ (s.g i).exp ≤ s.now

structure Inv (C : Cfg) (s : MSt) : Prop where
  within : ∀ i < s.n, (s.g i).spent ≤ (s.g i).amt
  settled_ok : ∀ i < s.n, (s.g i).settled = true →
    (s.g i).spent ≤ (s.g i).final ∧ (s.g i).final ≤ (s.g i).amt ∧ (s.g i).exp ≤ s.now
  msgs : ∀ m ∈ s.net, MsgOk s m
  cclk_le : s.cclk ≤ s.now + C.σ
  hclk_le : ∀ h, s.hclk h ≤ s.now + C.σ
  cap : acc s ≤ C.G

theorem inv_init (C : Cfg) : Inv C init :=
  ⟨by simp [init], by simp [init], by simp [init], by simp [init], by simp [init], by simp [acc, init]⟩

theorem total_le_acc (C : Cfg) (s : MSt) (h : Inv C s) : total s ≤ acc s := by
  unfold total acc
  apply Finset.sum_le_sum; intro i hi
  rw [mem_range] at hi
  split_ifs with hs
  · exact (h.settled_ok i hi hs).1
  · exact h.within i hi

theorem acc_upd (s : MSt) (i : ℕ) (v : GS) (hi : i < s.n) :
    acc (upd s i v) + (if (s.g i).settled then (s.g i).final else (s.g i).amt) =
      acc s + (if v.settled then v.final else v.amt) := by
  unfold acc
  simp only [upd_n]
  rw [← Finset.add_sum_erase _ _ (mem_range.2 hi), ← Finset.add_sum_erase (range s.n) _ (mem_range.2 hi)]
  have e : ∑ j ∈ (range s.n).erase i,
      (if ((upd s i v).g j).settled then ((upd s i v).g j).final else ((upd s i v).g j).amt) =
      ∑ j ∈ (range s.n).erase i, (if (s.g j).settled then (s.g j).final else (s.g j).amt) := by
    apply Finset.sum_congr rfl; intro j hj
    rw [upd_ne s i j v (Finset.ne_of_mem_erase hj)]
  rw [e, upd_self]
  omega

theorem acc_upd_le (s : MSt) (i : ℕ) (v : GS) (hi : i < s.n)
    (hle : (if v.settled then v.final else v.amt) ≤ (if (s.g i).settled then (s.g i).final else (s.g i).amt)) :
    acc (upd s i v) ≤ acc s := by
  have := acc_upd s i v hi
  omega

/-- messages stay consistent when grant i is replaced by one with the same spend and expiry -/
theorem msgs_upd (s : MSt) (i : ℕ) (v : GS) (hm : ∀ m ∈ s.net, MsgOk s m) (hsp : v.spent = (s.g i).spent)
    (hex : v.exp = (s.g i).exp) : ∀ m ∈ (upd s i v).net, MsgOk (upd s i v) m := by
  intro m hmem
  have h0 := hm m hmem
  cases m with
  | poll j =>
    refine ⟨h0.1, ?_⟩
    by_cases hj : j = i
    · subst hj; rw [upd_self, hex]; exact h0.2
    · rw [upd_ne s i j v hj]; exact h0.2
  | settle j sp =>
    refine ⟨h0.1, ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj; rw [upd_self, hsp]; exact h0.2.1
      · rw [upd_ne s i j v hj]; exact h0.2.1
    · by_cases hj : j = i
      · subst hj; rw [upd_self, hex]; exact h0.2.2
      · rw [upd_ne s i j v hj]; exact h0.2.2

theorem settled_ok_upd (s : MSt) (i : ℕ) (v : GS) (h : ∀ j < s.n, (s.g j).settled = true →
    (s.g j).spent ≤ (s.g j).final ∧ (s.g j).final ≤ (s.g j).amt ∧ (s.g j).exp ≤ s.now)
    (hv : v.settled = true → v.spent ≤ v.final ∧ v.final ≤ v.amt ∧ v.exp ≤ s.now) :
    ∀ j < (upd s i v).n, ((upd s i v).g j).settled = true →
      ((upd s i v).g j).spent ≤ ((upd s i v).g j).final ∧ ((upd s i v).g j).final ≤ ((upd s i v).g j).amt ∧
        ((upd s i v).g j).exp ≤ (upd s i v).now := by
  intro j hj hs
  rw [upd_n] at hj
  by_cases hji : j = i
  · subst hji; rw [upd_self] at hs ⊢; exact hv hs
  · rw [upd_ne s i j v hji] at hs ⊢; exact h j hj hs

theorem within_upd (s : MSt) (i : ℕ) (v : GS) (h : ∀ j < s.n, (s.g j).spent ≤ (s.g j).amt)
    (hv : v.spent ≤ v.amt) : ∀ j < (upd s i v).n, ((upd s i v).g j).spent ≤ ((upd s i v).g j).amt := by
  intro j hj
  rw [upd_n] at hj
  by_cases hji : j = i
  · subst hji; rw [upd_self]; exact hv
  · rw [upd_ne s i j v hji]; exact h j hj

theorem step_inv (C : Cfg) (hC : C.aware = true) (s : MSt) (o : MOp) (ho : legal C s o) (h : Inv C s) :
    Inv C (step C s o) := by
  have hm : margin C = C.σ := by simp [margin, hC]
  cases o with
  | tick =>
    refine ⟨h.within, fun i hi hs => ?_, fun m hmem => ?_, ?_, fun x => ?_, h.cap⟩
    · obtain ⟨a, b, c⟩ := h.settled_ok i hi hs
      exact ⟨a, b, by show (s.g i).exp ≤ s.now + 1; omega⟩
    · have := h.msgs m hmem
      cases m with
      | poll j => exact ⟨this.1, by have := this.2; show (s.g j).exp ≤ s.now + 1; omega⟩
      | settle j sp => exact ⟨this.1, this.2.1, by have := this.2.2; show (s.g j).exp ≤ s.now + 1; omega⟩
    · show s.cclk ≤ s.now + 1 + C.σ; have := h.cclk_le; omega
    · show s.hclk x ≤ s.now + 1 + C.σ; have := h.hclk_le x; omega
  | cset c =>
    simp only [legal] at ho
    exact ⟨h.within, h.settled_ok, h.msgs, ho.2.1, h.hclk_le, h.cap⟩
  | hset hh c =>
    simp only [legal] at ho
    refine ⟨h.within, h.settled_ok, h.msgs, h.cclk_le, fun x => ?_, h.cap⟩
    show Function.update s.hclk hh c x ≤ s.now + C.σ
    by_cases hx : x = hh
    · subst hx; simp only [Function.update_self]; exact ho.2.1
    · rw [Function.update_of_ne hx]; exact h.hclk_le x
  | grant host a dur =>
    simp only [step]
    split_ifs with hg
    · have hold : ∀ j < s.n, (add s ⟨host, a, s.cclk + dur, 0, false, 0⟩).g j = s.g j := fun j hj => by
        simp [add, Function.update_of_ne (show j ≠ s.n by omega)]
      have hnew : (add s ⟨host, a, s.cclk + dur, 0, false, 0⟩).g s.n = ⟨host, a, s.cclk + dur, 0, false, 0⟩ := by
        simp [add]
      refine ⟨fun i hi => ?_, fun i hi hs => ?_, fun m hmem => ?_, h.cclk_le, h.hclk_le, ?_⟩
      · change i < s.n + 1 at hi
        rcases Nat.lt_or_ge i s.n with h' | h'
        · rw [hold i h']; exact h.within i h'
        · rw [show i = s.n by omega, hnew]; simp
      · change i < s.n + 1 at hi
        rcases Nat.lt_or_ge i s.n with h' | h'
        · rw [hold i h'] at hs ⊢; exact h.settled_ok i h' hs
        · rw [show i = s.n by omega, hnew] at hs; simp at hs
      · have := h.msgs m hmem
        cases m with
        | poll j =>
          refine ⟨Nat.lt_succ_of_lt this.1, ?_⟩
          show ((add s _).g j).exp ≤ s.now
          rw [hold j this.1]; exact this.2
        | settle j sp =>
          refine ⟨Nat.lt_succ_of_lt this.1, ?_, ?_⟩
          · show sp = ((add s _).g j).spent
            rw [hold j this.1]; exact this.2.1
          · show ((add s _).g j).exp ≤ s.now
            rw [hold j this.1]; exact this.2.2
      · unfold acc
        change ∑ i ∈ range (s.n + 1), _ ≤ C.G
        rw [Finset.sum_range_succ, hnew]
        have e : ∑ i ∈ range s.n, (if ((add s ⟨host, a, s.cclk + dur, 0, false, 0⟩).g i).settled
            then ((add s ⟨host, a, s.cclk + dur, 0, false, 0⟩).g i).final
            else ((add s ⟨host, a, s.cclk + dur, 0, false, 0⟩).g i).amt) = acc s := by
          unfold acc
          apply Finset.sum_congr rfl; intro i hi
          rw [hold i (mem_range.1 hi)]
        rw [e]; simpa using hg
    · exact h
  | spend i x =>
    simp only [legal] at ho
    simp only [step]
    split_ifs with hsp
    · obtain ⟨hi, _, hexp, hamt⟩ := hsp
      rw [hm] at hexp
      -- the spend happens strictly before expiry in true time
      have hlt : s.now < (s.g i).exp := by omega
      have hns : (s.g i).settled = false := by
        by_contra hc'
        have := (h.settled_ok i hi (by simpa using hc')).2.2
        omega
      refine ⟨within_upd s i _ h.within hamt, settled_ok_upd s i _ h.settled_ok (fun hs => by simp [hns] at hs),
        fun m hmem => ?_, h.cclk_le, h.hclk_le,
        (acc_upd_le s i (addSpent (s.g i) x) hi (by simp [hns])).trans h.cap⟩
      have h0 := h.msgs m hmem
      cases m with
      | poll j =>
        have hji : j ≠ i := fun hji => by subst hji; have := h0.2; omega
        refine ⟨h0.1, ?_⟩
        simp only [upd_now]; rw [upd_ne s i j _ hji]; exact h0.2
      | settle j sp =>
        have hji : j ≠ i := fun hji => by subst hji; have := h0.2.2; omega
        refine ⟨h0.1, ?_, ?_⟩
        · rw [upd_ne s i j _ hji]; exact h0.2.1
        · simp only [upd_now]; rw [upd_ne s i j _ hji]; exact h0.2.2
    · exact h
  | poll i =>
    simp only [step]
    split_ifs with hp
    · obtain ⟨hi, hexp⟩ := hp
      rw [hm] at hexp
      refine ⟨h.within, h.settled_ok, fun m hmem => ?_, h.cclk_le, h.hclk_le, h.cap⟩
      rcases List.mem_append.1 hmem with hmem | hmem
      · exact h.msgs m hmem
      · simp only [List.mem_singleton] at hmem; subst hmem
        exact ⟨hi, by have := h.cclk_le; show (s.g i).exp ≤ s.now; omega⟩
    · exact h
  | reply i =>
    simp only [step]
    split_ifs with hp
    · obtain ⟨hi, _, hpoll⟩ := hp
      refine ⟨h.within, h.settled_ok, fun m hmem => ?_, h.cclk_le, h.hclk_le, h.cap⟩
      rcases List.mem_append.1 hmem with hmem | hmem
      · exact h.msgs m hmem
      · simp only [List.mem_singleton] at hmem; subst hmem
        exact ⟨hi, rfl, (h.msgs _ hpoll).2⟩
    · exact h
  | deliver k =>
    simp only [step]
    cases hk : settleOf s k with
    | none => exact h
    | some p =>
      obtain ⟨i, sp⟩ := p
      dsimp only
      split_ifs with hi
      · obtain ⟨_, hsp, hexp⟩ := h.msgs _ (settleOf_mem hk)
        refine ⟨within_upd s i _ h.within (h.within i hi),
          settled_ok_upd s i _ h.settled_ok (fun _ => ⟨by simp [hsp], by simp [hsp, h.within i hi], hexp⟩),
          msgs_upd s i _ h.msgs rfl rfl, h.cclk_le, h.hclk_le, ?_⟩
        refine (acc_upd_le s i _ hi ?_).trans h.cap
        simp only [settleAt_settled, settleAt_final, ↓reduceIte]
        split_ifs with hs
        · rw [hsp]; exact (h.settled_ok i hi hs).1
        · rw [hsp]; exact h.within i hi
      · exact h
  | drop k =>
    refine ⟨h.within, h.settled_ok, fun m hmem => h.msgs m (List.mem_of_mem_eraseIdx hmem), h.cclk_le, h.hclk_le,
      h.cap⟩
  | close i =>
    simp only [step]
    split_ifs with hc
    · obtain ⟨hi, hns, hexp⟩ := hc
      rw [hm] at hexp
      have hnow : (s.g i).exp ≤ s.now := by have := h.cclk_le; omega
      refine ⟨within_upd s i _ h.within (h.within i hi),
        settled_ok_upd s i _ h.settled_ok (fun _ => ⟨h.within i hi, le_rfl, hnow⟩),
        msgs_upd s i _ h.msgs rfl rfl, h.cclk_le, h.hclk_le, ?_⟩
      refine (acc_upd_le s i _ hi ?_).trans h.cap
      simp [hns]
    · exact h
  | crash hh => exact ⟨h.within, h.settled_ok, h.msgs, h.cclk_le, h.hclk_le, h.cap⟩
  | restart hh => exact ⟨h.within, h.settled_ok, h.msgs, h.cclk_le, h.hclk_le, h.cap⟩

theorem run_inv (C : Cfg) (hC : C.aware = true) (s : MSt) (ops : List MOp) (hl : LegalTrace C s ops)
    (h : Inv C s) : Inv C (run C s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => exact ih _ hl.2 (step_inv C hC s o hl.1 h)

/-- **(1) Escrow safety with message-passing settlement.** With skew-aware margins, for every legal interleaving
(any delays, duplications, reorderings and losses of messages; crashes and restarts; monotone clocks within σ), the
total spend across all hosts is ≤ G. -/
theorem escrow_safe (C : Cfg) (hC : C.aware = true) (ops : List MOp) (hl : LegalTrace C init ops) :
    total (run C init ops) ≤ C.G :=
  let h := run_inv C hC init ops hl (inv_init C)
  (total_le_acc C _ h).trans h.cap

/-! ## (3) Liveness -/

/-- **Delivery returns the unused escrow.** Delivering a settle message for grant i settles it at exactly its spend.
The accounted total drops by (previous accounted amount − spend): amt − spent if it was outstanding. -/
theorem deliver_returns (C : Cfg) (s : MSt) (h : Inv C s) (k i sp : ℕ) (hk : settleOf s k = some (i, sp)) :
    ((step C s (.deliver k)).g i).settled = true ∧
      ((step C s (.deliver k)).g i).final = ((step C s (.deliver k)).g i).spent ∧
      acc (step C s (.deliver k)) + ((if (s.g i).settled then (s.g i).final else (s.g i).amt) - (s.g i).spent) =
        acc s := by
  obtain ⟨hi, hsp, _⟩ := h.msgs _ (settleOf_mem hk)
  have hstep : step C s (.deliver k) = upd s i (settleAt (s.g i) sp) := by
    simp only [step, hk, hi, ↓reduceIte]
  rw [hstep, upd_self]
  refine ⟨rfl, hsp, ?_⟩
  have e := acc_upd s i (settleAt (s.g i) sp) hi
  simp only [settleAt_settled, settleAt_final, ↓reduceIte] at e
  have hle : (s.g i).spent ≤ (if (s.g i).settled then (s.g i).final else (s.g i).amt) := by
    split_ifs with hs
    · exact (h.settled_ok i hi hs).1
    · exact h.within i hi
  omega

/-- **Exact settlement is stable.** Once grant i is settled at exactly its spend, every later legal step keeps it so:
late or duplicated settle messages carry the same count, `close` needs an unsettled grant, and no legal spend on an
expired grant is possible. -/
theorem settled_stable (C : Cfg) (hC : C.aware = true) (s : MSt) (h : Inv C s) (i : ℕ) (hi : i < s.n)
    (hs : (s.g i).settled = true) (hf : (s.g i).final = (s.g i).spent) (o : MOp) (ho : legal C s o) :
    ((step C s o).g i).settled = true ∧ ((step C s o).g i).final = ((step C s o).g i).spent := by
  have hm : margin C = C.σ := by simp [margin, hC]
  have hexp := (h.settled_ok i hi hs).2.2
  cases o with
  | grant host a dur =>
    simp only [step]; split_ifs
    · have : (add s ⟨host, a, s.cclk + dur, 0, false, 0⟩).g i = s.g i := by
        simp [add, Function.update_of_ne (show i ≠ s.n by omega)]
      rw [this]; exact ⟨hs, hf⟩
    · exact ⟨hs, hf⟩
  | spend j x =>
    simp only [legal] at ho
    simp only [step]; split_ifs with hsp
    · by_cases hji : i = j
      · subst hji; rw [hm] at hsp; omega
      · rw [upd_ne s j i _ hji]; exact ⟨hs, hf⟩
    · exact ⟨hs, hf⟩
  | deliver k =>
    simp only [step]
    cases hk : settleOf s k with
    | none => exact ⟨hs, hf⟩
    | some p =>
      obtain ⟨j, sp⟩ := p
      dsimp only
      split_ifs with hj
      · by_cases hji : i = j
        · subst hji
          obtain ⟨_, hsp, _⟩ := h.msgs _ (settleOf_mem hk)
          rw [upd_self]; exact ⟨rfl, hsp⟩
        · rw [upd_ne s j i _ hji]; exact ⟨hs, hf⟩
      · exact ⟨hs, hf⟩
  | close j =>
    simp only [step]; split_ifs with hc
    · by_cases hji : i = j
      · subst hji; rw [hs] at hc; exact absurd hc.2.1 (by decide)
      · rw [upd_ne s j i _ hji]; exact ⟨hs, hf⟩
    · exact ⟨hs, hf⟩
  | tick => exact ⟨hs, hf⟩
  | cset c => exact ⟨hs, hf⟩
  | hset hh c => exact ⟨hs, hf⟩
  | poll j => simp only [step]; split_ifs <;> exact ⟨hs, hf⟩
  | reply j => simp only [step]; split_ifs <;> exact ⟨hs, hf⟩
  | drop k => exact ⟨hs, hf⟩
  | crash hh => exact ⟨hs, hf⟩
  | restart hh => exact ⟨hs, hf⟩

theorem n_mono (C : Cfg) (s : MSt) (o : MOp) : s.n ≤ (step C s o).n := by
  cases o with
  | grant host a dur => simp only [step]; split_ifs <;> simp [add]
  | spend i x => simp only [step]; split_ifs <;> simp
  | poll i => simp only [step]; split_ifs <;> simp
  | reply i => simp only [step]; split_ifs <;> simp
  | close i => simp only [step]; split_ifs <;> simp
  | deliver k =>
    simp only [step]
    cases settleOf s k with
    | none => exact le_rfl
    | some p => dsimp only; split_ifs <;> simp
  | tick => exact le_rfl
  | cset c => exact le_rfl
  | hset hh c => exact le_rfl
  | drop k => exact le_rfl
  | crash hh => exact le_rfl
  | restart hh => exact le_rfl

theorem settled_stable_run (C : Cfg) (hC : C.aware = true) (s : MSt) (ops : List MOp) (hl : LegalTrace C s ops)
    (h : Inv C s) (i : ℕ) (hi : i < s.n) (hs : (s.g i).settled = true) (hf : (s.g i).final = (s.g i).spent) :
    ((run C s ops).g i).settled = true ∧ ((run C s ops).g i).final = ((run C s ops).g i).spent := by
  induction ops generalizing s with
  | nil => exact ⟨hs, hf⟩
  | cons o ops ih =>
    obtain ⟨hs', hf'⟩ := settled_stable C hC s h i hi hs hf o hl.1
    exact ih _ hl.2 (step_inv C hC s o hl.1 h) (lt_of_lt_of_le hi (n_mono C s o)) hs' hf'

/-- **Unused escrow returns, trace-level.** FAIRNESS PREMISE: the legal trace delivers, at some point, a settle message
for grant i. Then at the end of the trace grant i is settled at exactly its spend: its unused escrow amt − spent is
back in the budget, however the rest of the trace (including later duplicates, reorderings, crashes) goes. -/
theorem escrow_returns (C : Cfg) (hC : C.aware = true) (pre post : List MOp) (k i sp : ℕ)
    (hl : LegalTrace C init (pre ++ .deliver k :: post)) (hdel : settleOf (run C init pre) k = some (i, sp)) :
    ((run C init (pre ++ .deliver k :: post)).g i).settled = true ∧
      ((run C init (pre ++ .deliver k :: post)).g i).final = ((run C init (pre ++ .deliver k :: post)).g i).spent := by
  rw [legalTrace_append] at hl
  have h0 := run_inv C hC init pre hl.1 (inv_init C)
  set s := run C init pre
  have hi : i < s.n := (h0.msgs _ (settleOf_mem hdel)).1
  obtain ⟨hs, hf, _⟩ := deliver_returns C s h0 k i sp hdel
  have h1 := step_inv C hC s (.deliver k) hl.2.1 h0
  rw [run_append, run_cons]
  exact settled_stable_run C hC _ post hl.2.2 h1 i (lt_of_lt_of_le hi (n_mono C s _)) hs hf

/-- **A settle message becomes available after expiry.** With the coordinator's clock past exp + σ and the host UP,
[poll i, reply i, deliver k] (k the reply's index) is legal and settles grant i at exactly its spend. -/
theorem settle_enabled (C : Cfg) (hC : C.aware = true) (s : MSt) (i : ℕ) (hi : i < s.n)
    (hup : s.up (s.g i).host = true) (hexp : (s.g i).exp + C.σ ≤ s.cclk) :
    LegalTrace C s [.poll i, .reply i, .deliver (s.net.length + 1)] ∧
      ((run C s [.poll i, .reply i, .deliver (s.net.length + 1)]).g i).settled = true ∧
      ((run C s [.poll i, .reply i, .deliver (s.net.length + 1)]).g i).final = (s.g i).spent := by
  have hm : margin C = C.σ := by simp [margin, hC]
  have h1 : step C s (.poll i) = { s with net := s.net ++ [Msg.poll i] } := by
    simp only [step]; rw [ite_eq_left ⟨hi, by rw [hm]; exact hexp⟩]
  have h2 : step C { s with net := s.net ++ [Msg.poll i] } (.reply i) =
      { s with net := s.net ++ [Msg.poll i] ++ [Msg.settle i (s.g i).spent] } := by
    simp only [step]; rw [ite_eq_left ⟨hi, hup, by simp⟩]
  have hk : settleOf { s with net := s.net ++ [Msg.poll i] ++ [Msg.settle i (s.g i).spent] } (s.net.length + 1) =
      some (i, (s.g i).spent) := by
    simp [settleOf]
  have h3 : step C { s with net := s.net ++ [Msg.poll i] ++ [Msg.settle i (s.g i).spent] } (.deliver (s.net.length + 1))
      = upd { s with net := s.net ++ [Msg.poll i] ++ [Msg.settle i (s.g i).spent] } i (settleAt (s.g i) (s.g i).spent) := by
    simp only [step, hk]; rw [ite_eq_left (show i < s.n from hi)]
  refine ⟨⟨trivial, trivial, trivial, trivial⟩, ?_⟩
  rw [show run C s [.poll i, .reply i, .deliver (s.net.length + 1)] =
    step C (step C (step C s (.poll i)) (.reply i)) (.deliver (s.net.length + 1)) from rfl, h1, h2, h3, upd_self]
  exact ⟨rfl, rfl⟩

/-! ## Witnesses -/

/-- G = 10, σ = 2 -/
def C10 (aware : Bool) : Cfg := ⟨10, 2, aware⟩

/-- host 0 gets 10 until coordinator time 5. At true time 5 the coordinator (clock 5) polls; host 0's clock reads 3
(2 behind, legal) and it replies with its count 0; the coordinator settles at 0 and grants host 1 the escrow;
host 1 spends 10; then host 0, whose clock still reads 3 < 5, spends its 10. -/
def skewTrace : List MOp :=
  [.grant 0 10 5, .tick, .tick, .tick, .tick, .tick, .cset 5, .hset 0 3, .poll 0, .reply 0, .deliver 1,
   .grant 1 10 100, .hset 1 5, .spend 1 10, .spend 0 10]

theorem skewTrace_legal (aware : Bool) : LegalTrace (C10 aware) init skewTrace := by
  cases aware <;> exact legalTrace_of_B _ _ _ (by decide)

/-- **(2) Skew-unaware polling double-allocates.** Without the σ margins the legal trace spends 20 > G = 10: the
poll at coordinator time exp reaches a host whose clock lags, so the reply is not final. With the margins the poll
is refused until exp + σ and the trace spends ≤ 10. -/
theorem skew_unaware_overspends :
    total (run (C10 false) init skewTrace) = 20 ∧ total (run (C10 true) init skewTrace) ≤ 10 :=
  ⟨by decide, escrow_safe _ rfl _ (skewTrace_legal true)⟩

/-- host 0 takes the whole budget, spends 3, crashes; after expiry the coordinator polls and closes conservatively;
host 1's grant is refused. Host 0 restarts, replies, the reply is delivered, and host 1's grant of 7 is accepted. -/
def crashPre : List MOp :=
  [.grant 0 10 5, .spend 0 3, .crash 0, .tick, .tick, .tick, .tick, .tick, .tick, .tick, .cset 7, .poll 0, .reply 0,
   .close 0, .grant 1 7 50]

def crashPost : List MOp := [.restart 0, .reply 0, .deliver 1, .grant 1 7 50]

/-- **(4) A crashed host holds its escrow until it answers.** While host 0 is down it does not reply (the network
holds only the poll), the coordinator's conservative close returns nothing, and host 1's grant is refused (still one
grant). After restart and delivery of its reply, the unused 7 returns and host 1 is granted. -/
theorem crash_holds_escrow :
    (run (C10 true) init crashPre).net.length = 1 ∧ (run (C10 true) init crashPre).n = 1 ∧
      (run (C10 true) init (crashPre ++ crashPost)).n = 2 ∧
      LegalTrace (C10 true) init (crashPre ++ crashPost) := by
  refine ⟨by decide, by decide, by decide, legalTrace_of_B _ _ _ (by decide)⟩

end ControlStack.EscrowBudgetMsg

#print axioms ControlStack.EscrowBudgetMsg.escrow_safe
#print axioms ControlStack.EscrowBudgetMsg.deliver_returns
#print axioms ControlStack.EscrowBudgetMsg.settled_stable
#print axioms ControlStack.EscrowBudgetMsg.escrow_returns
#print axioms ControlStack.EscrowBudgetMsg.settle_enabled
#print axioms ControlStack.EscrowBudgetMsg.skew_unaware_overspends
#print axioms ControlStack.EscrowBudgetMsg.crash_holds_escrow
