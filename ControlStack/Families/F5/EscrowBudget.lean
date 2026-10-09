/-
F5 at datacenter scale: a global budget G across n hosts WITHOUT a central counter on every step (escrow / leases
with expiry, clock skew, partitions, crashes).

`SC28Budget` (one meter consulted on every work step) and `LabStack` (one shared counter in the joint gate) assume
every spend reaches the counter. Across a datacenter that is not possible: hosts are partitioned, latency is high.
The classical answer is ESCROW. A coordinator grants host i an allocation a_i with
Σ (outstanding allocations) + Σ (settled spend) ≤ G. Hosts spend LOCALLY within their allocation until it expires.
Unused escrow returns only after expiry, when the coordinator settles the grant.

Model (`ESt`, `EOp`, `step`), parameters: the budget G, a clock-skew bound σ, and two design flags:
- `aware` (account for skew): a host stops spending once its own clock reads exp − σ, and the coordinator settles
  only once its clock reads exp + σ;
- `expiry`: grants can be settled at all.
Operations:
- `grant host amt dur`: the coordinator grants `amt` until true time now + dur, only if the accounted total stays
  ≤ G;
- `spend i x h`: grant i's host spends x locally, its clock reading h. Accepted if h + σ < exp (when `aware`) and
  spent + x ≤ amt. The host does NOT know whether its grant was settled (it may be partitioned);
- `reclaim i c`: the coordinator settles grant i, its clock reading c, if c ≥ exp + σ (when `aware`). If the host
  is reachable, the settled amount is the host's spend. If the host is partitioned, it is conservatively the whole
  allocation;
- `reconcile i`: a settled grant whose host is reachable again is re-settled at its actual spend;
- `partition`, `heal`, `crash`: crashes change nothing durable. The host's spend counter is durable (an
  anti-rollback premise: `Core/AntiRollback.lean`);
- `tick`.
Premise `legal` (bounded skew): every host clock reading h satisfies now ≤ h + σ (it lags true time by at most σ),
and every coordinator reading c satisfies c ≤ now + σ (it leads by at most σ).

Results:
- (1) `escrow_safe` (adversary class TRACE_ARBITRARY over legal traces): for every interleaving of grants, spends,
  crashes, partitions, heals, ticks, settlements and reconciliations, the total spend across hosts is ≤ G.
- (2) `skew_unaware_overspends`: if the coordinator settles as soon as ITS clock reaches exp and the host stops only
  at exp on ITS clock, a slow host clock (σ = 2) spends after settlement. The escrow is double-allocated: total
  spend 20 > G = 10. The skew-aware design refuses.
- (3) `no_expiry_starves`: without expiry, a crashed host's escrow is never returned, and every later grant is
  refused (budget starvation, a liveness cost). Liveness with expiry:
  - `reclaim_frees`: once true time ≥ exp + 2σ, settling with a legal coordinator reading (|c − now| ≤ σ) succeeds,
    and if the host is reachable the unused escrow amt − spent returns at once;
  - `reconcile_frees`: a grant settled during a partition returns its unused escrow when the partition heals.
  So unused escrow returns within (lease duration) + 2σ + (delivery and partition bound).
- (4) `datacenter_example`: 1000 hosts with 1000 units each exactly fill G = 10⁶. With σ = 2 ticks and 60-tick
  leases, total spend ≤ 10⁶ on every legal trace, and unused escrow is settleable 64 ticks after the grant.

Limits:
- Time is discrete.
- The skew bound σ and durable host counters are premises (measurement and anti-rollback).
- A spend is an instantaneous local effect. Effects in flight to an external sink after expiry need the sink's
  own fencing (`DistributedHalt.fenced_after_eps`).
- The settlement message is assumed authentic (the coordinator learns the true spend).
- Escrow/lease budgeting is classical; no novelty is claimed.
-/
import Mathlib.Tactic

namespace ControlStack.EscrowBudget

open Finset

/-- one grant: host, allocation, expiry (true time), local spend, settled flag and settled amount -/
structure GS where
  host : ℕ
  amt : ℕ
  exp : ℕ
  spent : ℕ
  settled : Bool
  final : ℕ

structure ESt where
  now : ℕ
  n : ℕ
  g : ℕ → GS
  cut : List ℕ

inductive EOp where
  | tick
  | grant (host amt dur : ℕ)
  | spend (i x h : ℕ)
  | reclaim (i c : ℕ)
  | reconcile (i : ℕ)
  | partition (host : ℕ)
  | heal (host : ℕ)
  | crash (host : ℕ)

structure Cfg where
  G : ℕ
  σ : ℕ
  aware : Bool
  expiry : Bool

def init : ESt := ⟨0, 0, fun _ => ⟨0, 0, 0, 0, false, 0⟩, []⟩

/-- the coordinator's accounted total: outstanding allocations plus settled amounts -/
def acc (s : ESt) : ℕ := ∑ i ∈ range s.n, (if (s.g i).settled then (s.g i).final else (s.g i).amt)

/-- the total spend across all hosts -/
def total (s : ESt) : ℕ := ∑ i ∈ range s.n, (s.g i).spent

def margin (C : Cfg) : ℕ := if C.aware then C.σ else 0

/-- replace grant i -/
def upd (s : ESt) (i : ℕ) (v : GS) : ESt := ⟨s.now, s.n, Function.update s.g i v, s.cut⟩

/-- append a new grant -/
def add (s : ESt) (v : GS) : ESt := ⟨s.now, s.n + 1, Function.update s.g s.n v, s.cut⟩

@[simp] theorem upd_n (s : ESt) (i : ℕ) (v : GS) : (upd s i v).n = s.n := rfl
@[simp] theorem upd_now (s : ESt) (i : ℕ) (v : GS) : (upd s i v).now = s.now := rfl
@[simp] theorem upd_cut (s : ESt) (i : ℕ) (v : GS) : (upd s i v).cut = s.cut := rfl
theorem upd_self (s : ESt) (i : ℕ) (v : GS) : (upd s i v).g i = v := by simp [upd]
theorem upd_ne (s : ESt) (i j : ℕ) (v : GS) (h : j ≠ i) : (upd s i v).g j = s.g j := by simp [upd, h]

def step (C : Cfg) (s : ESt) : EOp → ESt
  | .tick => ⟨s.now + 1, s.n, s.g, s.cut⟩
  | .grant host a dur =>
    if acc s + a ≤ C.G then add s ⟨host, a, s.now + dur, 0, false, 0⟩ else s
  | .spend i x h =>
    if i < s.n ∧ h + margin C < (s.g i).exp ∧ (s.g i).spent + x ≤ (s.g i).amt then
      upd s i ⟨(s.g i).host, (s.g i).amt, (s.g i).exp, (s.g i).spent + x, (s.g i).settled, (s.g i).final⟩
    else s
  | .reclaim i c =>
    if C.expiry = true ∧ i < s.n ∧ (s.g i).settled = false ∧ (s.g i).exp + margin C ≤ c then
      upd s i ⟨(s.g i).host, (s.g i).amt, (s.g i).exp, (s.g i).spent, true,
        if (s.g i).host ∈ s.cut then (s.g i).amt else (s.g i).spent⟩
    else s
  | .reconcile i =>
    if i < s.n ∧ (s.g i).settled = true ∧ (s.g i).host ∉ s.cut then
      upd s i ⟨(s.g i).host, (s.g i).amt, (s.g i).exp, (s.g i).spent, (s.g i).settled, (s.g i).spent⟩
    else s
  | .partition host => ⟨s.now, s.n, s.g, host :: s.cut⟩
  | .heal host => ⟨s.now, s.n, s.g, s.cut.filter (· ≠ host)⟩
  | .crash _ => s

def run (C : Cfg) (s : ESt) (ops : List EOp) : ESt := ops.foldl (step C) s

/-- bounded skew: host clocks lag true time by ≤ σ; the coordinator's clock leads by ≤ σ -/
def legal (C : Cfg) (s : ESt) : EOp → Prop
  | .spend _ _ h => s.now ≤ h + C.σ
  | .reclaim _ c => c ≤ s.now + C.σ
  | _ => True

/-! ## (1) Safety -/

structure Inv (C : Cfg) (s : ESt) : Prop where
  within : ∀ i < s.n, (s.g i).spent ≤ (s.g i).amt
  settled_ok : ∀ i < s.n, (s.g i).settled = true →
    (s.g i).spent ≤ (s.g i).final ∧ (s.g i).final ≤ (s.g i).amt ∧ (s.g i).exp ≤ s.now
  cap : acc s ≤ C.G

theorem inv_init (C : Cfg) : Inv C init := ⟨by simp [init], by simp [init], by simp [acc, init]⟩

theorem total_le_acc (C : Cfg) (s : ESt) (h : Inv C s) : total s ≤ acc s := by
  unfold total acc
  apply Finset.sum_le_sum; intro i hi
  rw [mem_range] at hi
  split_ifs with hs
  · exact (h.settled_ok i hi hs).1
  · exact h.within i hi

/-- updating grant i changes the accounted total only at i -/
theorem acc_upd (s : ESt) (i : ℕ) (v : GS) (hi : i < s.n) :
    acc (upd s i v) + (if (s.g i).settled then (s.g i).final else (s.g i).amt) =
      acc s + (if v.settled then v.final else v.amt) := by
  unfold acc
  simp only [upd_n]
  rw [← Finset.add_sum_erase _ _ (mem_range.2 hi), ← Finset.add_sum_erase (range s.n) _ (mem_range.2 hi)]
  have e : ∑ j ∈ (range s.n).erase i, (if ((upd s i v).g j).settled then ((upd s i v).g j).final else ((upd s i v).g j).amt) =
      ∑ j ∈ (range s.n).erase i, (if (s.g j).settled then (s.g j).final else (s.g j).amt) := by
    apply Finset.sum_congr rfl; intro j hj
    rw [upd_ne s i j v (Finset.ne_of_mem_erase hj)]
  rw [e, upd_self]
  omega

theorem acc_upd_le (s : ESt) (i : ℕ) (v : GS) (hi : i < s.n)
    (hle : (if v.settled then v.final else v.amt) ≤ (if (s.g i).settled then (s.g i).final else (s.g i).amt)) :
    acc (upd s i v) ≤ acc s := by
  have := acc_upd s i v hi
  omega

theorem step_inv (C : Cfg) (hC : C.aware = true) (s : ESt) (o : EOp) (ho : legal C s o) (h : Inv C s) :
    Inv C (step C s o) := by
  have hm : margin C = C.σ := by simp [margin, hC]
  cases o with
  | tick =>
    refine ⟨h.within, fun i hi hs => ?_, h.cap⟩
    obtain ⟨a, b, c⟩ := h.settled_ok i hi hs
    exact ⟨a, b, by show (s.g i).exp ≤ s.now + 1; omega⟩
  | grant host a dur =>
    simp only [step]
    split_ifs with hg
    · have hold : ∀ j < s.n, (add s ⟨host, a, s.now + dur, 0, false, 0⟩).g j = s.g j := fun j hj => by
        simp [add, Function.update_of_ne (show j ≠ s.n by omega)]
      have hnew : (add s ⟨host, a, s.now + dur, 0, false, 0⟩).g s.n = ⟨host, a, s.now + dur, 0, false, 0⟩ := by
        simp [add]
      refine ⟨fun i hi => ?_, fun i hi hs => ?_, ?_⟩
      · change i < s.n + 1 at hi
        rcases Nat.lt_or_ge i s.n with h' | h'
        · rw [hold i h']; exact h.within i h'
        · rw [show i = s.n by omega, hnew]; simp
      · change i < s.n + 1 at hi
        rcases Nat.lt_or_ge i s.n with h' | h'
        · rw [hold i h'] at hs ⊢; exact h.settled_ok i h' hs
        · rw [show i = s.n by omega, hnew] at hs; simp at hs
      · unfold acc
        change ∑ i ∈ range (s.n + 1), _ ≤ C.G
        rw [Finset.sum_range_succ, hnew]
        have e : ∑ i ∈ range s.n, (if ((add s ⟨host, a, s.now + dur, 0, false, 0⟩).g i).settled
            then ((add s ⟨host, a, s.now + dur, 0, false, 0⟩).g i).final
            else ((add s ⟨host, a, s.now + dur, 0, false, 0⟩).g i).amt) = acc s := by
          unfold acc
          apply Finset.sum_congr rfl; intro i hi
          rw [hold i (mem_range.1 hi)]
        rw [e]; simpa using hg
    · exact h
  | spend i x hc =>
    simp only [legal] at ho
    simp only [step]
    split_ifs with hsp
    · obtain ⟨hi, hexp, hamt⟩ := hsp
      rw [hm] at hexp
      have hns : (s.g i).settled = false := by
        by_contra hc'
        have := (h.settled_ok i hi (by simpa using hc')).2.2
        omega
      refine ⟨fun j hj => ?_, fun j hj hs => ?_, ?_⟩
      · rw [upd_n] at hj
        by_cases hji : j = i
        · subst hji; rw [upd_self]; exact hamt
        · rw [upd_ne s i j _ hji]; exact h.within j hj
      · rw [upd_n] at hj
        by_cases hji : j = i
        · subst hji; rw [upd_self] at hs; simp [hns] at hs
        · rw [upd_ne s i j _ hji] at hs ⊢; exact h.settled_ok j hj hs
      · exact (acc_upd_le s i ⟨(s.g i).host, (s.g i).amt, (s.g i).exp, (s.g i).spent + x, (s.g i).settled,
          (s.g i).final⟩ hi le_rfl).trans h.cap
    · exact h
  | reclaim i c =>
    simp only [legal] at ho
    simp only [step]
    by_cases hr : C.expiry = true ∧ i < s.n ∧ (s.g i).settled = false ∧ (s.g i).exp + margin C ≤ c
    · rw [if_pos hr]
      obtain ⟨-, hi, hns, hexp⟩ := hr
      rw [hm] at hexp
      have hfin : (if (s.g i).host ∈ s.cut then (s.g i).amt else (s.g i).spent) ≤ (s.g i).amt := by
        split_ifs <;> first | exact le_rfl | exact h.within i hi
      have hsp : (s.g i).spent ≤ (if (s.g i).host ∈ s.cut then (s.g i).amt else (s.g i).spent) := by
        split_ifs <;> first | exact le_rfl | exact h.within i hi
      refine ⟨fun j hj => ?_, fun j hj hs => ?_, ?_⟩
      · rw [upd_n] at hj
        by_cases hji : j = i
        · subst hji; rw [upd_self]; exact h.within j hj
        · rw [upd_ne s i j _ hji]; exact h.within j hj
      · rw [upd_n] at hj
        by_cases hji : j = i
        · subst hji; rw [upd_self]; exact ⟨hsp, hfin, by simp only [upd_now]; omega⟩
        · rw [upd_ne s i j _ hji] at hs ⊢; exact h.settled_ok j hj hs
      · refine (acc_upd_le s i _ hi ?_).trans h.cap
        rw [if_pos rfl, hns, if_neg Bool.false_ne_true]
        exact hfin
    · rw [if_neg hr]; exact h
  | reconcile i =>
    simp only [step]
    split_ifs with hr
    · obtain ⟨hi, hs, -⟩ := hr
      obtain ⟨h1, h2, h3⟩ := h.settled_ok i hi hs
      refine ⟨fun j hj => ?_, fun j hj hs' => ?_, ?_⟩
      · rw [upd_n] at hj
        by_cases hji : j = i
        · subst hji; rw [upd_self]; exact h.within j hj
        · rw [upd_ne s i j _ hji]; exact h.within j hj
      · rw [upd_n] at hj
        by_cases hji : j = i
        · subst hji; rw [upd_self]; exact ⟨le_rfl, h.within j hj, by simpa using h3⟩
        · rw [upd_ne s i j _ hji] at hs' ⊢; exact h.settled_ok j hj hs'
      · refine (acc_upd_le s i _ hi ?_).trans h.cap
        show (if (s.g i).settled then (s.g i).spent else (s.g i).amt) ≤ _
        rw [hs, if_pos rfl, if_pos rfl]
        exact h1
    · exact h
  | partition host => exact ⟨h.within, h.settled_ok, h.cap⟩
  | heal host => exact ⟨h.within, h.settled_ok, h.cap⟩
  | crash host => exact h

/-- traces whose every operation is legal in the state where it occurs -/
def LegalTrace (C : Cfg) : ESt → List EOp → Prop
  | _, [] => True
  | s, o :: ops => legal C s o ∧ LegalTrace C (step C s o) ops

/-- a checkable version of `legal` -/
def legalB (C : Cfg) (s : ESt) : EOp → Bool
  | .spend _ _ h => decide (s.now ≤ h + C.σ)
  | .reclaim _ c => decide (c ≤ s.now + C.σ)
  | _ => true

def legalTraceB (C : Cfg) : ESt → List EOp → Bool
  | _, [] => true
  | s, o :: ops => legalB C s o && legalTraceB C (step C s o) ops

theorem legalTrace_of_B (C : Cfg) : ∀ (ops : List EOp) (s : ESt), legalTraceB C s ops = true → LegalTrace C s ops := by
  intro ops
  induction ops with
  | nil => intro _ _; trivial
  | cons o ops ih =>
    intro s h
    simp only [legalTraceB, Bool.and_eq_true] at h
    refine ⟨?_, ih _ h.2⟩
    have h1 := h.1
    cases o <;> simp_all [legalB, legal]

theorem run_inv (C : Cfg) (hC : C.aware = true) (s : ESt) (ops : List EOp) (hl : LegalTrace C s ops)
    (h : Inv C s) : Inv C (run C s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => exact ih _ hl.2 (step_inv C hC s o hl.1 h)

/-- **Escrow safety.** With skew-aware expiry, for every legal interleaving of grants, local spends, crashes,
partitions, heals, ticks, settlements and reconciliations, the total spend across all hosts is ≤ G. -/
theorem escrow_safe (C : Cfg) (hC : C.aware = true) (ops : List EOp) (hl : LegalTrace C init ops) :
    total (run C init ops) ≤ C.G :=
  let h := run_inv C hC init ops hl (inv_init C)
  (total_le_acc C _ h).trans h.cap

/-! ## (3) Liveness: escrow returns after expiry -/

/-- **Settlement frees unused escrow.** Once true time ≥ exp + 2σ, a coordinator reading within σ of true time
settles the grant. If the host is reachable, the accounted total drops by exactly the unused escrow amt − spent. -/
theorem reclaim_frees (C : Cfg) (hC : C.aware = true) (hE : C.expiry = true) (s : ESt) (h : Inv C s) (i c : ℕ)
    (hi : i < s.n) (hns : (s.g i).settled = false) (hlate : (s.g i).exp + 2 * C.σ ≤ s.now)
    (hc : s.now ≤ c + C.σ) (hreach : (s.g i).host ∉ s.cut) :
    ((step C s (.reclaim i c)).g i).settled = true ∧ ((step C s (.reclaim i c)).g i).final = (s.g i).spent ∧
      acc (step C s (.reclaim i c)) + ((s.g i).amt - (s.g i).spent) = acc s := by
  have hm : margin C = C.σ := by simp [margin, hC]
  have hcond : C.expiry = true ∧ i < s.n ∧ (s.g i).settled = false ∧ (s.g i).exp + margin C ≤ c := by
    refine ⟨hE, hi, hns, ?_⟩; rw [hm]; omega
  have hstep : step C s (.reclaim i c) = upd s i ⟨(s.g i).host, (s.g i).amt, (s.g i).exp, (s.g i).spent, true,
      (s.g i).spent⟩ := by
    simp only [step, if_pos hcond, if_neg hreach]
  rw [hstep, upd_self]
  refine ⟨rfl, rfl, ?_⟩
  have e := acc_upd s i ⟨(s.g i).host, (s.g i).amt, (s.g i).exp, (s.g i).spent, true, (s.g i).spent⟩ hi
  rw [hns, if_neg Bool.false_ne_true, if_pos rfl] at e
  dsimp only at e
  have := h.within i hi
  omega

/-- **Reconciliation after a partition.** A grant settled while its host was partitioned (settled at the full
allocation) returns its unused escrow once the host is reachable again. -/
theorem reconcile_frees (C : Cfg) (s : ESt) (h : Inv C s) (i : ℕ) (hi : i < s.n) (hs : (s.g i).settled = true)
    (hreach : (s.g i).host ∉ s.cut) :
    acc (step C s (.reconcile i)) + ((s.g i).final - (s.g i).spent) = acc s := by
  have hstep : step C s (.reconcile i) = upd s i ⟨(s.g i).host, (s.g i).amt, (s.g i).exp, (s.g i).spent,
      (s.g i).settled, (s.g i).spent⟩ := by
    simp only [step, if_pos (show i < s.n ∧ (s.g i).settled = true ∧ (s.g i).host ∉ s.cut from ⟨hi, hs, hreach⟩)]
  rw [hstep]
  have e := acc_upd s i ⟨(s.g i).host, (s.g i).amt, (s.g i).exp, (s.g i).spent, (s.g i).settled, (s.g i).spent⟩ hi
  have := (h.settled_ok i hi hs).1
  rw [hs] at e ⊢
  rw [if_pos rfl, if_pos rfl] at e
  dsimp only at e
  omega

/-! ## Witnesses -/

/-- G = 10, σ = 2 -/
def C10 (aware expiry : Bool) : Cfg := ⟨10, 2, aware, expiry⟩

/-- host 0 gets 10 until t = 5; at t = 5 the coordinator (clock 5) settles it; host 1 gets 10 and spends it; host 0,
whose clock reads 3 (2 behind), spends its 10 -/
def skewTrace : List EOp :=
  [.grant 0 10 5, .tick, .tick, .tick, .tick, .tick, .reclaim 0 5, .grant 1 10 100, .spend 1 10 5, .spend 0 10 3]

theorem skewTrace_legal (aware : Bool) : LegalTrace (C10 aware true) init skewTrace := by
  cases aware <;> exact legalTrace_of_B _ _ _ (by decide)

/-- **(2) Skew-unaware settlement double-allocates.** Without the σ margins the legal trace spends 20 > G = 10;
the skew-aware design spends nothing beyond its single allocation. -/
theorem skew_unaware_overspends :
    total (run (C10 false true) init skewTrace) = 20 ∧ total (run (C10 true true) init skewTrace) ≤ 10 := by
  refine ⟨by decide, escrow_safe _ rfl _ (skewTrace_legal true)⟩

/-- host 0 gets the whole budget and crashes; much later the coordinator tries to settle it and grant host 1 -/
def starveTrace : List EOp :=
  [.grant 0 10 5, .crash 0, .tick, .tick, .tick, .tick, .tick, .tick, .tick, .tick, .tick, .tick, .reclaim 0 10,
   .grant 1 10 50]

/-- **(3) No expiry starves the budget.** Without expiry host 1's grant is refused forever (n stays 1); with expiry
the crashed host's escrow returns and host 1 is granted. -/
theorem no_expiry_starves :
    (run (C10 true false) init starveTrace).n = 1 ∧ (run (C10 true true) init starveTrace).n = 2 := by
  decide

/-! ## (4) Numbers -/

/-- **Datacenter numbers.**
- 1000 hosts with 1000 units each exactly fill G = 10⁶.
- With σ = 2 ticks and 60-tick leases, every legal trace spends ≤ 10⁶.
- Unused escrow is settleable 60 + 2σ = 64 ticks after its grant. -/
theorem datacenter_example (ops : List EOp) (hl : LegalTrace ⟨1000000, 2, true, true⟩ init ops) :
    total (run ⟨1000000, 2, true, true⟩ init ops) ≤ 1000000 ∧ 1000 * 1000 ≤ (1000000 : ℕ) ∧ 60 + 2 * 2 = 64 :=
  ⟨escrow_safe _ rfl ops hl, by norm_num, by norm_num⟩

end ControlStack.EscrowBudget

#print axioms ControlStack.EscrowBudget.escrow_safe
#print axioms ControlStack.EscrowBudget.reclaim_frees
#print axioms ControlStack.EscrowBudget.reconcile_frees
#print axioms ControlStack.EscrowBudget.skew_unaware_overspends
#print axioms ControlStack.EscrowBudget.no_expiry_starves
#print axioms ControlStack.EscrowBudget.datacenter_example
