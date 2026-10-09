/-
LabStack: one shared-state lab system composing SC-26 (payments), SC-16 (deployments) and SC-28 (compute leases)
(RUNTIME-VM-HANDOFF §6, F8: "formalize one actual shared-state transition across F1/F3/F4/F5/F7").

`Core/Compose.lean`'s `prod` keeps components independent. A GLOBAL budget is shared state across gates, so this file
uses a direct joint state `LabSt`:
- the three component states;
- ONE shared absorbing halt bit;
- ONE global money counter `money`.
Operations (`LabOp`):
- `pay o`, `dep o`, `comp o`: each component's own operations, run by its own step (with its deployed checks);
- `deployPay n`: a cross-gate deputy. A deployment of approval nonce n triggers a vendor payment. It goes through
  SC-26's own gate: it issues `execute` for the vendor's payment request, which needs SC-26's approval;
- `halt c`: the lab admins' halt.
The joint step adds three couplings:
- **global budget**: a payment step or a compute step is accepted only if `money + Δ ≤ G`, where Δ is the payment
  spend increase, or the metered compute charge increase × `price`;
- **shared halt**: a lab halt, or any component's own admin halt, sets the shared halt bit (`share = true`). After
  it, nothing changes except in-flight bank arrivals (`pay (.arrive k)`);
- **authenticated issuers**: the lab runs under `authRun` (`Core/AuthenticatedLog.lean`) with `labClaim`, so every
  trusted act is issuer-authenticated.

Results (adversary class TRACE_ARBITRARY over issued traces, with issuers of the adversary in U):
- `lab_safe`:
  - SC-26 `Good` (exactly approved, unique, within SC-26's cap);
  - SC-16 `Good` (deployments reviewed and approved);
  - SC-28 `Good` (usage within leases and SC-28's cap);
  - GLOBAL: total payments + price × total compute usage ≤ G;
  - authenticated provenance: every payment approval, deploy review, deploy approval and lease was issued by its
    principal, and that principal is outside U.
- `lab_halt_freezes`: after the shared halt, the deployment and compute states, the money counter and the payment
  gate's sent messages are frozen; the bank gains only messages already in flight.
- `deputy_admissible`: the deploy-triggered payment is an admissible bridge in the sense of `Compose`
  (`Compose.admissible_of_step`): it acts on SC-26 only by issuing SC-26's own operation.
Witnesses:
- `separate_caps_exceed_global`: each gate within its own cap jointly spends 20 > G = 10. In the lab the compute
  step is refused;
- `deputy_reuse_breaks_sc26`: a deputy that treats the deploy approval as payment authority (appends to the bank
  directly) breaks SC-26 `Good`, while the admissible deputy pays nothing without SC-26 approval;
- `no_shared_halt_keeps_running`: without the shared halt, compute keeps consuming after SC-16's admin halts.
Certificate: `labStack` (Cert.Stack) with its typed ledger `labLedger` (printable by tools/cert_ledger.py with
`--import ControlStack.Scenarios.LabStack --ledger ControlStack.LabStack.labLedger`).

Limits:
- Composition is by interleaving of atomic component steps.
- The budget counter, halt bit and deputy are trusted components of the joint gate (the runtime correspondence is a
  premise, as for each component).
- Price × metered charge is the compute spend definition. Real billing lag and meters are measurement premises.
- No new mathematics.
-/
import Mathlib.Tactic
import ControlStack.Core.Compose
import ControlStack.Core.Cert
import ControlStack.Core.AuthenticatedLog
import ControlStack.Scenarios.SC26Authenticated
import ControlStack.Scenarios.AuthInstancesA

namespace ControlStack.LabStack

open ControlStack.Gate ControlStack.Authenticated ControlStack.AuthenticatedLog

/-! ## The joint system -/

structure LabParams where
  R26 : SC26.Roles
  cap26 : ℕ
  R16 : SC16.Roles
  h : ℕ → ℕ
  admins28 : List ℕ
  G28 : ℕ
  price : ℕ
  G : ℕ
  /-- deployment approval nonce ↦ the SC-26 request id of its vendor payment -/
  vendor : ℕ → ℕ
  labAdmins : List ℕ

structure LabSt where
  pay : SC26.St
  dep : SC16.St
  comp : SC28.St
  halted : Bool
  money : ℕ
deriving DecidableEq, Repr

inductive LabOp where
  | pay (o : SC26.Op)
  | dep (o : SC16.Op)
  | comp (o : SC28.Op)
  | deployPay (n : ℕ)
  | halt (c : ℕ)
deriving DecidableEq, Repr

def labInit : LabSt := ⟨SC26.init, SC16.init, SC28.init, false, 0⟩

def isArrive : SC26.Op → Bool
  | .arrive _ => true
  | _ => false

/-- the deputy's SC-26 operation: `execute` the vendor's payment request if deployment `n` happened; otherwise a
direct bank call by a non-gate identity (refused by the bank's authentication: a no-op) -/
def deputyOp (P : LabParams) (d : SC16.St) (n : ℕ) : SC26.Op :=
  if d.deployed.any (fun e => decide (e.n = n)) then .execute P.R26.gate (P.vendor n)
  else .bankCall (P.R26.gate + 1) 0 ⟨0, 0, 0⟩

/-- accept a payment-gate step if the global budget allows its spend increase -/
def payStep (P : LabParams) (share : Bool) (s : LabSt) (p : SC26.St) : LabSt :=
  if s.money + (p.spent - s.pay.spent) ≤ P.G then
    { s with pay := p, money := s.money + (p.spent - s.pay.spent), halted := s.halted || (share && p.halted) }
  else s

/-- accept a compute step if the global budget allows its metered charge × price -/
def compStep (P : LabParams) (share : Bool) (s : LabSt) (c : SC28.St) : LabSt :=
  if s.money + P.price * (SC28.spentT c - SC28.spentT s.comp) ≤ P.G then
    { s with comp := c, money := s.money + P.price * (SC28.spentT c - SC28.spentT s.comp),
             halted := s.halted || (share && c.halted) }
  else s

def labStep (P : LabParams) (share : Bool) (s : LabSt) : LabOp → LabSt
  | .pay o =>
    if s.halted = true ∧ isArrive o = false then s else payStep P share s (SC26.step P.R26 P.cap26 SC26.full s.pay o)
  | .dep o =>
    if s.halted then s
    else { s with dep := SC16.step P.R16 P.h SC16.full s.dep o,
                  halted := s.halted || (share && (SC16.step P.R16 P.h SC16.full s.dep o).halted) }
  | .comp o => if s.halted then s else compStep P share s (SC28.step P.admins28 P.G28 SC28.full s.comp o)
  | .deployPay n =>
    if s.halted then s else payStep P share s (SC26.step P.R26 P.cap26 SC26.full s.pay (deputyOp P s.dep n))
  | .halt c => if c ∈ P.labAdmins then { s with halted := true } else s

def labRun (P : LabParams) (share : Bool) (s : LabSt) (ops : List LabOp) : LabSt := ops.foldl (labStep P share) s

/-- the joint claim: each component's own claims; the deputy is a gate-internal service -/
def labClaim : LabOp → Option ℕ
  | .pay o => SC26Authenticated.claim o
  | .dep o => AuthInstances.claim16 o
  | .comp o => AuthInstances.claim28 o
  | .deployPay _ => none
  | .halt c => some c

/-- legal operations: no untrusted bank call with the gate credential, no privileged counter rollback -/
def labLegal (P : LabParams) : LabOp → Prop
  | .pay o => SC26.legal P.R26 o
  | .comp o => SC28.legal o
  | _ => True

/-! ## Invariant -/

structure LabInv (P : LabParams) (s : LabSt) : Prop where
  pay : SC26.Inv P.R26 P.cap26 s.pay
  dep : SC16.Inv P.R16 P.h s.dep
  comp : SC28.Inv P.G28 s.comp
  money_ge : s.pay.spent + P.price * SC28.spentT s.comp ≤ s.money
  money_le : s.money ≤ P.G

theorem labInv_init (P : LabParams) : LabInv P labInit :=
  ⟨SC26.inv_init _ _, SC16.inv_init _ _, SC28.inv_init _, by simp [labInit, SC26.init, SC28.init, SC28.spentT],
    by simp [labInit]⟩

theorem payStep_inv (P : LabParams) (share : Bool) (s : LabSt) (p : SC26.St) (h : LabInv P s)
    (hp : SC26.Inv P.R26 P.cap26 p) : LabInv P (payStep P share s p) := by
  unfold payStep
  split_ifs with hm
  · refine ⟨hp, h.dep, h.comp, ?_, hm⟩
    have := h.money_ge
    simp only
    generalize P.price * SC28.spentT s.comp = X at *
    omega
  · exact h

theorem compStep_inv (P : LabParams) (share : Bool) (s : LabSt) (c : SC28.St) (h : LabInv P s)
    (hc : SC28.Inv P.G28 c) : LabInv P (compStep P share s c) := by
  unfold compStep
  split_ifs with hm
  · refine ⟨h.pay, h.dep, hc, ?_, hm⟩
    have h0 := h.money_ge
    have h1 : SC28.spentT c ≤ SC28.spentT s.comp + (SC28.spentT c - SC28.spentT s.comp) := by omega
    have h2 := Nat.mul_le_mul_left P.price h1
    rw [Nat.mul_add] at h2
    simp only
    generalize P.price * SC28.spentT c = A at *
    generalize P.price * SC28.spentT s.comp = B at *
    generalize P.price * (SC28.spentT c - SC28.spentT s.comp) = D at *
    omega
  · exact h

theorem deputyOp_legal (P : LabParams) (d : SC16.St) (n : ℕ) : SC26.legal P.R26 (deputyOp P d n) := by
  unfold deputyOp; split
  · trivial
  · show P.R26.gate + 1 ≠ P.R26.gate; omega

theorem labStep_inv (P : LabParams) (share : Bool) (s : LabSt) (o : LabOp) (ho : labLegal P o) (h : LabInv P s) :
    LabInv P (labStep P share s o) := by
  cases o with
  | pay o =>
    simp only [labStep]
    split_ifs
    · exact h
    · exact payStep_inv P share s _ h (SC26.step_inv _ _ SC26.sound_full _ o ho h.pay)
  | dep o =>
    simp only [labStep]
    split_ifs
    · exact h
    · exact ⟨h.pay, SC16.step_inv _ _ _ o h.dep, h.comp, h.money_ge, h.money_le⟩
  | comp o =>
    simp only [labStep]
    split_ifs
    · exact h
    · exact compStep_inv P share s _ h (SC28.step_inv _ _ _ o ho h.comp)
  | deployPay n =>
    simp only [labStep]
    split_ifs
    · exact h
    · exact payStep_inv P share s _ h (SC26.step_inv _ _ SC26.sound_full _ _ (deputyOp_legal P s.dep n) h.pay)
  | halt c =>
    simp only [labStep]
    split_ifs
    · exact ⟨h.pay, h.dep, h.comp, h.money_ge, h.money_le⟩
    · exact h

theorem labRun_inv (P : LabParams) (share : Bool) (s : LabSt) (ops : List LabOp) (hops : ∀ o ∈ ops, labLegal P o)
    (h : LabInv P s) : LabInv P (labRun P share s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih =>
    exact ih _ (fun o' ho' => hops o' (List.mem_cons_of_mem o ho')) (labStep_inv P share s o (hops o List.mem_cons_self) h)

/-- payments actually made are at most SC-26's committed spend -/
theorem bank_le_spent {R : SC26.Roles} {cap : ℕ} {s : SC26.St} (h : SC26.Inv R cap s) :
    (s.bank.map (fun e => e.2.amount)).sum ≤ s.spent := by
  rw [SC26.bank_sum s (fun e he => (h.bank_ok e he).2)]
  have hsub : List.Subperm (s.bank.map Prod.fst) s.reserved :=
    List.Nodup.subperm h.bank_nodup (fun k hk => by
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hk
      exact (h.bank_ok e he).1)
  calc _ ≤ (s.reserved.map (SC26.amt s)).sum := SC26.sum_le_of_subperm _ _ _ hsub
    _ = s.spent := h.spent_eq.symm

/-- **The global budget**: total payments + price × total compute usage ≤ G -/
theorem global_budget (P : LabParams) (s : LabSt) (h : LabInv P s) :
    (s.pay.bank.map (fun e => e.2.amount)).sum + P.price * SC28.usedT s.comp ≤ P.G := by
  have h1 := bank_le_spent h.pay
  have h2 := Nat.mul_le_mul_left P.price h.comp.tot
  have h3 := h.money_ge
  have h4 := h.money_le
  generalize P.price * SC28.usedT s.comp = A at *
  generalize P.price * SC28.spentT s.comp = B at *
  omega

/-! ## Provenance of trusted acts under authentication -/

theorem payStep_cases (P : LabParams) (share : Bool) (s : LabSt) (p : SC26.St) :
    payStep P share s p = s ∨
      ((payStep P share s p).pay = p ∧ (payStep P share s p).dep = s.dep ∧ (payStep P share s p).comp = s.comp) := by
  unfold payStep; split_ifs
  · exact Or.inr ⟨rfl, rfl, rfl⟩
  · exact Or.inl rfl

theorem compStep_cases (P : LabParams) (share : Bool) (s : LabSt) (c : SC28.St) :
    compStep P share s c = s ∨
      ((compStep P share s c).comp = c ∧ (compStep P share s c).dep = s.dep ∧ (compStep P share s c).pay = s.pay) := by
  unfold compStep; split_ifs
  · exact Or.inr ⟨rfl, rfl, rfl⟩
  · exact Or.inl rfl

/-- one lab step changes each component only by that component's own step (or not at all) -/
theorem labStep_parts (P : LabParams) (share : Bool) (s : LabSt) (o : LabOp) :
    let t := labStep P share s o
    (t.pay = s.pay ∨ (∃ o', o = .pay o' ∧ t.pay = SC26.step P.R26 P.cap26 SC26.full s.pay o') ∨
        (∃ n, o = .deployPay n ∧ t.pay = SC26.step P.R26 P.cap26 SC26.full s.pay (deputyOp P s.dep n))) ∧
    (t.dep = s.dep ∨ ∃ o', o = .dep o' ∧ t.dep = SC16.step P.R16 P.h SC16.full s.dep o') ∧
    (t.comp = s.comp ∨ ∃ o', o = .comp o' ∧ t.comp = SC28.step P.admins28 P.G28 SC28.full s.comp o') := by
  cases o with
  | pay o =>
    simp only [labStep]
    split_ifs
    · exact ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
    · rcases payStep_cases P share s (SC26.step P.R26 P.cap26 SC26.full s.pay o) with e | ⟨e1, e2, e3⟩
      · rw [e]; exact ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
      · exact ⟨Or.inr (Or.inl ⟨o, rfl, e1⟩), Or.inl e2, Or.inl e3⟩
  | dep o =>
    simp only [labStep]
    split_ifs
    · exact ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
    · exact ⟨Or.inl rfl, Or.inr ⟨o, rfl, rfl⟩, Or.inl rfl⟩
  | comp o =>
    simp only [labStep]
    split_ifs
    · exact ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
    · rcases compStep_cases P share s (SC28.step P.admins28 P.G28 SC28.full s.comp o) with e | ⟨e1, e2, e3⟩
      · rw [e]; exact ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
      · exact ⟨Or.inl e3, Or.inl e2, Or.inr ⟨o, rfl, e1⟩⟩
  | deployPay n =>
    simp only [labStep]
    split_ifs
    · exact ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
    · rcases payStep_cases P share s (SC26.step P.R26 P.cap26 SC26.full s.pay (deputyOp P s.dep n)) with e | ⟨e1, e2, e3⟩
      · rw [e]; exact ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl⟩
      · exact ⟨Or.inr (Or.inr ⟨n, rfl, e1⟩), Or.inl e2, Or.inl e3⟩
  | halt c =>
    simp only [labStep]
    split_ifs <;> exact ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

theorem deputyOp_not_approve (P : LabParams) (d : SC16.St) (n a k : ℕ) (tx : SC26.Tx) :
    deputyOp P d n ≠ .approve a k tx := by
  unfold deputyOp; split <;> simp

theorem pay_appr_step (P : LabParams) (share : Bool) (s : LabSt) (o : LabOp) (x : ℕ × ℕ × SC26.Tx)
    (hx : x ∈ (labStep P share s o).pay.approvals) :
    x ∈ s.pay.approvals ∨ ∃ c, labClaim o = some c ∧ (o = .pay (.approve c x.1 x.2.2) ∧ c = x.2.1) := by
  rcases (labStep_parts P share s o).1 with e | ⟨o', rfl, e⟩ | ⟨n, rfl, e⟩
  · rw [e] at hx; exact Or.inl hx
  · rw [e] at hx
    rcases SC26Authenticated.step_approvals _ _ _ o' x hx with h | h
    · exact Or.inl h
    · subst h; exact Or.inr ⟨x.2.1, rfl, rfl, rfl⟩
  · rw [e] at hx
    rcases SC26Authenticated.step_approvals _ _ _ _ x hx with h | h
    · exact Or.inl h
    · exact absurd h (deputyOp_not_approve P s.dep n _ _ _)

theorem dep_review_step (P : LabParams) (share : Bool) (s : LabSt) (o : LabOp) (x : SC16.Review)
    (hx : x ∈ (labStep P share s o).dep.reviews) :
    x ∈ s.dep.reviews ∨ ∃ c, labClaim o = some c ∧ (o = .dep (.review c x.d) ∧ c = x.reviewer ∧ c ∈ P.R16.reviewers) := by
  rcases (labStep_parts P share s o).2.1 with e | ⟨o', rfl, e⟩
  · rw [e] at hx; exact Or.inl hx
  · rw [e] at hx
    rcases AuthInstances.sc16_review_step _ _ _ o' x hx with h | ⟨c, hc, h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨c, hc, by rw [h1], h2, h3⟩

theorem dep_appr_step (P : LabParams) (share : Bool) (s : LabSt) (o : LabOp) (x : SC16.Appr)
    (hx : x ∈ (labStep P share s o).dep.approvals) :
    x ∈ s.dep.approvals ∨ ∃ c, labClaim o = some c ∧
      (o = .dep (.approve c x.n x.d x.target x.slot) ∧ c = x.approver ∧ c ∈ P.R16.approvers) := by
  rcases (labStep_parts P share s o).2.1 with e | ⟨o', rfl, e⟩
  · rw [e] at hx; exact Or.inl hx
  · rw [e] at hx
    rcases AuthInstances.sc16_appr_step _ _ _ o' x hx with h | ⟨c, hc, h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨c, hc, by rw [h1], h2, h3⟩

theorem comp_lease_step (P : LabParams) (share : Bool) (s : LabSt) (o : LabOp) (x : ℕ × ℕ)
    (hx : x ∈ (labStep P share s o).comp.leases) :
    x ∈ s.comp.leases ∨ ∃ c, labClaim o = some c ∧ (o = .comp (.issue c x.1 x.2) ∧ c ∈ P.admins28) := by
  rcases (labStep_parts P share s o).2.2 with e | ⟨o', rfl, e⟩
  · rw [e] at hx; exact Or.inl hx
  · rw [e] at hx
    rcases AuthInstances.sc28_lease_step _ _ _ o' x hx with h | ⟨c, hc, h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨c, hc, by rw [h1], h2⟩

/-- **LabStack safety.** For every legal issued trace (adversary issuers in U, disjoint from the trusted roles): the
three component properties, the GLOBAL budget, and authenticated provenance of every trusted act. -/
theorem lab_safe (P : LabParams) (U : List ℕ) (ops : List (ℕ × LabOp)) (hlegal : ∀ io ∈ ops, labLegal P io.2)
    (hU26 : ∀ u ∈ U, u ∉ P.R26.approvers) (hU16r : ∀ u ∈ U, u ∉ P.R16.reviewers)
    (hU16a : ∀ u ∈ U, u ∉ P.R16.approvers) (hU28 : ∀ u ∈ U, u ∉ P.admins28) :
    SC26.Good P.R26 P.cap26 (authRun (labStep P true) labClaim labInit ops).pay ∧
    SC16.Good P.R16 P.h (authRun (labStep P true) labClaim labInit ops).dep ∧
    SC28.Good P.G28 (authRun (labStep P true) labClaim labInit ops).comp ∧
    ((authRun (labStep P true) labClaim labInit ops).pay.bank.map (fun e => e.2.amount)).sum +
      P.price * SC28.usedT (authRun (labStep P true) labClaim labInit ops).comp ≤ P.G ∧
    (∀ ap ∈ (authRun (labStep P true) labClaim labInit ops).pay.approvals, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
      (o = .pay (.approve c ap.1 ap.2.2) ∧ c = ap.2.1)) ∧
    (∀ rv ∈ (authRun (labStep P true) labClaim labInit ops).dep.reviews, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
      (o = .dep (.review c rv.d) ∧ c = rv.reviewer ∧ c ∈ P.R16.reviewers)) ∧
    (∀ ap ∈ (authRun (labStep P true) labClaim labInit ops).dep.approvals, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
      (o = .dep (.approve c ap.n ap.d ap.target ap.slot) ∧ c = ap.approver ∧ c ∈ P.R16.approvers)) ∧
    (∀ l ∈ (authRun (labStep P true) labClaim labInit ops).comp.leases, ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧
      (o = .comp (.issue c l.1 l.2) ∧ c ∈ P.admins28)) := by
  have hinv : LabInv P (authRun (labStep P true) labClaim labInit ops) := by
    rw [authRun_eq]
    exact labRun_inv P true labInit _ (fun o ho => by
      obtain ⟨i, hi⟩ := mem_of_applied labClaim ops o ho
      exact hlegal _ hi) (labInv_init P)
  refine ⟨hinv.pay.good, hinv.dep.good, hinv.comp.good, global_budget P _ hinv, ?_, ?_, ?_, ?_⟩
  · intro ap hap
    obtain ⟨c, o, hmem, hp⟩ := issued_of_mem_log (labStep P true) labClaim (fun s => s.pay.approvals)
      (fun c o x => o = .pay (.approve c x.1 x.2.2) ∧ c = x.2.1) (pay_appr_step P true) labInit rfl ops ap hap
    have hrole : ap.2.1 ∈ P.R26.approvers := by
      obtain ⟨r, -, -, hr, -⟩ := hinv.pay.appr_ok ap hap
      exact hr
    exact ⟨c, o, hmem, fun hu => hU26 c hu (hp.2 ▸ hrole), hp⟩
  · exact issued_trusted (labStep P true) labClaim (fun s => s.dep.reviews) _ P.R16.reviewers U
      (dep_review_step P true) (fun _ _ _ hp => hp.2.2) hU16r labInit rfl ops
  · exact issued_trusted (labStep P true) labClaim (fun s => s.dep.approvals) _ P.R16.approvers U
      (dep_appr_step P true) (fun _ _ _ hp => hp.2.2) hU16a labInit rfl ops
  · exact issued_trusted (labStep P true) labClaim (fun s => s.comp.leases) _ P.admins28 U
      (comp_lease_step P true) (fun _ _ _ hp => hp.2) hU28 labInit rfl ops

/-! ## One shared halt -/

theorem arrive_step (R : SC26.Roles) (cap : ℕ) (p : SC26.St) (k : ℕ) :
    (SC26.step R cap SC26.full p (.arrive k)).net = p.net ∧ (SC26.step R cap SC26.full p (.arrive k)).spent = p.spent ∧
      ∀ e ∈ (SC26.step R cap SC26.full p (.arrive k)).bank, e ∈ p.bank ∨ e ∈ p.net := by
  simp only [SC26.step]
  split
  · exact ⟨rfl, rfl, fun e he => Or.inl he⟩
  · rename_i m hm
    refine ⟨by unfold SC26.bankAppend; split_ifs <;> rfl, by unfold SC26.bankAppend; split_ifs <;> rfl, ?_⟩
    intro e he
    rcases SC26.bankAppend_mem _ _ _ _ e he with h | h
    · exact Or.inl h
    · right; rw [h]; exact List.mem_of_find?_eq_some hm

theorem labStep_halted (P : LabParams) (s : LabSt) (o : LabOp) (hh : s.halted = true) :
    let t := labStep P true s o
    t.halted = true ∧ t.dep = s.dep ∧ t.comp = s.comp ∧ t.money = s.money ∧ t.pay.net = s.pay.net ∧
      ∀ e ∈ t.pay.bank, e ∈ s.pay.bank ∨ e ∈ s.pay.net := by
  cases o with
  | pay o =>
    by_cases ha : isArrive o = true
    · cases o with
      | arrive k =>
        obtain ⟨h1, h2, h3⟩ := arrive_step P.R26 P.cap26 s.pay k
        simp only [labStep, hh, isArrive, Bool.true_eq_false, and_false, if_false]
        unfold payStep
        split_ifs
        · refine ⟨by simp [hh], rfl, rfl, by simp [h2], h1, h3⟩
        · exact ⟨hh, rfl, rfl, rfl, rfl, fun e he => Or.inl he⟩
      | _ => simp [isArrive] at ha
    · have : labStep P true s (.pay o) = s := by
        simp only [labStep]; rw [if_pos ⟨hh, by simpa using ha⟩]
      rw [this]; exact ⟨hh, rfl, rfl, rfl, rfl, fun e he => Or.inl he⟩
  | halt c =>
    simp only [labStep]
    split_ifs
    · exact ⟨rfl, rfl, rfl, rfl, rfl, fun e he => Or.inl he⟩
    · exact ⟨hh, rfl, rfl, rfl, rfl, fun e he => Or.inl he⟩
  | _ => simp only [labStep, hh, if_true]; refine ⟨trivial, trivial, trivial, trivial, trivial, ?_⟩; intro e he; exact Or.inl he

/-- **One shared halt freezes the lab.** After the shared halt (set by a lab admin or ANY component's own admin
halt), for any operations: deployments, compute and the money counter are frozen, the payment gate sends nothing
new, and the bank gains only messages already in flight. -/
theorem lab_halt_freezes (P : LabParams) (s : LabSt) (ops : List LabOp) (hh : s.halted = true) :
    let t := labRun P true s ops
    t.halted = true ∧ t.dep = s.dep ∧ t.comp = s.comp ∧ t.money = s.money ∧ t.pay.net = s.pay.net ∧
      ∀ e ∈ t.pay.bank, e ∈ s.pay.bank ∨ e ∈ s.pay.net := by
  induction ops generalizing s with
  | nil => exact ⟨hh, rfl, rfl, rfl, rfl, fun e he => Or.inl he⟩
  | cons o ops ih =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := labStep_halted P s o hh
    obtain ⟨i1, i2, i3, i4, i5, i6⟩ := ih (labStep P true s o) h1
    refine ⟨i1, i2.trans h2, i3.trans h3, i4.trans h4, i5.trans h5, fun e he => ?_⟩
    rcases i6 e he with h | h
    · exact h6 e h
    · right; rw [← h5]; exact h

/-- a component's own admin halt sets the shared halt -/
theorem component_halt_shared (P : LabParams) (s : LabSt) (c : ℕ) (hh : s.halted = false)
    (hc : c ∈ P.R16.admins) : (labStep P true s (.dep (.halt c))).halted = true := by
  simp [labStep, hh, SC16.step, hc]

/-! ## The deputy as a `Compose` bridge -/

/-- SC-16 as a gate (effects: deployments) with a spec -/
def sys16 (R : SC16.Roles) (h : ℕ → ℕ) : System SC16.St SC16.Op SC16.Dep := ⟨SC16.step R h SC16.full, SC16.St.deployed⟩

def spec16 (R : SC16.Roles) (h : ℕ → ℕ) : Spec (sys16 R h) where
  Inv := SC16.Inv R h
  ok := fun _ _ => True
  step_inv := fun s o hi => SC16.step_inv R h s o hi
  log_prefix := fun s o => SC16.deployed_prefix R h SC16.full s o
  inv_ok := fun _ _ _ _ => trivial

/-- the deploy-triggered payment bridge: reads SC-16's state, acts on SC-26's -/
def deputyBridge (P : LabParams) (n : ℕ) (d : SC16.St) (p : SC26.St) : SC26.St :=
  SC26.step P.R26 P.cap26 SC26.full p (deputyOp P d n)

/-- **The deputy is admissible** (`Compose.admissible_of_step`): it acts on SC-26 only through SC-26's own gate, so
SC-26's spec (exact approval) holds in the composed system. -/
theorem deputy_admissible (P : LabParams) (n : ℕ) :
    Compose.BridgeAdmissible (spec16 P.R16 P.h) (SC26.spec P.R26 P.cap26) (deputyBridge P n) :=
  Compose.admissible_of_step _ _ _ (fun d _ => ⟨deputyOp P d n, deputyOp_legal P d n⟩) (fun _ _ => rfl)

/-! ## Witnesses -/

def P0 : LabParams := ⟨SC26.R0, 10, SC16.R0, id, [9], 10, 1, 10, id, [4]⟩

def payOps : List SC26.Op := [.request 1 SC26.tx1, .approve 2 0 SC26.tx1, .execute 1 0, .deliver 0, .arrive 0]
def compOps : List SC28.Op := [.issue 9 0 10, .assignTo 9 1 0, .work 1 10 10]

/-- **Separate caps exceed the global budget.** SC-26 alone (cap 10) pays 10 and SC-28 alone (cap 10) consumes 10:
each gate's own theorem holds, yet together they spend 20 > G = 10. In the lab with the shared counter the compute
step is refused: payments 10, compute 0. -/
theorem separate_caps_exceed_global :
    ((SC26.run SC26.R0 10 SC26.full SC26.init payOps).bank.map (fun e => e.2.amount)).sum +
      SC28.usedT (SC28.run [9] 10 SC28.full SC28.init compOps) = 20 ∧
    ((labRun P0 true labInit (payOps.map .pay ++ compOps.map .comp)).pay.bank.map (fun e => e.2.amount)).sum = 10 ∧
    (labRun P0 true labInit (payOps.map .pay ++ compOps.map .comp)).comp.usage = [] := by
  decide

/-- the confused deputy: on a deployment, pay the vendor directly (the deploy approval reused as payment authority) -/
def unsafeDeputy (P : LabParams) (n : ℕ) (tx : SC26.Tx) (d : SC16.St) (p : SC26.St) : SC26.St :=
  if d.deployed.any (fun e => decide (e.n = n)) then { p with bank := p.bank ++ [(P.vendor n, tx)] } else p

/-- the honest deployment trace of SC-16 (reviewer 2, approver 3) -/
def depOps : List SC16.Op := [.stage 1 7, .review 2 7, .approve 3 0 7 5 0, .deploy 1 0 5 7]

/-- **Deputy reuse breaks SC-26.** After a genuinely approved deployment, the unsafe deputy pays the vendor and SC-26's
`Good` fails (no payment approval exists); the admissible deputy (through SC-26's `execute`) pays nothing. -/
theorem deputy_reuse_breaks_sc26 :
    let d := SC16.run SC16.R0 id SC16.full SC16.init depOps
    (unsafeDeputy P0 0 SC26.tx1 d SC26.init).bank = [(0, SC26.tx1)] ∧
      ¬ SC26.Good P0.R26 P0.cap26 (unsafeDeputy P0 0 SC26.tx1 d SC26.init) ∧
      (deputyBridge P0 0 d SC26.init).bank = [] := by
  refine ⟨by decide, ?_, by decide⟩
  apply SC26.not_good_of (0, SC26.tx1) (by decide)
  intro ap hap
  have : (unsafeDeputy P0 0 SC26.tx1 (SC16.run SC16.R0 id SC16.full SC16.init depOps) SC26.init).approvals = [] := by
    decide
  rw [this] at hap
  simp at hap

/-- **Without the shared halt, one gate keeps acting.** SC-16's admin (4) halts deployments; with `share = false`
compute keeps consuming, with the shared halt it does not. -/
theorem no_shared_halt_keeps_running :
    (labRun P0 false labInit ([.dep (.halt 4)] ++ compOps.map .comp)).comp.usage = [(1, 0, 10)] ∧
    (labRun P0 true labInit ([.dep (.halt 4)] ++ compOps.map .comp)).comp.usage = [] := by
  decide

/-! ## Stack certificate and typed ledger -/

open ControlStack.Cert

/-- the lab's premises (typed) -/
def labPremises (P : LabParams) (U : List ℕ) (ops : List (ℕ × LabOp)) : List Premise :=
  [⟨"LAB.issuer_authentic: the platform-reported identity is the issuer (modelled by authRun)", .environment, True⟩,
   ⟨"LAB.legal: no untrusted bank call with the gate credential; no privileged counter rollback", .environment,
     ∀ io ∈ ops, labLegal P io.2⟩,
   ⟨"LAB.adversary_outside_roles: adversary issuers hold no approver, reviewer or admin role", .organisational,
     (∀ u ∈ U, u ∉ P.R26.approvers) ∧ (∀ u ∈ U, u ∉ P.R16.reviewers) ∧ (∀ u ∈ U, u ∉ P.R16.approvers) ∧
       (∀ u ∈ U, u ∉ P.admins28)⟩,
   ⟨"LAB.runtime_correspondence: the deployed gates, shared counter, halt bit and deputy implement labStep",
     .correspondence, True⟩,
   ⟨"LAB.price_metered: compute spend = price × trusted-meter charge (F5 measurement)", .measurement, True⟩,
   ⟨"LAB.safety: component Goods + global budget + provenance", .proofObligation "ControlStack.LabStack.lab_safe",
     True⟩]

/-- the lab stack certificate: its claims hold whenever its premises do -/
def labStack (P : LabParams) (U : List ℕ) (ops : List (ℕ × LabOp)) : Stack :=
  ⟨labPremises P U ops,
   [("SC-26 Good", SC26.Good P.R26 P.cap26 (authRun (labStep P true) labClaim labInit ops).pay),
    ("SC-16 Good", SC16.Good P.R16 P.h (authRun (labStep P true) labClaim labInit ops).dep),
    ("SC-28 Good", SC28.Good P.G28 (authRun (labStep P true) labClaim labInit ops).comp),
    ("global budget", ((authRun (labStep P true) labClaim labInit ops).pay.bank.map (fun e => e.2.amount)).sum +
      P.price * SC28.usedT (authRun (labStep P true) labClaim labInit ops).comp ≤ P.G)],
   fun hp c hc => by
    obtain ⟨-, hp⟩ := hp.cons
    obtain ⟨hl, hp⟩ := hp.cons
    obtain ⟨⟨h1, h2, h3, h4⟩, -⟩ := hp.cons
    obtain ⟨g26, g16, g28, gb, -⟩ := lab_safe P U ops hl h1 h2 h3 h4
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact g26
    · exact g16
    · exact g28
    · exact gb⟩

/-- the lab's typed ledger (closed, printable) -/
def labLedger : List (String × PremiseKind) :=
  [("LAB.issuer_authentic: the platform-reported identity is the issuer (modelled by authRun)", .environment),
   ("LAB.legal: no untrusted bank call with the gate credential; no privileged counter rollback", .environment),
   ("LAB.adversary_outside_roles: adversary issuers hold no approver, reviewer or admin role", .organisational),
   ("LAB.runtime_correspondence: the deployed gates, shared counter, halt bit and deputy implement labStep",
     .correspondence),
   ("LAB.price_metered: compute spend = price × trusted-meter charge (F5 measurement)", .measurement),
   ("LAB.safety: component Goods + global budget + provenance", .proofObligation "ControlStack.LabStack.lab_safe")]

theorem lab_ledger_eq (P : LabParams) (U : List ℕ) (ops : List (ℕ × LabOp)) :
    typedLedger (labStack P U ops).premises = labLedger := rfl

end ControlStack.LabStack

#print axioms ControlStack.LabStack.lab_safe
#print axioms ControlStack.LabStack.global_budget
#print axioms ControlStack.LabStack.lab_halt_freezes
#print axioms ControlStack.LabStack.component_halt_shared
#print axioms ControlStack.LabStack.deputy_admissible
#print axioms ControlStack.LabStack.separate_caps_exceed_global
#print axioms ControlStack.LabStack.deputy_reuse_breaks_sc26
#print axioms ControlStack.LabStack.no_shared_halt_keeps_running
#print axioms ControlStack.LabStack.lab_ledger_eq
