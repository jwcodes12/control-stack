/-
SC-26: no irreversible transaction without an exact, independent, one-use approval.

One JOINT shared-state transition system covers the families the scenario needs (RUNTIME-VM-HANDOFF.md §6, F8 "one
actual shared-state transition per effect"):
- F1: the only effect path is the gate's delivery to the external system, which accepts only the gate's credential;
- F3: an absorbing HALT issued by an admin freezes approvals, executions and deliveries;
- F5: a global spending cap, charged once per reservation;
- F7: an approval binds the exact payload, comes from an approver distinct from the requester, and is consumed once;
- the external system (the "bank") is idempotent per key, so crash/retry delivery is exactly-once at the bank.

The adversary chooses ANY finite sequence of operations: requests, approvals, executions, delivery retries (which also
model crash recovery: a retry may happen any number of times, in any order), direct calls to the bank, and halts. Every
caller identity is arbitrary except one formal premise: no untrusted operation carries the gate's own credential
(`legal`). The model does not distinguish who ISSUES an operation from the caller identity it carries: an `approve`
with an approver's identity is read as that approver's genuine act. So "approved by an approver" means consent only
under credential separation for approvers and admins too; that is a runtime premise (OS identity via SO_PEERCRED,
private credentials), enforced and tested in the harness, not a theorem (adversarial review, Gemini, 2026-10-09).
The cap bounds the total AMOUNT; zero-amount payments are not capped in number, but each still needs its own exact
approval.

Main results:
- `sc26_safe`: from the initial state, after any legal trace, every bank entry has a request with exactly that payload,
  a reservation, and an approval of exactly that payload by an approver who is not the requester; bank keys are
  unique; the bank's total amount is at most the cap.
- `safe_of_sound`: the same for EVERY configuration with the payload, distinctness, cap, receiver-dedup and
  receiver-authentication checks; `good_without_nonce`: the gate-side nonce is not needed for safety.
- `sc26_once`: in the deployed configuration each request id is reserved and charged at most once.
- `sc26_safe_disjoint`: with disjoint agent/approver roles, every payment's approver is not an agent.
- `halt_freezes`: after a halt the gate sends nothing new; the bank gains only messages already in flight at the halt
  (`inflight_after_halt` shows they can still complete; `halt_freezes_quiescent`: with nothing in flight, the bank is
  frozen exactly).
- `sys`/`spec`: the model is a client of the shared gate interface (`Core/Gate.lean`).

Necessity witnesses (each removes one check or premise and exhibits a concrete bad trace):
`payload_unchecked_breaks`, `no_dedup_retry_duplicates`, `no_dedup_breaks_cap`, `no_cap_breaks`,
`no_halt_check_breaks`, `no_bank_auth_breaks`, `gate_credential_leak_breaks`, `self_approval_without_distinct_check`
(the distinctness check matters only when roles overlap). `same_payload_twice_is_good` records that exactly-once is
per request id, not per business intent. `execute` does not check its caller (any principal may trigger execution of
an approved request; harmless for `Good`). `nonce_protects_budget_only` records an honest
nuance: with an idempotent bank the gate-side nonce is not needed for effect uniqueness; it protects budget accounting.

Limits: this is the transition system. The runtime (`scenarios/SC-26/harness/`) is linked to it by a trace checker
(`scenarios/SC-26/harness/model.py`, differential-tested against this file's `#eval`), not by a refinement proof.
Credential separation, OS integrity, durable storage and the meaning of "consent" are premises (see
`scenarios/SC-26/correspondence.md`). Nothing here is new mathematics: each theorem is an induction over the trace.
-/
import Mathlib.Tactic
import ControlStack.Core.Gate

namespace ControlStack.SC26

open ControlStack.Gate

/-- a transaction payload: destination account, amount, memo digest -/
structure Tx where
  dest : ℕ
  amount : ℕ
  memo : ℕ
deriving DecidableEq, Repr

/-- trusted role assignment (by OS identity); `gate` is the gate's own credential, the only one the bank accepts -/
structure Roles where
  agents : List ℕ
  approvers : List ℕ
  admins : List ℕ
  gate : ℕ

structure Req where
  id : ℕ
  requester : ℕ
  tx : Tx
deriving DecidableEq, Repr

structure St where
  next : ℕ
  reqs : List Req
  /-- (request id, approver, payload the approver approved) -/
  approvals : List (ℕ × ℕ × Tx)
  reserved : List ℕ
  spent : ℕ
  halted : Bool
  /-- the external system's ledger: (idempotency key, payload) -/
  bank : List (ℕ × Tx)
  /-- messages the gate has sent to the external system; each may arrive any number of times, at any later time -/
  net : List (ℕ × Tx)
deriving DecidableEq, Repr

inductive Op where
  | request (caller : ℕ) (tx : Tx)
  | approve (caller : ℕ) (id : ℕ) (tx : Tx)
  | execute (caller : ℕ) (id : ℕ)
  /-- the gate (re)sends a reserved transaction to the external system: first attempt, retry or crash recovery -/
  | deliver (id : ℕ)
  /-- the external system processes a message in flight (not under the gate's control; not stopped by HALT) -/
  | arrive (key : ℕ)
  /-- a direct call to the external system by `caller` -/
  | bankCall (caller : ℕ) (key : ℕ) (tx : Tx)
  | halt (caller : ℕ)
deriving DecidableEq, Repr

/-- which checks the implementation performs; `full` is the deployed configuration -/
structure Checks where
  distinct : Bool
  payload : Bool
  nonce : Bool
  cap : Bool
  haltCheck : Bool
  bankDedup : Bool
  bankAuth : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true, true, true, true⟩

/-- the checks the SAFETY property needs. The gate-side nonce and the halt check are not among them: with an
idempotent receiver, uniqueness of effects comes from the receiver (adversarial review, Opus 5.5, D4). -/
structure Sound (C : Checks) : Prop where
  distinct : C.distinct = true
  payload : C.payload = true
  cap : C.cap = true
  dedup : C.bankDedup = true
  auth : C.bankAuth = true

theorem sound_full : Sound full := ⟨rfl, rfl, rfl, rfl, rfl⟩

def init : St := ⟨0, [], [], [], 0, false, [], []⟩

def reqOf (s : St) (id : ℕ) : Option Req := s.reqs.find? (fun r => r.id = id)

/-- the external system appends an entry unless (when idempotent) the key is already present -/
def bankAppend (C : Checks) (s : St) (key : ℕ) (tx : Tx) : St :=
  if C.bankDedup ∧ key ∈ s.bank.map Prod.fst then s else { s with bank := s.bank ++ [(key, tx)] }

def step (R : Roles) (cap : ℕ) (C : Checks) (s : St) : Op → St
  | .request c tx =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ R.agents then { s with reqs := s.reqs ++ [⟨s.next, c, tx⟩], next := s.next + 1 } else s
  | .approve c id tx =>
    if s.halted ∧ C.haltCheck then s
    else match reqOf s id with
      | none => s
      | some r =>
        if c ∈ R.approvers ∧ (C.distinct → c ≠ r.requester) ∧ (C.payload → tx = r.tx) then
          { s with approvals := s.approvals ++ [(id, c, tx)] }
        else s
  | .execute _ id =>
    if s.halted ∧ C.haltCheck then s
    else match reqOf s id with
      | none => s
      | some r =>
        if (∃ ap ∈ s.approvals, ap.1 = id) ∧ (C.nonce → id ∉ s.reserved) ∧ (C.cap → s.spent + r.tx.amount ≤ cap) then
          { s with reserved := s.reserved ++ [id], spent := s.spent + r.tx.amount }
        else s
  | .deliver id =>
    if s.halted ∧ C.haltCheck then s
    else if id ∈ s.reserved then
      match reqOf s id with
      | none => s
      | some r => { s with net := s.net ++ [(id, r.tx)] }
    else s
  | .arrive key =>
    match s.net.find? (fun m => m.1 = key) with
    | none => s
    | some m => bankAppend C s m.1 m.2
  | .bankCall c key tx => if C.bankAuth ∧ c ≠ R.gate then s else bankAppend C s key tx
  | .halt c => if c ∈ R.admins then { s with halted := true } else s

def run (R : Roles) (cap : ℕ) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step R cap C) s

/-- untrusted operations never carry the gate's credential (credential separation, a correspondence premise) -/
def legal (R : Roles) : Op → Prop
  | .bankCall c _ _ => c ≠ R.gate
  | _ => True

/-! ## The invariant -/

/-- an approval of exactly `r`'s payload, by an approver who is not `r`'s requester -/
def Approved (R : Roles) (s : St) (k : ℕ) (r : Req) : Prop :=
  ∃ a, (k, a, r.tx) ∈ s.approvals ∧ a ∈ R.approvers ∧ a ≠ r.requester

def amt (s : St) (k : ℕ) : ℕ := ((reqOf s k).map (fun r => r.tx.amount)).getD 0

structure Inv (R : Roles) (cap : ℕ) (s : St) : Prop where
  appr_ok : ∀ ap ∈ s.approvals, ∃ r, reqOf s ap.1 = some r ∧ ap.2.2 = r.tx ∧ ap.2.1 ∈ R.approvers ∧
    ap.2.1 ≠ r.requester
  res_ok : ∀ k ∈ s.reserved, ∃ r, reqOf s k = some r ∧ Approved R s k r
  spent_eq : s.spent = (s.reserved.map (amt s)).sum
  spent_le : s.spent ≤ cap
  bank_ok : ∀ e ∈ s.bank, e.1 ∈ s.reserved ∧ ∃ r, reqOf s e.1 = some r ∧ r.tx = e.2
  bank_nodup : (s.bank.map Prod.fst).Nodup
  net_ok : ∀ m ∈ s.net, m.1 ∈ s.reserved ∧ ∃ r, reqOf s m.1 = some r ∧ r.tx = m.2

/-- the safety property: every effect is exactly approved, keys are unique, the total is within the cap -/
def Good (R : Roles) (cap : ℕ) (s : St) : Prop :=
  (∀ e ∈ s.bank, ∃ r, reqOf s e.1 = some r ∧ r.tx = e.2 ∧ e.1 ∈ s.reserved ∧ Approved R s e.1 r) ∧
  (s.bank.map Prod.fst).Nodup ∧ (s.bank.map (fun e => e.2.amount)).sum ≤ cap

theorem reqOf_append (s : St) (l : List Req) (k : ℕ) (r : Req) (h : reqOf s k = some r) :
    reqOf { s with reqs := s.reqs ++ l } k = some r := by
  simp only [reqOf] at h ⊢
  simp [List.find?_append, h]

theorem inv_init (R : Roles) (cap : ℕ) : Inv R cap init :=
  ⟨by simp [init], by simp [init], by simp [init], by simp [init], by simp [init], by simp [init], by simp [init]⟩

/-- states whose request lookups and approvals extend `s`'s -/
structure Ext (s t : St) : Prop where
  req : ∀ k r, reqOf s k = some r → reqOf t k = some r
  appr : s.approvals ⊆ t.approvals

theorem Approved.mono {R : Roles} {s t : St} {k : ℕ} {r : Req} (h : Ext s t) (ha : Approved R s k r) :
    Approved R t k r := by
  obtain ⟨a, h1, h2, h3⟩ := ha
  exact ⟨a, h.appr h1, h2, h3⟩

theorem amt_ext {s t : St} (h : Ext s t) (k : ℕ) (hk : ∃ r, reqOf s k = some r) : amt t k = amt s k := by
  obtain ⟨r, hr⟩ := hk
  simp [amt, hr, h.req k r hr]

theorem sum_ext {s t : St} (h : Ext s t) (l : List ℕ) (hl : ∀ k ∈ l, ∃ r, reqOf s k = some r) :
    (l.map (amt t)).sum = (l.map (amt s)).sum := by
  congr 1
  exact List.map_congr_left (fun k hk => amt_ext h k (hl k hk))

/-- the bank's total equals the sum of `amt` over its keys -/
theorem bank_sum (s : St) (hb : ∀ e ∈ s.bank, ∃ r, reqOf s e.1 = some r ∧ r.tx = e.2) :
    (s.bank.map (fun e => e.2.amount)).sum = ((s.bank.map Prod.fst).map (amt s)).sum := by
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro e he
  obtain ⟨r, hr, hx⟩ := hb e he
  simp [amt, hr, hx]

theorem sum_le_of_subperm (f : ℕ → ℕ) (l₁ l₂ : List ℕ) (h : List.Subperm l₁ l₂) : (l₁.map f).sum ≤ (l₂.map f).sum := by
  obtain ⟨l, hp, hs⟩ := h
  rw [← (hp.map f).sum_eq]
  exact (hs.map f).sum_le_sum (fun _ _ => Nat.zero_le _)

theorem Inv.good {R : Roles} {cap : ℕ} {s : St} (h : Inv R cap s) : Good R cap s := by
  refine ⟨?_, h.bank_nodup, ?_⟩
  · intro e he
    obtain ⟨hres, r, hr, hx⟩ := h.bank_ok e he
    obtain ⟨r', hr', ha⟩ := h.res_ok e.1 hres
    rw [hr] at hr'
    cases hr'
    exact ⟨r, hr, hx, hres, ha⟩
  · rw [bank_sum s (fun e he => (h.bank_ok e he).2)]
    have hsub : List.Subperm (s.bank.map Prod.fst) s.reserved :=
      List.Nodup.subperm h.bank_nodup (fun k hk => by
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hk
        exact (h.bank_ok e he).1)
    calc _ ≤ (s.reserved.map (amt s)).sum := sum_le_of_subperm _ _ _ hsub
      _ = s.spent := h.spent_eq.symm
      _ ≤ cap := h.spent_le

/-- a step that extends requests and approvals (validly) and changes neither reservations, spending nor the bank -/
theorem inv_of_ext {R : Roles} {cap : ℕ} {s t : St} (h : Inv R cap s) (he : Ext s t)
    (happr : ∀ ap ∈ t.approvals, ap ∉ s.approvals →
      ∃ r, reqOf t ap.1 = some r ∧ ap.2.2 = r.tx ∧ ap.2.1 ∈ R.approvers ∧ ap.2.1 ≠ r.requester)
    (hres : t.reserved = s.reserved) (hsp : t.spent = s.spent) (hbank : t.bank = s.bank) (hnet : t.net = s.net) :
    Inv R cap t := by
  have hreq : ∀ k ∈ s.reserved, ∃ r, reqOf s k = some r := fun k hk =>
    let ⟨r, hr, _⟩ := h.res_ok k hk; ⟨r, hr⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ap hap
    by_cases hs : ap ∈ s.approvals
    · obtain ⟨r, hr, h1⟩ := h.appr_ok ap hs
      exact ⟨r, he.req _ r hr, h1⟩
    · exact happr ap hap hs
  · intro k hk
    rw [hres] at hk
    obtain ⟨r, hr, ha⟩ := h.res_ok k hk
    exact ⟨r, he.req k r hr, ha.mono he⟩
  · rw [hsp, hres, sum_ext he s.reserved hreq]; exact h.spent_eq
  · rw [hsp]; exact h.spent_le
  · intro e hb
    rw [hbank] at hb
    obtain ⟨h1, r, hr, hx⟩ := h.bank_ok e hb
    exact ⟨hres ▸ h1, r, he.req _ r hr, hx⟩
  · rw [hbank]; exact h.bank_nodup
  · intro m hm
    rw [hnet] at hm
    obtain ⟨h1, r, hr, hx⟩ := h.net_ok m hm
    exact ⟨hres ▸ h1, r, he.req _ r hr, hx⟩

theorem ext_refl (s : St) : Ext s s := ⟨fun _ _ h => h, fun _ h => h⟩

theorem bankAppend_inv {R : Roles} {cap : ℕ} {C : Checks} (hdd : C.bankDedup = true) {s : St} (h : Inv R cap s)
    (k : ℕ) (r : Req) (hk : k ∈ s.reserved) (hr : reqOf s k = some r) : Inv R cap (bankAppend C s k r.tx) := by
  unfold bankAppend
  by_cases hd : k ∈ s.bank.map Prod.fst
  · simpa [hdd, hd] using h
  · simp only [hdd, true_and, hd, ite_false]
    refine ⟨h.appr_ok, h.res_ok, h.spent_eq, h.spent_le, ?_, ?_, h.net_ok⟩
    · intro e he
      rcases List.mem_append.1 he with he | he
      · exact h.bank_ok e he
      · simp at he; subst he; exact ⟨hk, r, hr, rfl⟩
    · simp only [List.map_append, List.map_cons, List.map_nil]
      refine List.nodup_append.2 ⟨h.bank_nodup, List.nodup_singleton _, fun a ha b hb => ?_⟩
      simp only [List.mem_singleton] at hb
      subst hb
      rintro rfl
      exact hd ha

theorem step_inv (R : Roles) (cap : ℕ) {C : Checks} (hC : Sound C) (s : St) (o : Op) (ho : legal R o)
    (h : Inv R cap s) : Inv R cap (step R cap C s o) := by
  cases o with
  | request c tx =>
    simp only [step]
    split_ifs with h1 h2
    · exact h
    · exact inv_of_ext h ⟨fun k r hr => reqOf_append s _ k r hr, fun _ h => h⟩
        (fun ap hap hn => absurd hap hn) rfl rfl rfl rfl
    · exact h
  | approve c id tx =>
    simp only [step]
    split_ifs with h1
    · exact h
    · split
      · exact h
      · rename_i r hr
        split_ifs with h2
        · obtain ⟨hc, hd, hp⟩ := h2
          simp only [hC.distinct, hC.payload, forall_const] at hd hp
          refine inv_of_ext h ⟨fun _ _ hr => hr, fun _ hx => List.mem_append_left _ hx⟩ ?_ rfl rfl rfl rfl
          intro ap hap hn
          rcases List.mem_append.1 hap with hap | hap
          · exact absurd hap hn
          · simp at hap; subst hap; exact ⟨r, hr, hp, hc, hd⟩
        · exact h
  | execute c id =>
    simp only [step]
    split_ifs with h1
    · exact h
    · split
      · exact h
      · rename_i r hr
        split_ifs with h2
        · obtain ⟨⟨ap, hap, hid⟩, hn, hc⟩ := h2
          simp only [hC.cap, forall_const] at hc
          obtain ⟨r', hr', htx, happ, hne⟩ := h.appr_ok ap hap
          rw [hid, hr] at hr'
          cases hr'
          have happroved : Approved R s id r := ⟨ap.2.1, by
            obtain ⟨k, a, t⟩ := ap; simp only at hid htx; subst hid htx; exact hap, happ, hne⟩
          refine ⟨h.appr_ok, ?_, ?_, ?_, ?_, h.bank_nodup, ?_⟩
          · intro k hk
            rcases List.mem_append.1 hk with hk | hk
            · exact h.res_ok k hk
            · simp at hk; subst hk; exact ⟨r, hr, happroved⟩
          · show s.spent + r.tx.amount = ((s.reserved ++ [id]).map (amt s)).sum
            rw [List.map_append, List.sum_append, ← h.spent_eq]
            simp [amt, hr]
          · exact hc
          · intro e he
            obtain ⟨h1, h2⟩ := h.bank_ok e he
            exact ⟨List.mem_append_left _ h1, h2⟩
          · intro m hm
            obtain ⟨h1, h2⟩ := h.net_ok m hm
            exact ⟨List.mem_append_left _ h1, h2⟩
        · exact h
  | deliver id =>
    simp only [step]
    split_ifs with h1 h2
    · exact h
    · split
      · exact h
      · rename_i r hr
        refine ⟨h.appr_ok, h.res_ok, h.spent_eq, h.spent_le, h.bank_ok, h.bank_nodup, ?_⟩
        intro m hm
        rcases List.mem_append.1 hm with hm | hm
        · exact h.net_ok m hm
        · simp at hm; subst hm; exact ⟨h2, r, hr, rfl⟩
    · exact h
  | arrive key =>
    simp only [step]
    split
    · exact h
    · rename_i m hm
      have hmem : m ∈ s.net := List.mem_of_find?_eq_some hm
      obtain ⟨h1, r, hr, hx⟩ := h.net_ok m hmem
      rw [← hx]
      exact bankAppend_inv hC.dedup h m.1 r h1 hr
  | bankCall c key tx =>
    simp only [legal] at ho
    simpa [step, hC.auth, ho] using h
  | halt c =>
    simp only [step]
    split_ifs
    · exact inv_of_ext h ⟨fun _ _ hr => hr, fun _ hx => hx⟩ (fun ap hap hn => absurd hap hn) rfl rfl rfl rfl
    · exact h

theorem run_cons (R : Roles) (cap : ℕ) (C : Checks) (s : St) (o : Op) (ops : List Op) :
    run R cap C s (o :: ops) = run R cap C (step R cap C s o) ops := rfl

theorem run_inv (R : Roles) (cap : ℕ) {C : Checks} (hC : Sound C) (s : St) (ops : List Op)
    (hops : ∀ o ∈ ops, legal R o) (h : Inv R cap s) : Inv R cap (run R cap C s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih =>
    rw [run_cons]
    exact ih _ (fun o' ho' => hops o' (List.mem_cons_of_mem o ho'))
      (step_inv R cap hC s o (hops o List.mem_cons_self) h)

/-- **Safety for every sound configuration.** The theorem needs only the payload, distinctness, cap, receiver-dedup
and receiver-authentication checks; neither the gate-side nonce nor the halt check is needed for `Good`. -/
theorem safe_of_sound (R : Roles) (cap : ℕ) {C : Checks} (hC : Sound C) (ops : List Op)
    (hops : ∀ o ∈ ops, legal R o) : Good R cap (run R cap C init ops) :=
  (run_inv R cap hC init ops hops (inv_init R cap)).good

/-- the gate-side nonce is not needed for safety (it protects budget accounting: `nonce_protects_budget_only`) -/
theorem good_without_nonce (R : Roles) (cap : ℕ) (ops : List Op) (hops : ∀ o ∈ ops, legal R o) :
    Good R cap (run R cap { full with nonce := false } init ops) :=
  safe_of_sound R cap ⟨rfl, rfl, rfl, rfl, rfl⟩ ops hops

/-- **SC-26 safety.** After any legal trace from the initial state, every bank entry has a request with exactly that
payload, a reservation, and an approval of exactly that payload by an approver who is not the requester; bank keys
are unique; the bank's total is at most the cap. Adversary: any legal operation sequence (stateful, adaptive,
including arbitrary delivery retries, crash recovery, duplicated or delayed messages). Formal premise: `legal` (no
untrusted operation carries the gate's credential). Reading "approved by an approver" as CONSENT additionally needs
credential separation for approvers (an `approve` carrying an approver identity is that approver's own act) and, for
independence, role disjointness (`sc26_safe_disjoint`). Exactly-once is per request id, not per business intent
(`same_payload_twice_is_good`); uniqueness of effects relies on the receiver's idempotency (`no_dedup_breaks_cap`). -/
theorem sc26_safe (R : Roles) (cap : ℕ) (ops : List Op) (hops : ∀ o ∈ ops, legal R o) :
    Good R cap (run R cap full init ops) :=
  safe_of_sound R cap sound_full ops hops

/-- with disjoint agent and approver roles, every payment's approver is not an agent at all -/
theorem sc26_safe_disjoint (R : Roles) (cap : ℕ) (hdisj : ∀ a ∈ R.approvers, a ∉ R.agents) (ops : List Op)
    (hops : ∀ o ∈ ops, legal R o) :
    ∀ e ∈ (run R cap full init ops).bank, ∃ r a, reqOf (run R cap full init ops) e.1 = some r ∧ r.tx = e.2 ∧
      (e.1, a, e.2) ∈ (run R cap full init ops).approvals ∧ a ∈ R.approvers ∧ a ∉ R.agents ∧ a ≠ r.requester := by
  intro e he
  obtain ⟨r, hr, hx, _, a, ha, happ, hne⟩ := (sc26_safe R cap ops hops).1 e he
  exact ⟨r, a, hr, hx, hx ▸ ha, happ, hdisj a happ, hne⟩

theorem bankAppend_reserved (C : Checks) (s : St) (k : ℕ) (tx : Tx) : (bankAppend C s k tx).reserved = s.reserved := by
  unfold bankAppend; split_ifs <;> rfl

/-- with the nonce check, a reservation (an approval's consumption) happens at most once per request id -/
theorem step_res_nodup (R : Roles) (cap : ℕ) (C : Checks) (hn : C.nonce = true) (s : St) (o : Op)
    (h : s.reserved.Nodup) : (step R cap C s o).reserved.Nodup := by
  cases o with
  | execute c id =>
    simp only [step]
    split_ifs with h1
    · exact h
    · split
      · exact h
      · split_ifs with h2
        · obtain ⟨_, hn', _⟩ := h2
          have hni : id ∉ s.reserved := hn' hn
          refine List.nodup_append.2 ⟨h, List.nodup_singleton _, fun a ha b hb => ?_⟩
          simp only [List.mem_singleton] at hb
          subst hb
          rintro rfl
          exact hni ha
        · exact h
  | arrive key =>
    simp only [step]; split
    · exact h
    · rw [bankAppend_reserved]; exact h
  | bankCall c key tx =>
    simp only [step]; split_ifs
    · exact h
    · rw [bankAppend_reserved]; exact h
  | request c tx => simp only [step]; split_ifs <;> exact h
  | approve c id tx =>
    simp only [step]; split_ifs
    · exact h
    · split
      · exact h
      · split_ifs <;> exact h
  | deliver id =>
    simp only [step]; split_ifs
    · exact h
    · split <;> exact h
    · exact h
  | halt c => simp only [step]; split_ifs <;> exact h

/-- **One use per approval** (deployed configuration): each request id is reserved, and charged, at most once -/
theorem sc26_once (R : Roles) (cap : ℕ) (ops : List Op) : (run R cap full init ops).reserved.Nodup := by
  suffices ∀ s, s.reserved.Nodup → (run R cap full s ops).reserved.Nodup from this init (by simp [init])
  induction ops with
  | nil => exact fun s h => h
  | cons o ops ih => exact fun s h => ih _ (step_res_nodup R cap full rfl s o h)

/-! ## Absorbing halt -/

theorem bankAppend_mem (C : Checks) (s : St) (k : ℕ) (tx : Tx) (e : ℕ × Tx) (he : e ∈ (bankAppend C s k tx).bank) :
    e ∈ s.bank ∨ e = (k, tx) := by
  unfold bankAppend at he
  split_ifs at he
  · exact Or.inl he
  · rcases List.mem_append.1 he with h | h
    · exact Or.inl h
    · simp at h; exact Or.inr h

/-- one step from a halted state: the gate sends nothing new, stays halted, and the bank gains only messages already
in flight -/
theorem step_halted (R : Roles) (cap : ℕ) (s : St) (o : Op) (ho : legal R o) (hh : s.halted = true) :
    (step R cap full s o).net = s.net ∧ (step R cap full s o).halted = true ∧
      ∀ e ∈ (step R cap full s o).bank, e ∈ s.bank ∨ e ∈ s.net := by
  cases o with
  | bankCall c key tx =>
    simp only [legal] at ho
    have : step R cap full s (.bankCall c key tx) = s := by simp [step, full, ho]
    rw [this]
    exact ⟨rfl, hh, fun e he => Or.inl he⟩
  | halt c =>
    simp only [step]
    split_ifs
    · exact ⟨rfl, rfl, fun e he => Or.inl he⟩
    · exact ⟨rfl, hh, fun e he => Or.inl he⟩
  | arrive key =>
    simp only [step]
    split
    · exact ⟨rfl, hh, fun e he => Or.inl he⟩
    · rename_i m hm
      refine ⟨by unfold bankAppend; split_ifs <;> rfl, by unfold bankAppend; split_ifs <;> exact hh, ?_⟩
      intro e he
      rcases bankAppend_mem _ _ _ _ e he with h | h
      · exact Or.inl h
      · right; rw [h]; exact List.mem_of_find?_eq_some hm
  | _ => simp only [step, full, hh, and_self, ite_true]; exact ⟨trivial, trivial, fun e he => Or.inl he⟩

/-- **HALT freezes what the gate sends.** Once halted, after any legal trace, every bank entry was already in the bank
or already in flight when the halt was processed; no new message is sent. In-flight messages may still complete
(`inflight_after_halt`): HALT stops initiation, not delivery of what was already sent. -/
theorem halt_freezes (R : Roles) (cap : ℕ) (s : St) (ops : List Op) (hops : ∀ o ∈ ops, legal R o)
    (hh : s.halted = true) :
    (run R cap full s ops).net = s.net ∧ ∀ e ∈ (run R cap full s ops).bank, e ∈ s.bank ∨ e ∈ s.net := by
  induction ops generalizing s with
  | nil => exact ⟨rfl, fun e he => Or.inl he⟩
  | cons o ops ih =>
    rw [run_cons]
    obtain ⟨h1, h2, h3⟩ := step_halted R cap s o (hops o List.mem_cons_self) hh
    obtain ⟨ih1, ih2⟩ := ih _ (fun o' ho' => hops o' (List.mem_cons_of_mem o ho')) h2
    refine ⟨ih1.trans h1, fun e he => ?_⟩
    rcases ih2 e he with h | h
    · exact h3 e h
    · right; rw [← h1]; exact h

/-- with nothing in flight at the halt, the bank is frozen exactly -/
theorem halt_freezes_quiescent (R : Roles) (cap : ℕ) (s : St) (ops : List Op) (hops : ∀ o ∈ ops, legal R o)
    (hh : s.halted = true) (hq : ∀ m ∈ s.net, m ∈ s.bank) :
    ∀ e ∈ (run R cap full s ops).bank, e ∈ s.bank := fun e he =>
  ((halt_freezes R cap s ops hops hh).2 e he).elim id (hq e)

/-! ## Client of the shared gate interface -/

theorem bankAppend_prefix (C : Checks) (s : St) (k : ℕ) (tx : Tx) : s.bank <+: (bankAppend C s k tx).bank := by
  unfold bankAppend
  split_ifs
  · exact List.prefix_refl _
  · exact List.prefix_append _ _

theorem bank_prefix (R : Roles) (cap : ℕ) (C : Checks) (s : St) (o : Op) : s.bank <+: (step R cap C s o).bank := by
  cases o with
  | request c tx => simp only [step]; split_ifs <;> exact List.prefix_refl _
  | approve c id tx =>
    simp only [step]; split_ifs
    · exact List.prefix_refl _
    · split
      · exact List.prefix_refl _
      · split_ifs <;> exact List.prefix_refl _
  | execute c id =>
    simp only [step]; split_ifs
    · exact List.prefix_refl _
    · split
      · exact List.prefix_refl _
      · split_ifs <;> exact List.prefix_refl _
  | deliver id =>
    simp only [step]; split_ifs
    · exact List.prefix_refl _
    · split
      · exact List.prefix_refl _
      · exact List.prefix_refl _
    · exact List.prefix_refl _
  | arrive key =>
    simp only [step]; split
    · exact List.prefix_refl _
    · exact bankAppend_prefix _ _ _ _
  | bankCall c key tx =>
    simp only [step]; split_ifs
    · exact List.prefix_refl _
    · exact bankAppend_prefix _ _ _ _
  | halt c => simp only [step]; split_ifs <;> exact List.prefix_refl _

/-- the SC-26 gate as a `Gate.System` over legal operations; its effect log is the bank ledger -/
def sys (R : Roles) (cap : ℕ) : System St {o : Op // legal R o} (ℕ × Tx) where
  step := fun s o => step R cap full s o.1
  effects := St.bank

def spec (R : Roles) (cap : ℕ) : Spec (sys R cap) where
  Inv := Inv R cap
  ok := fun s e => ∃ r, reqOf s e.1 = some r ∧ r.tx = e.2 ∧ e.1 ∈ s.reserved ∧ Approved R s e.1 r
  step_inv := fun s o h => step_inv R cap sound_full s o.1 o.2 h
  log_prefix := fun s o => bank_prefix R cap full s o.1
  inv_ok := fun _ h e he => h.good.1 e he

/-! ## Non-vacuity and necessity witnesses

Roles: agent 1, approver 2, admin 3, gate credential 9. -/

def R0 : Roles := ⟨[1], [2], [3], 9⟩
def tx1 : Tx := ⟨5, 10, 0⟩
def tx2 : Tx := ⟨6, 10, 0⟩

/-- an effect without an approval of exactly its payload violates `Good` -/
theorem not_good_of {R : Roles} {cap : ℕ} {s : St} (e : ℕ × Tx) (he : e ∈ s.bank)
    (hn : ∀ ap ∈ s.approvals, ap.1 = e.1 → ap.2.2 = e.2 → ap.2.1 ∈ R.approvers → False) : ¬ Good R cap s := by
  intro hg
  obtain ⟨r, _, hx, _, a, ha, happ, _⟩ := hg.1 e he
  exact hn _ ha rfl hx happ

/-- **Non-vacuity**: the honest path pays, exactly once even with a crash-recovery retry. -/
theorem honest_trace_pays :
    (run R0 20 full init [.request 1 tx1, .approve 2 0 tx1, .execute 1 0, .deliver 0, .arrive 0, .deliver 0, .arrive 0, .arrive 0]).bank =
      [(0, tx1)] := by decide

/-- without the payload check, an approval of `tx2` releases `tx1` -/
theorem payload_unchecked_breaks :
    let s := run R0 20 { full with payload := false } init
      [.request 1 tx1, .approve 2 0 tx2, .execute 1 0, .deliver 0, .arrive 0]
    s.bank = [(0, tx1)] ∧ s.approvals = [(0, 2, tx2)] ∧ ¬ Good R0 20 s := by
  refine ⟨by decide, by decide, not_good_of (0, tx1) (by decide) ?_⟩
  have : (run R0 20 { full with payload := false } init
      [.request 1 tx1, .approve 2 0 tx2, .execute 1 0, .deliver 0, .arrive 0]).approvals = [(0, 2, tx2)] := by decide
  rw [this]
  intro ap hap _ h2 _
  simp at hap; subst hap; simp [tx1, tx2] at h2

/-- without an idempotent external system, a crash-recovery retry pays twice -/
theorem no_dedup_retry_duplicates :
    let s := run R0 20 { full with bankDedup := false } init
      [.request 1 tx1, .approve 2 0 tx1, .execute 1 0, .deliver 0, .arrive 0, .arrive 0]
    s.bank = [(0, tx1), (0, tx1)] ∧ ¬ Good R0 20 s := by
  refine ⟨by decide, fun hg => ?_⟩
  have h := hg.2.1
  have : (run R0 20 { full with bankDedup := false } init
      [.request 1 tx1, .approve 2 0 tx1, .execute 1 0, .deliver 0, .arrive 0, .arrive 0]).bank = [(0, tx1), (0, tx1)] := by
    decide
  rw [this] at h
  simp at h

/-- without receiver idempotency, repeated arrival of ONE approved message also breaks the cap: the gate's checks alone
give neither exactly-once nor the cap (adversarial review, Opus 5.5, D4) -/
theorem no_dedup_breaks_cap :
    let s := run R0 20 { full with bankDedup := false } init
      [.request 1 tx1, .approve 2 0 tx1, .execute 1 0, .deliver 0, .arrive 0, .arrive 0, .arrive 0]
    (s.bank.map (fun e => e.2.amount)).sum = 30 ∧ s.spent = 10 := by
  decide

/-- without receiver authentication, an agent's direct call pays with no request or approval -/
theorem no_bank_auth_breaks :
    let s := run R0 20 { full with bankAuth := false } init [.bankCall 1 0 tx1]
    s.bank = [(0, tx1)] ∧ ¬ Good R0 20 s := by
  refine ⟨by decide, not_good_of (0, tx1) (by decide) ?_⟩
  intro ap hap
  have : (run R0 20 { full with bankAuth := false } init [.bankCall 1 0 tx1]).approvals = [] := by decide
  rw [this] at hap
  simp at hap

/-- **Scope of "exactly once"**: it is per request id. Two requests with the same payload, each approved, are both
paid, and `Good` holds. Business-level deduplication (one payment per invoice) is not part of the model. -/
theorem same_payload_twice_is_good :
    let ops : List Op := [.request 1 tx1, .request 1 tx1, .approve 2 0 tx1, .approve 2 1 tx1, .execute 1 0,
      .execute 1 1, .deliver 0, .deliver 1, .arrive 0, .arrive 1]
    (run R0 20 full init ops).bank = [(0, tx1), (1, tx1)] ∧ Good R0 20 (run R0 20 full init ops) :=
  ⟨by decide, sc26_safe R0 20 _ (by
    intro o ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with h | h | h | h | h | h | h | h | h | h <;> subst h <;> trivial)⟩

/-- without the cap check, two approved transactions exceed the cap -/
theorem no_cap_breaks :
    let s := run R0 10 { full with cap := false } init
      [.request 1 tx1, .request 1 tx2, .approve 2 0 tx1, .approve 2 1 tx2, .execute 1 0, .execute 1 1,
        .deliver 0, .deliver 1, .arrive 0, .arrive 1]
    (s.bank.map (fun e => e.2.amount)).sum = 20 ∧ ¬ Good R0 10 s := by
  refine ⟨by decide, fun hg => ?_⟩
  have h := hg.2.2
  have : (run R0 10 { full with cap := false } init
      [.request 1 tx1, .request 1 tx2, .approve 2 0 tx1, .approve 2 1 tx2, .execute 1 0, .execute 1 1,
        .deliver 0, .deliver 1, .arrive 0, .arrive 1]).bank.map (fun e => e.2.amount) = [10, 10] := by decide
  rw [this] at h
  simp at h

/-- without the halt check, a transaction approved before the halt is still paid after it -/
theorem no_halt_check_breaks :
    let C := { full with haltCheck := false }
    let s := run R0 20 C init [.request 1 tx1, .approve 2 0 tx1, .halt 3]
    s.halted = true ∧ s.bank = [] ∧ s.net = [] ∧ (run R0 20 C s [.execute 1 0, .deliver 0, .arrive 0]).bank = [(0, tx1)] := by
  decide

/-- with the halt check (deployed configuration), the same trace pays nothing after the halt -/
theorem halt_check_blocks :
    let s := run R0 20 full init [.request 1 tx1, .approve 2 0 tx1, .halt 3]
    (run R0 20 full s [.execute 1 0, .deliver 0, .arrive 0]).bank = [] := by
  decide

/-- **HALT does not recall in-flight messages**: a payment sent before the halt still completes after it -/
theorem inflight_after_halt :
    let s := run R0 20 full init [.request 1 tx1, .approve 2 0 tx1, .execute 1 0, .deliver 0, .halt 3]
    s.halted = true ∧ s.bank = [] ∧ (run R0 20 full s [.arrive 0]).bank = [(0, tx1)] := by
  decide

/-- if an untrusted principal holds the gate's credential, it pays without any request or approval -/
theorem gate_credential_leak_breaks :
    let s := run R0 20 full init [.bankCall 9 0 tx1]
    s.bank = [(0, tx1)] ∧ ¬ Good R0 20 s := by
  refine ⟨by decide, not_good_of (0, tx1) (by decide) ?_⟩
  intro ap hap
  have : (run R0 20 full init [.bankCall 9 0 tx1]).approvals = [] := by decide
  rw [this] at hap
  simp at hap

def R1 : Roles := ⟨[1], [1], [3], 9⟩

/-- if roles overlap and the distinctness check is off, a principal approves and pays its own request -/
theorem self_approval_without_distinct_check :
    let s := run R1 20 { full with distinct := false } init
      [.request 1 tx1, .approve 1 0 tx1, .execute 1 0, .deliver 0, .arrive 0]
    s.bank = [(0, tx1)] ∧ ¬ Good R1 20 s := by
  refine ⟨by decide, fun hg => ?_⟩
  have hb : (run R1 20 { full with distinct := false } init
      [.request 1 tx1, .approve 1 0 tx1, .execute 1 0, .deliver 0, .arrive 0]).bank = [(0, tx1)] := by decide
  obtain ⟨r, hr, _, _, a, ha, _, hne⟩ := hg.1 (0, tx1) (by rw [hb]; simp)
  have hreq : reqOf (run R1 20 { full with distinct := false } init
      [.request 1 tx1, .approve 1 0 tx1, .execute 1 0, .deliver 0, .arrive 0]) 0 = some ⟨0, 1, tx1⟩ := by decide
  have happ : (run R1 20 { full with distinct := false } init
      [.request 1 tx1, .approve 1 0 tx1, .execute 1 0, .deliver 0, .arrive 0]).approvals = [(0, 1, tx1)] := by decide
  rw [hreq] at hr
  cases hr
  rw [happ] at ha
  simp at ha
  exact hne ha

/-- with the deployed checks, the same overlapping-roles trace pays nothing -/
theorem distinct_check_blocks_self_approval :
    (run R1 20 full init [.request 1 tx1, .approve 1 0 tx1, .execute 1 0, .deliver 0, .arrive 0]).bank = [] := by
  decide

/-- **Honest nuance.** Without the gate-side nonce, an idempotent bank still pays once, but the budget is charged
twice: in this model the nonce protects budget accounting (availability), not effect uniqueness. -/
theorem nonce_protects_budget_only :
    let s := run R0 20 { full with nonce := false } init
      [.request 1 tx1, .approve 2 0 tx1, .execute 1 0, .execute 1 0, .deliver 0, .deliver 0, .arrive 0, .arrive 0]
    s.bank = [(0, tx1)] ∧ s.spent = 20 := by
  decide

end ControlStack.SC26

#print axioms ControlStack.SC26.sc26_safe
#print axioms ControlStack.SC26.halt_freezes
#print axioms ControlStack.SC26.spec
#print axioms ControlStack.SC26.honest_trace_pays
#print axioms ControlStack.SC26.payload_unchecked_breaks
#print axioms ControlStack.SC26.no_dedup_retry_duplicates
#print axioms ControlStack.SC26.no_cap_breaks
#print axioms ControlStack.SC26.no_halt_check_breaks
#print axioms ControlStack.SC26.halt_check_blocks
#print axioms ControlStack.SC26.halt_freezes_quiescent
#print axioms ControlStack.SC26.inflight_after_halt
#print axioms ControlStack.SC26.gate_credential_leak_breaks
#print axioms ControlStack.SC26.self_approval_without_distinct_check
#print axioms ControlStack.SC26.distinct_check_blocks_self_approval
#print axioms ControlStack.SC26.nonce_protects_budget_only
#print axioms ControlStack.SC26.safe_of_sound
#print axioms ControlStack.SC26.good_without_nonce
#print axioms ControlStack.SC26.sc26_safe_disjoint
#print axioms ControlStack.SC26.sc26_once
#print axioms ControlStack.SC26.no_dedup_breaks_cap
#print axioms ControlStack.SC26.no_bank_auth_breaks
#print axioms ControlStack.SC26.same_payload_twice_is_good
