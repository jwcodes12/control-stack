/-
SC-90: trusted monitoring with a finite audit budget, as a transactional gate (FLEXIBILITY TEST, not evidence).

Started from `tools/new_scenario.py` (spec `/tmp/sc90.json`, copy in `docs/flexibility-test/sc90.json`); every
declaration after the skeleton's `Payload`/`Roles`/`Checks` was written by hand.

Protocol (Redwood "trusted monitoring + audit budget"; Greenblatt et al. 2024). An agent proposes actions. A trusted
monitor records, for each request, a FLAG or PASS verdict (any verdict whatsoever: the monitor's quality is NOT
modelled, so the theorems hold for the worst monitor). A PASSed request executes. A FLAGGED request executes only if
an auditor has audited it and the audit found nothing. The auditor has a finite budget of `B` audits in total. An audit
that finds harm HALTs the gate (catch = absorbing shutdown, scaffold assumption A11). A flagged request that is not
audited (budget exhausted, or no auditor acts) simply does not execute: the protocol BLOCKS rather than defers.

Main results (all for configurations satisfying `Sound`, from `init`, over legal traces):
- `sc90_safe`: every ledger entry has a request with exactly that payload and was CLEARED (monitor PASS, or monitor FLAG
  plus an audit with no finding); ledger keys are unique; at most `B` ledger entries are flagged ones (i.e. at most
  `B` effects ever ran on the strength of an audit); a caught audit implies HALT.
- `harmful_effect_is_a_miss`: a harmful payload (ground-truth label `Payload.harm`, invisible to the gate) reaches the
  ledger only if the monitor PASSed it or the audit that cleared it reported no finding.
- `only_monitor_misses_escape`: if audits have perfect recall on harmful payloads (a PREMISE on the audit log, not a
  fact about the gate), every harmful effect is a monitor miss.
- `exhausted_blocks`: once the budget is spent, a flagged and unaudited request never executes on any legal trace.
- `halt_freezes`: with `haltCheck`, nothing is appended to the ledger after a halt (atomic delivery: this model has no
  in-flight messages).
Necessity witnesses: one per check (`no_<check>_breaks`).

NOT covered (and not expressible by `new_scenario.py`'s spec): the probability that the monitor misses (recall, false
positive rate), random or spot audits of PASSed requests, the monitor's score or threshold, the attacker's
adaptivity, audit recall below 1, the cost of blocking (usefulness), in-flight effects at HALT, and any link to the
probabilistic theorems in `AuditBudget.lean` / `DeferGame.lean` / `ReservedRecall.lean`. This file is the deterministic
gate half only. Credential separation (`legal`) is a premise: untrusted operations never carry the gate's credential;
and an op with a role's UID is read as that role's genuine act.
-/
import Mathlib.Tactic
import ControlStack.Core.Gate

set_option linter.unnecessarySeqFocus false

namespace ControlStack.SC90

open ControlStack.Gate

/-- the effect payload (`harm` is ground truth, visible to no gate check) -/
structure Payload where
  dest : ℕ
  harm : Bool
deriving DecidableEq, Repr

/-- trusted role assignment (by OS identity); `gate` is the gate's own credential, the only one the external
system accepts -/
structure Roles where
  agents : List ℕ
  monitors : List ℕ
  auditors : List ℕ
  admins : List ℕ
  gate : ℕ

structure Req where
  id : ℕ
  requester : ℕ
  p : Payload
deriving DecidableEq, Repr

structure St where
  /-- next request id (also the idempotency key) -/
  next : ℕ
  /-- absorbing HALT bit -/
  halted : Bool
  /-- the external system's append-only effect log, keyed by request id: (key, payload) -/
  ledger : List (ℕ × Payload)
  reqs : List Req
  /-- monitor log: (request id, flag) -/
  verdicts : List (ℕ × Bool)
  /-- auditor log: (request id, caught) -/
  audits : List (ℕ × Bool)
deriving DecidableEq, Repr

inductive Op where
  /-- an agent proposes an action with payload `p` -/
  | request (caller : ℕ) (p : Payload)
  /-- the trusted monitor records its flag verdict for request `id` (first verdict wins) -/
  | monitor (caller : ℕ) (id : ℕ) (flag : Bool)
  /-- an auditor spends one unit of audit budget on flagged request `id`; `caught` is the audit finding -/
  | audit (caller : ℕ) (id : ℕ) (caught : Bool)
  /-- the gate executes request `id` against the external system -/
  | execute (caller : ℕ) (id : ℕ)
  /-- a direct call to the external system by `caller` -/
  | directCall (caller : ℕ) (key : ℕ) (p : Payload)
  /-- trusted HALT by an admin (added by the generator) -/
  | halt (caller : ℕ)
deriving DecidableEq, Repr

/-- which checks the implementation performs; `full` is the deployed configuration -/
structure Checks where
  /-- execution needs a monitor verdict (control finding c1) -/
  monitorGate : Bool
  /-- a flagged request executes only after an audit that found nothing (control finding c2) -/
  auditGate : Bool
  /-- at most B audits are ever performed (control finding c3) -/
  budget : Bool
  /-- an audit that finds harm sets HALT (control finding c4) -/
  haltOnCatch : Bool
  /-- the external system accepts only the gate credential (control finding c5) -/
  auth : Bool
  /-- the external system is idempotent per key (control finding c6) -/
  dedup : Bool
  /-- every gate operation checks the HALT bit (control finding c7) -/
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := { monitorGate := true, auditGate := true, budget := true, haltOnCatch := true, auth := true, dedup := true, haltCheck := true }

/-- the checks the SAFETY property needs. `haltCheck` is not among them: it is needed only for `halt_freezes`. -/
structure Sound (C : Checks) : Prop where
  monitorGate : C.monitorGate = true
  auditGate : C.auditGate = true
  budget : C.budget = true
  haltOnCatch : C.haltOnCatch = true
  auth : C.auth = true
  dedup : C.dedup = true

theorem sound_full : Sound full := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def init : St := { next := 0, halted := false, ledger := [], reqs := [], verdicts := [], audits := [] }

def reqOf (s : St) (id : ℕ) : Option Req := s.reqs.find? (fun r => r.id = id)

/-- the external system appends an entry unless (when idempotent) the key is already present -/
def ledgerAppend (C : Checks) (s : St) (key : ℕ) (p : Payload) : St :=
  if C.dedup ∧ key ∈ s.ledger.map Prod.fst then s else { s with ledger := s.ledger ++ [(key, p)] }

/-- the gate's clearance test for request `id` under configuration `C` -/
def cleared (C : Checks) (s : St) (id : ℕ) : Prop :=
  C.monitorGate → ((id, false) ∈ s.verdicts ∨ ((id, true) ∈ s.verdicts ∧ (C.auditGate → (id, false) ∈ s.audits)))

instance (C : Checks) (s : St) (id : ℕ) : Decidable (cleared C s id) := by unfold cleared; infer_instance

/-- the transition function; `B` is the total audit budget -/
def step (R : Roles) (B : ℕ) (C : Checks) (s : St) : Op → St
  | .request c p =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ R.agents then { s with reqs := s.reqs ++ [⟨s.next, c, p⟩], next := s.next + 1 } else s
  | .monitor c id f =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ R.monitors ∧ id ∉ s.verdicts.map Prod.fst then { s with verdicts := s.verdicts ++ [(id, f)] } else s
  | .audit c id caught =>
    if s.halted ∧ C.haltCheck then s
    else if c ∈ R.auditors ∧ (id, true) ∈ s.verdicts ∧ id ∉ s.audits.map Prod.fst ∧
        (C.budget → s.audits.length < B) then
      { s with audits := s.audits ++ [(id, caught)], halted := s.halted || (caught && C.haltOnCatch) }
    else s
  | .execute _ id =>
    if s.halted ∧ C.haltCheck then s
    else match reqOf s id with
      | none => s
      | some r => if cleared C s id then ledgerAppend C s id r.p else s
  | .directCall c key p => if C.auth ∧ c ≠ R.gate then s else ledgerAppend C s key p
  | .halt c => if c ∈ R.admins then { s with halted := true } else s

def run (R : Roles) (B : ℕ) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step R B C) s

/-- untrusted operations never carry the gate's credential (credential separation, a correspondence premise) -/
def legal (R : Roles) : Op → Prop
  | .directCall c _ _ => c ≠ R.gate
  | _ => True

/-- the gate as a `Gate.System` over legal operations; its effect log is `St.ledger` -/
def sys (R : Roles) (B : ℕ) : System St {o : Op // legal R o} (ℕ × Payload) where
  step := fun s o => step R B full s o.1
  effects := St.ledger

/-- witness roles: role i gets UID i+1 (in the order of the spec); the gate credential is 9 -/
def R0 : Roles := ⟨[1], [2], [3], [4], 9⟩

/-- sanity: the empty trace is the initial state -/
example : run R0 1 full init [] = init := rfl

/-! ## The invariant and the safety property -/

/-- the monitor passed the request, or flagged it and an audit found nothing -/
def Cleared (s : St) (k : ℕ) : Prop :=
  (k, false) ∈ s.verdicts ∨ ((k, true) ∈ s.verdicts ∧ (k, false) ∈ s.audits)

structure Inv (B : ℕ) (s : St) : Prop where
  ledger_ok : ∀ e ∈ s.ledger, ∃ r, reqOf s e.1 = some r ∧ r.p = e.2 ∧ Cleared s e.1
  ledger_nd : (s.ledger.map Prod.fst).Nodup
  verd_nd : (s.verdicts.map Prod.fst).Nodup
  aud_nd : (s.audits.map Prod.fst).Nodup
  aud_le : s.audits.length ≤ B
  caught_halts : ∀ a ∈ s.audits, a.2 = true → s.halted = true

/-- entries whose monitor verdict was FLAG: each ran only on the strength of an audit -/
def flaggedEffects (s : St) : List (ℕ × Payload) := s.ledger.filter (fun e => decide ((e.1, true) ∈ s.verdicts))

/-- the safety property -/
def Good (B : ℕ) (s : St) : Prop :=
  (∀ e ∈ s.ledger, ∃ r, reqOf s e.1 = some r ∧ r.p = e.2 ∧ Cleared s e.1) ∧
  (s.ledger.map Prod.fst).Nodup ∧
  (flaggedEffects s).length ≤ B ∧
  (∀ a ∈ s.audits, a.2 = true → s.halted = true)

theorem inv_init (B : ℕ) : Inv B init :=
  ⟨by simp [init], by simp [init], by simp [init], by simp [init], by simp [init], by simp [init]⟩

theorem Cleared.mono {s t : St} (hV : s.verdicts ⊆ t.verdicts) (hA : s.audits ⊆ t.audits) {k : ℕ}
    (h : Cleared s k) : Cleared t k := by
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl (hV h)
  · exact Or.inr ⟨hV h1, hA h2⟩

theorem reqOf_append (s : St) (l : List Req) (k : ℕ) (r : Req) (h : reqOf s k = some r) :
    reqOf { s with reqs := s.reqs ++ l } k = some r := by
  simp only [reqOf] at h ⊢
  simp [List.find?_append, h]

/-- under `Inv`, a flagged ledger entry's key is an audited key; so flagged entries inject into audits -/
theorem Inv.flagged_le {B : ℕ} {s : St} (h : Inv B s) : (flaggedEffects s).length ≤ B := by
  have hnd : ((flaggedEffects s).map Prod.fst).Nodup :=
    h.ledger_nd.sublist (List.Sublist.map _ (List.filter_sublist))
  have hsub : ((flaggedEffects s).map Prod.fst) ⊆ s.audits.map Prod.fst := by
    intro k hk
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hk
    simp only [flaggedEffects, List.mem_filter, decide_eq_true_eq] at he
    obtain ⟨he, hv⟩ := he
    obtain ⟨r, -, -, hc⟩ := h.ledger_ok e he
    rcases hc with hc | ⟨-, hc⟩
    · exfalso
      -- (k,false) and (k,true) both in verdicts contradicts key-uniqueness
      have := List.inj_on_of_nodup_map h.verd_nd hc hv rfl
      simp at this
    · exact List.mem_map.2 ⟨_, hc, rfl⟩
  have := (List.Nodup.subperm hnd hsub).length_le
  simp only [List.length_map] at this
  exact this.trans h.aud_le

theorem Inv.good {B : ℕ} {s : St} (h : Inv B s) : Good B s :=
  ⟨h.ledger_ok, h.ledger_nd, h.flagged_le, h.caught_halts⟩

theorem cleared_sound {C : Checks} (hC : Sound C) {s : St} {k : ℕ} (h : cleared C s k) : Cleared s k := by
  rcases h hC.monitorGate with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2 hC.auditGate⟩

theorem ledgerAppend_inv {B : ℕ} {C : Checks} (hdd : C.dedup = true) {s : St} (h : Inv B s)
    (k : ℕ) (r : Req) (hr : reqOf s k = some r) (hcl : Cleared s k) : Inv B (ledgerAppend C s k r.p) := by
  unfold ledgerAppend
  by_cases hd : k ∈ s.ledger.map Prod.fst
  · simpa [hdd, hd] using h
  · simp only [hdd, true_and, hd, ite_false]
    refine ⟨?_, ?_, h.verd_nd, h.aud_nd, h.aud_le, h.caught_halts⟩
    · intro e he
      rcases List.mem_append.1 he with he | he
      · exact h.ledger_ok e he
      · simp only [List.mem_singleton] at he
        subst he
        exact ⟨r, hr, rfl, hcl⟩
    · simp only [List.map_append, List.map_cons, List.map_nil]
      refine List.nodup_append.2 ⟨h.ledger_nd, List.nodup_singleton _, fun a ha b hb => ?_⟩
      simp only [List.mem_singleton] at hb
      subst hb
      rintro rfl
      exact hd ha

theorem step_inv (R : Roles) (B : ℕ) {C : Checks} (hC : Sound C) (s : St) (o : Op) (ho : legal R o)
    (h : Inv B s) : Inv B (step R B C s o) := by
  cases o with
  | request c p =>
    simp only [step]
    split_ifs with h1 h2
    · exact h
    · refine ⟨?_, h.ledger_nd, h.verd_nd, h.aud_nd, h.aud_le, h.caught_halts⟩
      intro e he
      obtain ⟨r, hr, hp, hcl⟩ := h.ledger_ok e he
      exact ⟨r, reqOf_append s _ _ r hr, hp, hcl⟩
    · exact h
  | monitor c id f =>
    simp only [step]
    split_ifs with h1 h2
    · exact h
    · obtain ⟨-, hid⟩ := h2
      refine ⟨?_, h.ledger_nd, ?_, h.aud_nd, h.aud_le, h.caught_halts⟩
      · intro e he
        obtain ⟨r, hr, hp, hcl⟩ := h.ledger_ok e he
        exact ⟨r, hr, hp, hcl.mono (by intro x hx; simp [hx]) (by intro x hx; exact hx)⟩
      · simp only [List.map_append, List.map_cons, List.map_nil]
        refine List.nodup_append.2 ⟨h.verd_nd, List.nodup_singleton _, fun a ha b hb => ?_⟩
        simp only [List.mem_singleton] at hb
        subst hb
        rintro rfl
        exact hid ha
    · exact h
  | audit c id caught =>
    simp only [step]
    split_ifs with h1 h2
    · exact h
    · obtain ⟨-, -, hid, hb⟩ := h2
      refine ⟨?_, h.ledger_nd, h.verd_nd, ?_, ?_, ?_⟩
      · intro e he
        obtain ⟨r, hr, hp, hcl⟩ := h.ledger_ok e he
        exact ⟨r, hr, hp, hcl.mono (by intro x hx; exact hx) (by intro x hx; simp [hx])⟩
      · simp only [List.map_append, List.map_cons, List.map_nil]
        refine List.nodup_append.2 ⟨h.aud_nd, List.nodup_singleton _, fun a ha b hb => ?_⟩
        simp only [List.mem_singleton] at hb
        subst hb
        rintro rfl
        exact hid ha
      · have := hb hC.budget
        simp only [List.length_append, List.length_singleton]
        omega
      · intro a ha hat
        rcases List.mem_append.1 ha with ha | ha
        · simp [h.caught_halts a ha hat]
        · simp only [List.mem_singleton] at ha
          subst ha
          simp [show caught = true from hat, hC.haltOnCatch]
    · exact h
  | execute c id =>
    simp only [step]
    split_ifs with h1 h2
    · exact h
    · split
      · exact h
      · rename_i r hr
        exact ledgerAppend_inv hC.dedup h id r hr (cleared_sound hC h2)
    · split <;> exact h
  | directCall c key p =>
    simp only [legal] at ho
    simp only [step]
    split_ifs with hh
    · exact h
    · exact absurd ⟨hC.auth, ho⟩ hh
  | halt c =>
    simp only [step]
    split_ifs with h1
    · refine ⟨h.ledger_ok, h.ledger_nd, h.verd_nd, h.aud_nd, h.aud_le, fun a _ _ => rfl⟩
    · exact h

theorem run_inv (R : Roles) (B : ℕ) {C : Checks} (hC : Sound C) (s : St) (ops : List Op)
    (hops : ∀ o ∈ ops, legal R o) (h : Inv B s) : Inv B (run R B C s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih =>
    exact ih (step R B C s o) (fun o' ho' => hops o' (List.mem_cons_of_mem o ho'))
      (step_inv R B hC s o (hops o List.mem_cons_self) h)

/-- **SC-90 safety.** After any legal trace from the initial state, `Good` holds. -/
theorem sc90_safe (R : Roles) (B : ℕ) (ops : List Op) (hops : ∀ o ∈ ops, legal R o) :
    Good B (run R B full init ops) :=
  (run_inv R B sound_full init ops hops (inv_init B)).good

/-! ## Consequences: where a harmful effect can come from -/

/-- every effect in the ledger was monitor-PASSed or audited with no finding -/
theorem harmful_effect_is_a_miss {B : ℕ} {s : St} (h : Good B s) :
    ∀ e ∈ s.ledger, e.2.harm = true → (e.1, false) ∈ s.verdicts ∨ (e.1, false) ∈ s.audits := by
  intro e he _
  obtain ⟨r, -, -, hc⟩ := h.1 e he
  rcases hc with hc | ⟨-, hc⟩
  · exact Or.inl hc
  · exact Or.inr hc

/-- PREMISE (a fact about the auditor, not the gate): every audit of a request with a harmful payload reports it -/
def AuditRecallPerfect (s : St) : Prop :=
  ∀ a ∈ s.audits, ∀ r, reqOf s a.1 = some r → r.p.harm = true → a.2 = true

/-- with perfect audit recall, only monitor misses reach the ledger -/
theorem only_monitor_misses_escape {B : ℕ} {s : St} (h : Good B s) (hrec : AuditRecallPerfect s) :
    ∀ e ∈ s.ledger, e.2.harm = true → (e.1, false) ∈ s.verdicts := by
  intro e he hharm
  obtain ⟨r, hr, hp, hc⟩ := h.1 e he
  rcases hc with hc | ⟨-, hc⟩
  · exact hc
  · have := hrec _ hc r hr (by rw [hp]; exact hharm)
    simp at this

/-! ## Budget exhaustion blocks -/

theorem step_audits_exhausted (R : Roles) (B : ℕ) {C : Checks} (hC : Sound C) (s : St) (o : Op)
    (hex : B ≤ s.audits.length) : (step R B C s o).audits = s.audits := by
  cases o with
  | audit c id caught =>
    simp only [step]
    split_ifs with h1 h2
    · rfl
    · have := h2.2.2.2 hC.budget
      omega
    · rfl
  | request c p => simp only [step]; split_ifs <;> rfl
  | monitor c id f => simp only [step]; split_ifs <;> rfl
  | execute c id =>
    simp only [step]
    split_ifs <;> (try split) <;> simp [ledgerAppend] <;> split_ifs <;> rfl
  | directCall c key p => simp only [step]; split_ifs <;> simp [ledgerAppend] <;> split_ifs <;> rfl
  | halt c => simp only [step]; split_ifs <;> rfl

theorem step_verdicts_mono (R : Roles) (B : ℕ) (C : Checks) (s : St) (o : Op) :
    s.verdicts ⊆ (step R B C s o).verdicts := by
  cases o with
  | monitor c id f =>
    simp only [step]
    split_ifs
    · exact fun _ hx => hx
    · intro x hx; simp [hx]
    · exact fun _ hx => hx
  | request c p => simp only [step]; split_ifs <;> exact fun _ hx => hx
  | audit c id caught => simp only [step]; split_ifs <;> exact fun _ hx => hx
  | execute c id =>
    simp only [step]
    split_ifs <;> (try split) <;> simp [ledgerAppend] <;> split_ifs <;> exact fun _ hx => hx
  | directCall c key p => simp only [step]; split_ifs <;> simp [ledgerAppend] <;> split_ifs <;> exact fun _ hx => hx
  | halt c => simp only [step]; split_ifs <;> exact fun _ hx => hx

theorem run_exhausted (R : Roles) (B : ℕ) {C : Checks} (hC : Sound C) (s : St) (ops : List Op)
    (hex : B ≤ s.audits.length) :
    (run R B C s ops).audits = s.audits ∧ s.verdicts ⊆ (run R B C s ops).verdicts := by
  induction ops generalizing s with
  | nil => exact ⟨rfl, fun _ hx => hx⟩
  | cons o ops ih =>
    have h1 := step_audits_exhausted R B hC s o hex
    obtain ⟨h2, h3⟩ := ih (step R B C s o) (by rw [h1]; exact hex)
    show (run R B C (step R B C s o) ops).audits = s.audits ∧
      s.verdicts ⊆ (run R B C (step R B C s o) ops).verdicts
    exact ⟨h2.trans h1, fun x hx => h3 (step_verdicts_mono R B C s o hx)⟩

/-- **Exhaustion blocks.** Once `B` audits have been spent, a flagged request that was never audited can never
execute, on any legal continuation: the budget is a hard cap on flagged effects, not a soft one. -/
theorem exhausted_blocks (R : Roles) (B : ℕ) {C : Checks} (hC : Sound C) {s : St} (h : Inv B s)
    (hex : B ≤ s.audits.length) {k : ℕ} (hk : (k, true) ∈ s.verdicts) (hna : k ∉ s.audits.map Prod.fst)
    (ops : List Op) (hops : ∀ o ∈ ops, legal R o) : k ∉ (run R B C s ops).ledger.map Prod.fst := by
  obtain ⟨hA, hV⟩ := run_exhausted R B hC s ops hex
  have hI := run_inv R B hC s ops hops h
  intro hmem
  obtain ⟨e, he, hek⟩ := List.mem_map.1 hmem
  obtain ⟨r, -, -, hc⟩ := hI.ledger_ok e he
  rw [hek] at hc
  rcases hc with hc | ⟨-, hc⟩
  · have := List.inj_on_of_nodup_map hI.verd_nd hc (hV hk) rfl
    simp at this
  · rw [hA] at hc
    exact hna (List.mem_map.2 ⟨_, hc, rfl⟩)

/-! ## HALT -/

theorem step_halted (R : Roles) (B : ℕ) {C : Checks} (hh : C.haltCheck = true) (ha : C.auth = true) (s : St)
    (hs : s.halted = true) (o : Op) (ho : legal R o) : step R B C s o = s := by
  cases o with
  | request c p => simp [step, hs, hh]
  | monitor c id f => simp [step, hs, hh]
  | audit c id caught => simp [step, hs, hh]
  | execute c id => simp [step, hs, hh]
  | directCall c key p =>
    simp only [legal] at ho
    simp [step, ha, ho]
  | halt c =>
    simp only [step]
    split_ifs
    · cases s; simp_all
    · rfl

/-- **Halt freezes.** With the HALT check and receiver authentication, after a halt no legal operation changes
anything (in particular the ledger). In this model delivery is atomic: there are no in-flight messages to finish. -/
theorem halt_freezes (R : Roles) (B : ℕ) {C : Checks} (hh : C.haltCheck = true) (ha : C.auth = true) (s : St)
    (hs : s.halted = true) (ops : List Op) (hops : ∀ o ∈ ops, legal R o) : run R B C s ops = s := by
  induction ops with
  | nil => rfl
  | cons o ops ih =>
    show run R B C (step R B C s o) ops = s
    rw [step_halted R B hh ha s hs o (hops o List.mem_cons_self)]
    exact ih (fun o' ho' => hops o' (List.mem_cons_of_mem o ho'))

/-! ## The gate spec (reuse of `Core/Gate.lean`) -/

theorem step_ledger_prefix (R : Roles) (B : ℕ) (C : Checks) (s : St) (o : Op) :
    s.ledger <+: (step R B C s o).ledger := by
  cases o with
  | request c p => simp only [step]; split_ifs <;> exact List.prefix_refl _
  | monitor c id f => simp only [step]; split_ifs <;> exact List.prefix_refl _
  | audit c id caught => simp only [step]; split_ifs <;> exact List.prefix_refl _
  | execute c id =>
    simp only [step]
    split_ifs <;> (try split) <;> (try simp only [ledgerAppend]) <;> (try split_ifs) <;>
      first | exact List.prefix_refl _ | exact List.prefix_append _ _
  | directCall c key p =>
    simp only [step]
    split_ifs <;> (try simp only [ledgerAppend]) <;> (try split_ifs) <;>
      first | exact List.prefix_refl _ | exact List.prefix_append _ _
  | halt c => simp only [step]; split_ifs <;> exact List.prefix_refl _

/-- the model is a client of the shared gate interface -/
def spec (R : Roles) (B : ℕ) : Spec (sys R B) where
  Inv := Inv B
  ok := fun s e => ∃ r, reqOf s e.1 = some r ∧ r.p = e.2 ∧ Cleared s e.1
  step_inv := fun s o h => step_inv R B sound_full s o.1 o.2 h
  log_prefix := fun s o => step_ledger_prefix R B full s o.1
  inv_ok := fun _ h e he => h.ledger_ok e he

/-! ## Non-vacuity and one necessity witness per check -/

/-- a harmful payload (ground truth) -/
def pH : Payload := ⟨5, true⟩
def pB : Payload := ⟨6, false⟩

/-- **Non-vacuity**: a PASSed request and an audited FLAGGED request both execute under the full gate -/
theorem honest_trace_effects :
    (run R0 1 full init [.request 1 pB, .monitor 2 0 false, .execute 1 0]).ledger = [(0, pB)] ∧
    (run R0 1 full init [.request 1 pB, .monitor 2 0 true, .audit 3 0 false, .execute 1 0]).ledger = [(0, pB)] := by
  decide

/-- **Exhaustion**: with budget 0, the audit is refused and the flagged request is blocked forever -/
theorem budget_zero_blocks :
    (run R0 0 full init [.request 1 pB, .monitor 2 0 true, .audit 3 0 false, .execute 1 0]).ledger = [] := by
  decide

/-- a caught audit halts, and the harmful request never runs -/
theorem caught_halts_and_blocks :
    (run R0 1 full init [.request 1 pH, .monitor 2 0 true, .audit 3 0 true, .execute 1 0]).ledger = [] ∧
    (run R0 1 full init [.request 1 pH, .monitor 2 0 true, .audit 3 0 true]).halted = true := by
  decide

/-- a harmful request the monitor PASSes executes: the gate cannot do better than the monitor (a monitor miss) -/
theorem monitor_miss_escapes :
    (run R0 1 full init [.request 1 pH, .monitor 2 0 false, .execute 1 0]).ledger = [(0, pH)] := by
  decide

theorem no_monitorGate_breaks :
    ¬ Good 1 (run R0 1 { full with monitorGate := false } init [.request 1 pH, .execute 1 0]) := by
  have hs : run R0 1 { full with monitorGate := false } init [.request 1 pH, .execute 1 0] =
      ⟨1, false, [(0, pH)], [⟨0, 1, pH⟩], [], []⟩ := by decide
  rw [hs]
  intro hg
  obtain ⟨r, -, -, hc⟩ := hg.1 (0, pH) (by simp)
  simp [Cleared] at hc

theorem no_auditGate_breaks :
    ¬ Good 1 (run R0 1 { full with auditGate := false } init [.request 1 pH, .monitor 2 0 true, .execute 1 0]) := by
  have hs : run R0 1 { full with auditGate := false } init [.request 1 pH, .monitor 2 0 true, .execute 1 0] =
      ⟨1, false, [(0, pH)], [⟨0, 1, pH⟩], [(0, true)], []⟩ := by decide
  rw [hs]
  intro hg
  obtain ⟨r, -, -, hc⟩ := hg.1 (0, pH) (by simp)
  simp [Cleared] at hc

/-- budget 1, two flagged requests both audited and run: the budget is exceeded -/
theorem no_budget_breaks :
    ¬ Good 1 (run R0 1 { full with budget := false } init
      [.request 1 pB, .request 1 pB, .monitor 2 0 true, .monitor 2 1 true, .audit 3 0 false, .audit 3 1 false,
       .execute 1 0, .execute 1 1]) := by
  have hs : run R0 1 { full with budget := false } init
      [.request 1 pB, .request 1 pB, .monitor 2 0 true, .monitor 2 1 true, .audit 3 0 false, .audit 3 1 false,
       .execute 1 0, .execute 1 1] =
      ⟨2, false, [(0, pB), (1, pB)], [⟨0, 1, pB⟩, ⟨1, 1, pB⟩], [(0, true), (1, true)], [(0, false), (1, false)]⟩ := by
    decide
  rw [hs]
  intro hg
  have := hg.2.2.1
  simp [flaggedEffects] at this

theorem no_haltOnCatch_breaks :
    ¬ Good 1 (run R0 1 { full with haltOnCatch := false } init [.request 1 pH, .monitor 2 0 true, .audit 3 0 true]) := by
  have hs : run R0 1 { full with haltOnCatch := false } init [.request 1 pH, .monitor 2 0 true, .audit 3 0 true] =
      ⟨1, false, [], [⟨0, 1, pH⟩], [(0, true)], [(0, true)]⟩ := by decide
  rw [hs]
  intro hg
  have := hg.2.2.2 (0, true) (by simp) rfl
  simp at this

theorem no_auth_breaks :
    legal R0 (.directCall 1 7 pH) ∧
    ¬ Good 1 (run R0 1 { full with auth := false } init [.directCall 1 7 pH]) := by
  refine ⟨by simp [legal, R0], ?_⟩
  have hs : run R0 1 { full with auth := false } init [.directCall 1 7 pH] =
      ⟨0, false, [(7, pH)], [], [], []⟩ := by decide
  rw [hs]
  intro hg
  obtain ⟨r, hr, -⟩ := hg.1 (7, pH) (by simp)
  simp [reqOf] at hr

theorem no_dedup_breaks :
    ¬ Good 1 (run R0 1 { full with dedup := false } init [.request 1 pB, .monitor 2 0 false, .execute 1 0, .execute 1 0]) := by
  have hs : run R0 1 { full with dedup := false } init [.request 1 pB, .monitor 2 0 false, .execute 1 0, .execute 1 0] =
      ⟨1, false, [(0, pB), (0, pB)], [⟨0, 1, pB⟩], [(0, false)], []⟩ := by decide
  rw [hs]
  intro hg
  have := hg.2.1
  simp at this

/-- without the HALT check a request executes after the halt; with it, nothing does -/
theorem no_haltCheck_breaks :
    (run R0 1 { full with haltCheck := false } init [.request 1 pH, .monitor 2 0 false, .halt 4, .execute 1 0]).ledger =
      [(0, pH)] ∧
    (run R0 1 full init [.request 1 pH, .monitor 2 0 false, .halt 4, .execute 1 0]).ledger = [] := by
  decide

end ControlStack.SC90

#print axioms ControlStack.SC90.sc90_safe
#print axioms ControlStack.SC90.Inv.flagged_le
#print axioms ControlStack.SC90.harmful_effect_is_a_miss
#print axioms ControlStack.SC90.only_monitor_misses_escape
#print axioms ControlStack.SC90.exhausted_blocks
#print axioms ControlStack.SC90.halt_freezes
#print axioms ControlStack.SC90.spec
#print axioms ControlStack.SC90.honest_trace_effects
#print axioms ControlStack.SC90.budget_zero_blocks
#print axioms ControlStack.SC90.caught_halts_and_blocks
#print axioms ControlStack.SC90.monitor_miss_escapes
#print axioms ControlStack.SC90.no_monitorGate_breaks
#print axioms ControlStack.SC90.no_auditGate_breaks
#print axioms ControlStack.SC90.no_budget_breaks
#print axioms ControlStack.SC90.no_haltOnCatch_breaks
#print axioms ControlStack.SC90.no_auth_breaks
#print axioms ControlStack.SC90.no_dedup_breaks
#print axioms ControlStack.SC90.no_haltCheck_breaks
