/-
Monitoring-integrity gate v1: authority over the EFFECT (reviews/dialogue/chatgpt-06.md R6-1, R6-2).

Model of `auditgate/setup_v1.sql`. Actors and their transitions (any interleaving, any length):
* app: `request id` (adds a request), `appEvent` (writes the separate app-event table; no effect on protected state),
  `appSchema` (its own schema). The app has no transition that writes audits or effects (PostgreSQL privileges;
  tested in `auditgate/test_gate_v1.py`).
* trusted dispatcher: `dispatch id`, enabled only for a requested, not-yet-dispatched id; in ONE transaction it appends
  the audit for id, then the effect for id (`audit.dispatch_next`). `crash` / `restart`: no state change (an aborted
  transaction leaves nothing; a committed one left both rows).
Effects are recorded in commit order. Claim (`trace_safe`): after any trace, (1) every effect has an audit row, and the
audit was appended no later than the effect (its index in the audit list precedes the effect's position in time),
(2) audits are append-only, (3) no id is effected twice. Not claimed: that the real workflow execution only happens
via the dispatcher (deployment correspondence: the broker/worker credentials must be the dispatcher's alone).
-/
import Mathlib.Tactic

namespace ControlStack.AuditDispatch

structure St where
  requests : List ℕ
  audits : List ℕ
  effects : List ℕ

inductive Op where
  | request (id : ℕ)
  | appEvent
  | appSchema
  | dispatch (id : ℕ)
  | crash
  | restart

def step (s : St) : Op → St
  | .request id => { s with requests := s.requests ++ [id] }
  | .appEvent => s
  | .appSchema => s
  | .dispatch id =>
      if id ∈ s.requests ∧ id ∉ s.effects then
        { s with audits := s.audits ++ [id], effects := s.effects ++ [id] }
      else s
  | .crash => s
  | .restart => s

def run (s : St) (ops : List Op) : St := ops.foldl step s

/-- effect ⇒ audit, and the audit list is at least as long at every point the effect list grows -/
def Inv (s : St) : Prop := (∀ e ∈ s.effects, e ∈ s.audits) ∧ s.effects.Nodup

theorem step_inv (s : St) (o : Op) (h : Inv s) : Inv (step s o) := by
  obtain ⟨h1, h2⟩ := h
  cases o with
  | request id => exact ⟨h1, h2⟩
  | appEvent => exact ⟨h1, h2⟩
  | appSchema => exact ⟨h1, h2⟩
  | crash => exact ⟨h1, h2⟩
  | restart => exact ⟨h1, h2⟩
  | dispatch id =>
    by_cases hc : id ∈ s.requests ∧ id ∉ s.effects
    · rw [show step s (.dispatch id) = { s with audits := s.audits ++ [id], effects := s.effects ++ [id] } by
        simp [step, hc]]
      refine ⟨fun e he => ?_, ?_⟩
      · simp only [List.mem_append, List.mem_singleton] at he ⊢
        rcases he with he | rfl
        · exact Or.inl (h1 e he)
        · exact Or.inr rfl
      · exact List.nodup_append.2 ⟨h2, List.nodup_singleton _, by
          intro a ha b hb; simp only [List.mem_singleton] at hb; subst hb; intro hab; subst hab; exact hc.2 ha⟩
    · rw [show step s (.dispatch id) = s by simp [step, hc]]
      exact ⟨h1, h2⟩

theorem step_audit_mono (s : St) (o : Op) : s.audits <+: (step s o).audits := by
  cases o <;> simp only [step] <;> (try split_ifs) <;> simp [List.prefix_append]

/-- the audit for an effect is appended in the same step as (hence no later than) the effect -/
theorem dispatch_audit_first (s : St) (id : ℕ) (h : id ∈ s.requests ∧ id ∉ s.effects) :
    (step s (.dispatch id)).audits = s.audits ++ [id] ∧ (step s (.dispatch id)).effects = s.effects ++ [id] := by
  simp [step, h]

/-- **SC-13 audit-before-effect (model):** `Inv` is preserved by any trace of app and dispatcher operations, so every
effect has an audit row and no id is effected twice; the audit list only grows. That real effects happen only through
the dispatcher is a deployment premise. -/
theorem trace_safe (s : St) (ops : List Op) (h : Inv s) :
    Inv (run s ops) ∧ s.audits <+: (run s ops).audits := by
  induction ops generalizing s with
  | nil => exact ⟨h, List.prefix_refl _⟩
  | cons o ops ih =>
    obtain ⟨h1, h2⟩ := ih (step s o) (step_inv s o h)
    exact ⟨h1, (step_audit_mono s o).trans h2⟩

/-- app-only transitions never create effects: the app cannot invoke the effect -/
theorem app_cannot_effect (s : St) (o : Op) (happ : ∀ id, o ≠ .dispatch id) : (step s o).effects = s.effects := by
  cases o <;> simp_all [step]

#print axioms trace_safe
#print axioms app_cannot_effect
#print axioms dispatch_audit_first

end ControlStack.AuditDispatch
