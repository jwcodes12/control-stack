import ControlStack.Core.RunFixed
import ControlStack.GateClients
import ControlStack.EgressGate
import ControlStack.Scenarios.SC06Artifacts
import ControlStack.Scenarios.SC08Exec
import ControlStack.Scenarios.SC09Priv
import ControlStack.Scenarios.SC10Policy
import ControlStack.Scenarios.SC12Persistence
import ControlStack.Scenarios.EvalIntegrity
import ControlStack.Scenarios.SC15Review
import ControlStack.Scenarios.SC16Deploy
import ControlStack.Scenarios.SC19Prod
import ControlStack.Scenarios.SC20Data
import ControlStack.Scenarios.SC23Injection
import ControlStack.Scenarios.SC23Isolation
import ControlStack.Scenarios.SC25Audit
import ControlStack.Scenarios.SC17Infra
import ControlStack.Scenarios.SC14Runaway
import ControlStack.Scenarios.SC18Logging
import ControlStack.Scenarios.SC23IsolationV2
import ControlStack.Scenarios.SC26Transaction
import ControlStack.Scenarios.SC27Chain
import ControlStack.Scenarios.SC28Budget

/-!
Reuse bridges: each pinned scenario's `*_safe` and `halt_freezes` re-derived from
the shared gate interface (`Gate.Spec.trace_safe`, `Gate.foldl_fixed`,
`Gate.foldl_field_fixed`) through the scenario's own `sys`/`spec` client.

For every bridge the statement is copied verbatim from the pinned theorem and a
`rfl` check (`*_agree`) confirms that the two have the same type, so the bridge
proves exactly the pinned statement. The pinned theorems and files are unchanged;
this file only shows the scenario-local `run_inv`/`halt_freezes` inductions are
instances of the generic ones. It is model-level reuse, not a runtime claim.

Not bridged here: SC14 and SC18 (their `sys` takes legal-only operations, handled
separately below), liveness, and refinement files (they need invariant/legal-trace
side conditions or fairness hypotheses that the unconditional generic induction
does not have).
-/

namespace ControlStack.SC06
open ControlStack.Gate

theorem sc06_safe_via_gate (P : Policy) (ops : List Op) : Good P (run P full init ops) :=
  let h : Inv P (run P full init ops) := ((spec P).trace_safe init ops (inv_init P)).1
  ⟨h.ctx, h.exec⟩

theorem sc06_safe_agree : @sc06_safe_via_gate = @sc06_safe := rfl

theorem halt_freezes_via_gate (P : Policy) (s : St) (ops : List Op) (hh : s.halted = true) : run P full s ops = s :=
  foldl_fixed (step P full) (fun s => s.halted = true)
    (fun s o hs => step_halted P s o hs) hh ops

theorem halt_freezes_agree : @halt_freezes_via_gate = @halt_freezes := rfl

end ControlStack.SC06

namespace ControlStack.SC08
open ControlStack.Gate

theorem sc08_safe_via_gate (E : Env) (files : List (ℕ × ℕ)) (ops : List Op) : Good E (run E full ⟨files, [], false⟩ ops) :=
  ((spec E).trace_safe ⟨files, [], false⟩ ops (fun r hr => by simp at hr)).1

theorem sc08_safe_agree : @sc08_safe_via_gate = @sc08_safe := rfl

theorem halt_freezes_via_gate (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s :=
  foldl_fixed (step E full) (fun s => s.halted = true)
    (fun s o hs => step_halted E s o hs) hh ops

theorem halt_freezes_agree : @halt_freezes_via_gate = @halt_freezes := rfl

end ControlStack.SC08

namespace ControlStack.SC09
open ControlStack.Gate

theorem sc09_safe_via_gate (P : Policy) (ops : List Op) : Good P (run P full init ops) :=
  ((spec P).trace_safe init ops (good_init P)).1

theorem sc09_safe_agree : @sc09_safe_via_gate = @sc09_safe := rfl

theorem halt_freezes_via_gate (P : Policy) (s : St) (ops : List Op) (hh : s.halted = true) : run P full s ops = s :=
  foldl_fixed (step P full) (fun s => s.halted = true)
    (fun s o hs => step_halted P s o hs) hh ops

theorem halt_freezes_agree : @halt_freezes_via_gate = @halt_freezes := rfl

end ControlStack.SC09

namespace ControlStack.SC10
open ControlStack.Gate

theorem sc10_safe_via_gate (E : Env) (hpin : E.h E.pinned = E.pinnedDigest) (ops : List Op) : Good E (run E full init ops) :=
  let h : Inv E (run E full init ops) := ((spec E hpin).trace_safe init ops (inv_init E)).1
  ⟨h.decs, h.builds⟩

theorem sc10_safe_agree : @sc10_safe_via_gate = @sc10_safe := rfl

theorem halt_freezes_via_gate (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s :=
  foldl_fixed (step E full) (fun s => s.halted = true)
    (fun s o hs => step_halted E s o hs) hh ops

theorem halt_freezes_agree : @halt_freezes_via_gate = @halt_freezes := rfl

end ControlStack.SC10

namespace ControlStack.SC12
open ControlStack.Gate

theorem sc12_safe_via_gate (admins : List ℕ) (ops : List Op) : Good (run admins full init ops) :=
  let h : Inv (run admins full init ops) := ((spec admins).trace_safe init ops inv_init).1
  h.good

theorem sc12_safe_agree : @sc12_safe_via_gate = @sc12_safe := rfl

theorem halt_freezes_via_gate (admins : List ℕ) (s : St) (ops : List Op) (hh : s.halted = true) : run admins full s ops = s :=
  foldl_fixed (step admins full) (fun s => s.halted = true)
    (fun s o hs => step_halted admins s o hs) hh ops

theorem halt_freezes_agree : @halt_freezes_via_gate = @halt_freezes := rfl

end ControlStack.SC12

namespace ControlStack.EvalIntegrity
open ControlStack.Gate

theorem sc21_safe_via_gate (E : Env) (ops : List Op) : ∀ p ∈ (run E full init ops).published, PubOk E p :=
  let h : Inv E (run E full init ops) := ((spec E).trace_safe init ops (inv_init E)).1
  h.pub

theorem sc21_safe_agree : @sc21_safe_via_gate = @sc21_safe := rfl

theorem halt_freezes_via_gate (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s :=
  foldl_fixed (step E full) (fun s => s.halted = true)
    (fun s o hs => step_halted E s o hs) hh ops

theorem halt_freezes_agree : @halt_freezes_via_gate = @halt_freezes := rfl

end ControlStack.EvalIntegrity

namespace ControlStack.SC15
open ControlStack.Gate

theorem sc15_safe_via_gate (E : Env) (ops : List Op) : ∀ c ∈ (run E full init ops).merged, MergeOk E (run E full init ops) c :=
  let h : Inv E (run E full init ops) := ((spec E).trace_safe init ops (inv_init E)).1
  h.merged

theorem sc15_safe_agree : @sc15_safe_via_gate = @sc15_safe := rfl

theorem halt_freezes_via_gate (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s :=
  foldl_fixed (step E full) (fun s => s.halted = true)
    (fun s o hs => step_halted E s o hs) hh ops

theorem halt_freezes_agree : @halt_freezes_via_gate = @halt_freezes := rfl

end ControlStack.SC15

namespace ControlStack.SC16
open ControlStack.Gate

theorem sc16_safe_via_gate (R : Roles) (h : ℕ → ℕ) (ops : List Op) : Good R h (run R h full init ops) :=
  let hi : Inv R h (run R h full init ops) := ((spec R h).trace_safe init ops (inv_init R h)).1
  hi.good

theorem sc16_safe_agree : @sc16_safe_via_gate = @sc16_safe := rfl

theorem halt_freezes_via_gate (R : Roles) (h : ℕ → ℕ) (s : St) (ops : List Op) (hh : s.halted = true) : run R h full s ops = s :=
  foldl_fixed (step R h full) (fun s => s.halted = true)
    (fun s o hs => step_halted R h s o hs) hh ops

theorem halt_freezes_agree : @halt_freezes_via_gate = @halt_freezes := rfl

end ControlStack.SC16

namespace ControlStack.SC19
open ControlStack.Gate

theorem sc19_safe_via_gate (E : Env) (ops : List Op) : Good E (run E full init ops) :=
  let h : Inv E (run E full init ops) := ((spec E).trace_safe init ops (inv_init E)).1
  h.good

theorem sc19_safe_agree : @sc19_safe_via_gate = @sc19_safe := rfl

theorem halt_freezes_via_gate (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s :=
  foldl_fixed (step E full) (fun s => s.halted = true)
    (fun s o hs => step_halted E s o hs) hh ops

theorem halt_freezes_agree : @halt_freezes_via_gate = @halt_freezes := rfl

end ControlStack.SC19

namespace ControlStack.SC20
open ControlStack.Gate

theorem sc20_safe_via_gate (E : Env) (ops : List Op) : Good E (run E full init ops) :=
  let h : Inv E (run E full init ops) := ((spec E).trace_safe init ops (inv_init E)).1
  h.trained

theorem sc20_safe_agree : @sc20_safe_via_gate = @sc20_safe := rfl

theorem halt_freezes_via_gate (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s :=
  foldl_fixed (step E full) (fun s => s.halted = true)
    (fun s o hs => step_halted E s o hs) hh ops

theorem halt_freezes_agree : @halt_freezes_via_gate = @halt_freezes := rfl

end ControlStack.SC20

namespace ControlStack.SC23
open ControlStack.Gate

theorem sc23_safe_via_gate (P : Policy) (ops : List Op) : Good P (run P full init ops) :=
  let h : Inv P (run P full init ops) := ((spec P).trace_safe init ops (inv_init P)).1
  h.good

theorem sc23_safe_agree : @sc23_safe_via_gate = @sc23_safe := rfl

theorem halt_freezes_via_gate (P : Policy) (s : St) (ops : List Op) (hh : s.halted = true) : run P full s ops = s :=
  foldl_fixed (step P full) (fun s => s.halted = true)
    (fun s o hs => step_halted P s o hs) hh ops

theorem halt_freezes_agree : @halt_freezes_via_gate = @halt_freezes := rfl

end ControlStack.SC23

namespace ControlStack.SC23Isolation
open ControlStack.Gate

theorem sc23_isolated_safe_via_gate (E : Env) (ops : List Op) : ∀ x ∈ (run E full init ops).executed, ActOk E (run E full init ops) x :=
  let h : Inv E (run E full init ops) := ((spec E).trace_safe init ops (inv_init E)).1
  h.exec

theorem sc23_isolated_safe_agree : @sc23_isolated_safe_via_gate = @sc23_isolated_safe := rfl

theorem halt_freezes_via_gate (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s :=
  foldl_fixed (step E full) (fun s => s.halted = true)
    (fun s o hs => step_halted E s o hs) hh ops

theorem halt_freezes_agree : @halt_freezes_via_gate = @halt_freezes := rfl

end ControlStack.SC23Isolation

namespace ControlStack.SC25
open ControlStack.Gate

theorem sc25_safe_via_gate (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List Op) : Good R h cls (run R h cls full init ops) :=
  let hi : Inv R h cls (run R h cls full init ops) := ((spec R h cls).trace_safe init ops (inv_init R h cls)).1
  hi.good

theorem sc25_safe_agree : @sc25_safe_via_gate = @sc25_safe := rfl

theorem halt_freezes_via_gate (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (s : St) (ops : List Op) (hh : s.halted = true) : (run R h cls full s ops).executed = s.executed :=
  foldl_field_fixed (step R h cls full) (fun s => s.halted = true) St.executed
    (fun s o hs => step_halted R h cls s o hs) hh ops

theorem halt_freezes_agree : @halt_freezes_via_gate = @halt_freezes := rfl

end ControlStack.SC25

namespace ControlStack.SC17
open ControlStack.Gate

theorem sc17_safe_via_gate (E : Env) (g0 : List G) (ops : List Op) : Good E (run E full (init g0) ops) :=
  let h : Inv E (run E full (init g0) ops) := ((spec E).trace_safe (init g0) ops (inv_init E g0)).1
  h.good

theorem sc17_safe_agree : @sc17_safe_via_gate = @sc17_safe := rfl

theorem halt_freezes_via_gate (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : (run E full s ops).applied = s.applied :=
  foldl_field_fixed (step E full) (fun s => s.halted = true) St.applied
    (fun s o hs => step_halted E s o hs) hh ops

theorem halt_freezes_agree : @halt_freezes_via_gate = @halt_freezes := rfl

end ControlStack.SC17

/-! ## Clients whose `sys` takes only legal operations (SC14, SC18) -/

namespace ControlStack.SC14
open ControlStack.Gate

theorem sc14_safe_via_gate (E : Env) (exp : ℕ) (ops : List Op) (hops : ∀ o ∈ ops, legal o) :
    Good E (run E full (init exp) ops) := by
  obtain ⟨ops', e⟩ := foldl_legal (step E full) legal ops hops (init exp)
  have h : Inv E ((sys E).run (init exp) ops') :=
    ((spec E).trace_safe (init exp) ops' (inv_init E exp)).1
  have e' : (sys E).run (init exp) ops' = run E full (init exp) ops := e
  rw [e'] at h
  have h' : Inv E (run E full (init exp) ops) := h
  exact h'.good

theorem sc14_safe_agree : @sc14_safe_via_gate = @sc14_safe := rfl

theorem halt_freezes_via_gate (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) :
    (run E full s ops).usage = s.usage :=
  foldl_field_fixed (step E full) (fun s => s.halted = true) St.usage
    (fun s o hs => step_halted E s o hs) hh ops

theorem halt_freezes_agree : @halt_freezes_via_gate = @halt_freezes := rfl
end ControlStack.SC14

namespace ControlStack.SC18
open ControlStack.Gate

theorem sc18_safe_via_gate (admins : List ℕ) (trusted T : ℕ) (ops : List Op)
    (hops : ∀ o ∈ ops, legal admins trusted o) :
    Good T (run admins trusted T full (init trusted) ops) := by
  obtain ⟨ops', e⟩ := foldl_legal (step admins trusted T full) (legal admins trusted) ops hops (init trusted)
  have h : Inv trusted T ((sys admins trusted T).run (init trusted) ops') :=
    ((spec admins trusted T).trace_safe (init trusted) ops' (inv_init trusted T)).1
  have e' : (sys admins trusted T).run (init trusted) ops' = run admins trusted T full (init trusted) ops := e
  rw [e'] at h
  have h' : Inv trusted T (run admins trusted T full (init trusted) ops) := h
  exact ⟨h'.rel_ok, h'.nodup⟩

theorem sc18_safe_agree : @sc18_safe_via_gate = @sc18_safe := rfl

theorem halt_freezes_via_gate (admins : List ℕ) (trusted T : ℕ) (s : St) (ops : List Op)
    (hh : s.halted = true) : (run admins trusted T full s ops).released = s.released :=
  foldl_field_fixed (step admins trusted T full) (fun s => s.halted = true) St.released
    (fun s o hs => step_halted admins trusted T s o hs) hh ops

theorem halt_freezes_agree : @halt_freezes_via_gate = @halt_freezes := rfl
end ControlStack.SC18

/-! ## EgressGate (file unchanged; only imported) -/

namespace ControlStack.EgressGate
open ControlStack.Gate
open ControlStack.GateClients

theorem trace_safe_via_gate (p : Policy) (s : State) (actions : List Action)
    (h : Invariant p s) : Invariant p (run p s actions) :=
  ((egressSpec p).trace_safe s actions h).1

theorem trace_safe_agree : @trace_safe_via_gate = @trace_safe := rfl
end ControlStack.EgressGate

/-! ## SC26, SC27, SC28 -/

namespace ControlStack.SC26
open ControlStack.Gate

theorem sc26_safe_via_gate (R : Roles) (cap : ℕ) (ops : List Op) (hops : ∀ o ∈ ops, legal R o) :
    Good R cap (run R cap full init ops) := by
  obtain ⟨ops', e⟩ := foldl_legal (step R cap full) (legal R) ops hops init
  have h : Inv R cap ((sys R cap).run init ops') :=
    ((spec R cap).trace_safe init ops' (inv_init R cap)).1
  have e' : (sys R cap).run init ops' = run R cap full init ops := e
  rw [e'] at h
  exact (h : Inv R cap (run R cap full init ops)).good

theorem sc26_safe_agree : @sc26_safe_via_gate = @sc26_safe := rfl

theorem halt_freezes_via_gate (R : Roles) (cap : ℕ) (s : St) (ops : List Op)
    (hops : ∀ o ∈ ops, legal R o) (hh : s.halted = true) :
    (run R cap full s ops).net = s.net ∧
      ∀ e ∈ (run R cap full s ops).bank, e ∈ s.bank ∨ e ∈ s.net :=
  foldl_rel_fixed (step R cap full) (legal R) (fun s => s.halted = true)
    (fun a b => b.net = a.net ∧ ∀ e ∈ b.bank, e ∈ a.bank ∨ e ∈ a.net)
    (fun s => ⟨rfl, fun e he => Or.inl he⟩)
    (fun a b c hab hbc => ⟨hbc.1.trans hab.1, fun e he => by
      rcases hbc.2 e he with h | h
      · exact hab.2 e h
      · right; rw [← hab.1]; exact h⟩)
    (fun s o ho hs => by
      obtain ⟨h1, h2, h3⟩ := step_halted R cap s o ho hs
      exact ⟨⟨h1, h3⟩, h2⟩) hh ops hops

theorem halt_freezes_agree : @halt_freezes_via_gate = @halt_freezes := rfl
end ControlStack.SC26

namespace ControlStack.SC27Chain
open ControlStack.Gate

theorem sc27_safe_via_gate (E : Env) (ops : List Op)
    (hinj : Set.InjOn (chainHead E.H E.h0) {l | l ∈ (run E full init ops).accepted ∨
      ∃ a ∈ (run E full init ops).anchors, a.2 = some l}) :
    ∀ m ∈ (run E full init ops).accepted, ∃ a ∈ (run E full init ops).anchors, a.2 = some m := by
  have h : Inv E (run E full init ops) := ((spec E).trace_safe init ops (inv_init E)).1
  intro m hm
  obtain ⟨a, ha, l, hl, heq⟩ := h.acc m hm
  refine ⟨a, ha, ?_⟩
  rw [hl, hinj (Or.inr ⟨a, ha, hl⟩) (Or.inl hm) heq]

theorem sc27_safe_agree : @sc27_safe_via_gate = @sc27_safe := rfl

theorem halt_freezes_via_gate (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) :
    run E full s ops = s :=
  foldl_fixed (step E full) (fun s => s.halted = true) (fun s o hs => step_halted E s o hs) hh ops

theorem halt_freezes_agree : @halt_freezes_via_gate = @halt_freezes := rfl
end ControlStack.SC27Chain

namespace ControlStack.SC28
open ControlStack.Gate

theorem sc28_safe_via_gate (admins : List ℕ) (G : ℕ) (ops : List Op) (hops : ∀ o ∈ ops, legal o) :
    Good G (run admins G full init ops) := by
  obtain ⟨ops', e⟩ := foldl_legal (step admins G full) legal ops hops init
  have h : Inv G ((sys admins G).run init ops') :=
    ((spec admins G).trace_safe init ops' (inv_init G)).1
  have e' : (sys admins G).run init ops' = run admins G full init ops := e
  rw [e'] at h
  exact (h : Inv G (run admins G full init ops)).good

theorem sc28_safe_agree : @sc28_safe_via_gate = @sc28_safe := rfl

theorem halt_freezes_via_gate (admins : List ℕ) (G : ℕ) (s : St) (ops : List Op)
    (hh : s.halted = true) : (run admins G full s ops).usage = s.usage :=
  foldl_field_fixed (step admins G full) (fun s => s.halted = true) St.usage
    (fun s o hs => step_halted admins G s o hs) hh ops

theorem halt_freezes_agree : @halt_freezes_via_gate = @halt_freezes := rfl
end ControlStack.SC28

#print axioms ControlStack.SC06.sc06_safe_via_gate
#print axioms ControlStack.SC06.halt_freezes_via_gate
#print axioms ControlStack.SC08.sc08_safe_via_gate
#print axioms ControlStack.SC08.halt_freezes_via_gate
#print axioms ControlStack.SC09.sc09_safe_via_gate
#print axioms ControlStack.SC09.halt_freezes_via_gate
#print axioms ControlStack.SC10.sc10_safe_via_gate
#print axioms ControlStack.SC10.halt_freezes_via_gate
#print axioms ControlStack.SC12.sc12_safe_via_gate
#print axioms ControlStack.SC12.halt_freezes_via_gate
#print axioms ControlStack.EvalIntegrity.sc21_safe_via_gate
#print axioms ControlStack.EvalIntegrity.halt_freezes_via_gate
#print axioms ControlStack.SC15.sc15_safe_via_gate
#print axioms ControlStack.SC15.halt_freezes_via_gate
#print axioms ControlStack.SC16.sc16_safe_via_gate
#print axioms ControlStack.SC16.halt_freezes_via_gate
#print axioms ControlStack.SC19.sc19_safe_via_gate
#print axioms ControlStack.SC19.halt_freezes_via_gate
#print axioms ControlStack.SC20.sc20_safe_via_gate
#print axioms ControlStack.SC20.halt_freezes_via_gate
#print axioms ControlStack.SC23.sc23_safe_via_gate
#print axioms ControlStack.SC23.halt_freezes_via_gate
#print axioms ControlStack.SC23Isolation.sc23_isolated_safe_via_gate
#print axioms ControlStack.SC23Isolation.halt_freezes_via_gate
#print axioms ControlStack.SC25.sc25_safe_via_gate
#print axioms ControlStack.SC25.halt_freezes_via_gate
#print axioms ControlStack.SC17.sc17_safe_via_gate
#print axioms ControlStack.SC17.halt_freezes_via_gate
#print axioms ControlStack.SC14.sc14_safe_via_gate
#print axioms ControlStack.SC14.halt_freezes_via_gate
#print axioms ControlStack.SC18.sc18_safe_via_gate
#print axioms ControlStack.SC18.halt_freezes_via_gate
#print axioms ControlStack.EgressGate.trace_safe_via_gate
#print axioms ControlStack.SC26.sc26_safe_via_gate
#print axioms ControlStack.SC27Chain.sc27_safe_via_gate
#print axioms ControlStack.SC27Chain.halt_freezes_via_gate
#print axioms ControlStack.SC28.sc28_safe_via_gate
#print axioms ControlStack.SC28.halt_freezes_via_gate
#print axioms ControlStack.SC26.halt_freezes_via_gate

namespace ControlStack.SC23IsolationV2
open ControlStack.Gate ControlStack.Authenticated

theorem sc23v2_safe_authenticated_via_gate (E : Env) (U : List ℕ) (hU : ∀ u ∈ U, u ∉ E.users)
    (ops : List (ℕ × Op)) :
    ∀ x ∈ ((authed (raw E) claim).run init ops).executed, x.tool ∈ E.sensitive → x.tainted = true →
      ∃ c n, c ∈ E.users ∧ c ∉ U ∧ (c, Op.confirm c n x.tool x.vals) ∈ ops := by
  intro x hx hs ht
  rw [authed_run, raw_run] at hx
  have hinv : Inv E (run E full init (applied claim ops)) :=
    ((spec E).trace_safe init (applied claim ops) (inv_init E)).1
  obtain ⟨n, _, cf, hcf, _, htool, hvals, hby⟩ := hinv.exec x hx hs ht
  rcases run_confs E (applied claim ops) init cf hcf with h | h
  · simp [init] at h
  · have hiss := claim_issued_by claim ops _ cf.by_ h rfl
    rw [htool, hvals] at hiss
    exact ⟨cf.by_, cf.n, hby, fun hu => hU _ hu hby, hiss⟩

theorem sc23v2_safe_authenticated_agree :
    @sc23v2_safe_authenticated_via_gate = @sc23v2_safe_authenticated := rfl
end ControlStack.SC23IsolationV2

#print axioms ControlStack.SC23IsolationV2.sc23v2_safe_authenticated_via_gate

