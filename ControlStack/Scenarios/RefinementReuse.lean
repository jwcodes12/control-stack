import ControlStack.Core.RefinementTransferInv
import ControlStack.Scenarios.SC07Refinement
import ControlStack.Scenarios.SC18Refinement
import ControlStack.Scenarios.SC28Refinement
import ControlStack.Scenarios.SC26Refinement
import ControlStack.Scenarios.SC16RefinementReuse
import ControlStack.Scenarios.SC25RefinementReuse

/-!
Refinement reuse bridges. The pinned `simulation_run` of SC-07, SC-18, SC-26 and SC-28 is
the invariant-guarded induction `RefinementTransferInv.run_simulation_guarded`; each bridge
re-derives it from the pinned one-step `simulation` and invariant preservation, and a `rfl`
check confirms the bridged statement is the pinned one. `concrete_safe` is then re-derived
with the pinned proof text, using the bridged lemma. SC-16 and SC-25 use the existing bridges
in `SC16RefinementReuse` and `SC25RefinementReuse`.

Pinned files are unchanged. These are model-to-model facts; they do not say the real
registry, receiver or kernel implements the concrete model. SC-27's simulation needs a
trace-level injectivity hypothesis (`TraceInj`), not a per-step invariant, and is not bridged.
-/

namespace ControlStack.SC07Refinement
open ControlStack.RefinementTransfer ControlStack.RefinementTransferInv

theorem simulation_run_via_transfer (K : CCfg) (hK : K.quotaRule = true) (s : CSt) (ops : List COp) (h : CInv s) :
    α (runC K s ops) = SC07Liveness.run (envOf K) SC07Liveness.full (α s) (absTrace K s ops) := by
  have htrace : ∀ (s : CSt) (ops : List COp), absTrace K s ops = emitTrace (stepC K) (opsOf K) s ops := by
    intro s ops
    induction ops generalizing s with
    | nil => rfl
    | cons o ops ih =>
      change opsOf K s o ++ absTrace K (stepC K s o) ops = opsOf K s o ++ emitTrace (stepC K) (opsOf K) (stepC K s o) ops
      rw [ih]
  rw [htrace s ops]
  exact (run_simulation_guarded (stepC K) (SC07Liveness.step (envOf K) SC07Liveness.full) α (opsOf K) CInv (fun _ => True)
    (fun s o _ hi => cinv_step K hK s o hi) (fun s o _ hi => simulation K hK s o hi) s ops (fun _ _ => trivial) h).1

theorem simulation_run_agree : @simulation_run_via_transfer = @simulation_run := rfl

theorem concrete_safe_via_transfer (K : CCfg) (hK : K.quotaRule = true) (ops : List COp) :
    (∀ r ∈ (runC K cinit ops).fwd, (r.ip, r.port) ∈ K.allow) ∧
      ∀ w, payloadIn (runC K cinit ops).fwd w ≤ K.Q - 1 := by
  have e := simulation_run_via_transfer K hK cinit ops cinv_init
  rw [α_cinit] at e
  obtain ⟨hd, hw⟩ := SC07Liveness.sc07_safe (envOf K) (absTrace K cinit ops)
  rw [← e] at hd hw
  refine ⟨fun r hr => ?_, fun w => by rw [← wsum_α]; exact hw w⟩
  obtain ⟨⟨a, b⟩, hab, he⟩ := List.mem_map.1 (hd (toFwd r) (List.mem_map.2 ⟨r, hr, rfl⟩))
  obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 he
  exact hab

theorem concrete_safe_agree : @concrete_safe_via_transfer = @concrete_safe := rfl

end ControlStack.SC07Refinement

namespace ControlStack.SC18Refinement
open ControlStack.RefinementTransfer ControlStack.RefinementTransferInv
open ControlStack.SC18Liveness

theorem simulation_run_via_transfer (admins : List ℕ) (T : ℕ) (s : CSt) (ops : List COp) (h : CInv s) :
    α T (runC real T s ops) = Resume.run admins T (α T s) (absTrace T s ops) := by
  have htrace : ∀ (s : CSt) (ops : List COp), absTrace T s ops = emitTrace (stepC real T) (opsOf T) s ops := by
    intro s ops
    induction ops generalizing s with
    | nil => rfl
    | cons o ops ih =>
      change opsOf T s o ++ absTrace T (stepC real T s o) ops = opsOf T s o ++ emitTrace (stepC real T) (opsOf T) (stepC real T s o) ops
      rw [ih]
  rw [htrace s ops]
  exact (run_simulation_guarded (stepC real T) (Resume.step admins T) (α T) (opsOf T) CInv (fun _ => True)
    (fun s o _ hi => cinv_step T s o hi) (fun s o _ hi => simulation admins T s o hi) s ops (fun _ _ => trivial) h).1

theorem simulation_run_agree : @simulation_run_via_transfer = @simulation_run := rfl

theorem concrete_safe_via_transfer (T : ℕ) (ops : List COp) :
    (∀ r ∈ (runC real T cinit ops).released, Resume.RelOk T (α T (runC real T cinit ops)) r) ∧
      ((runC real T cinit ops).released.map SC18.Rel.id).Nodup := by
  have hs := simulation_run_via_transfer [] T cinit ops cinv_init
  have key := Resume.resume_safe [] T (absTrace T cinit ops)
  rw [← α_cinit T, ← hs] at key
  exact key

theorem concrete_safe_agree : @concrete_safe_via_transfer = @concrete_safe := rfl

end ControlStack.SC18Refinement

namespace ControlStack.SC28Refinement
open ControlStack.RefinementTransfer ControlStack.RefinementTransferInv

theorem simulation_run_via_transfer (G : ℕ) (s : CSt) (ops : List COp) (h : CInv s) :
    α (runC G s ops) = SC28.run [0] G SC28.full (α s) (absTrace G s ops) := by
  have htrace : ∀ (s : CSt) (ops : List COp), absTrace G s ops = emitTrace (stepC G) (opsOf G) s ops := by
    intro s ops
    induction ops generalizing s with
    | nil => rfl
    | cons o ops ih =>
      change opsOf G s o ++ absTrace G (stepC G s o) ops = opsOf G s o ++ emitTrace (stepC G) (opsOf G) (stepC G s o) ops
      rw [ih]
  rw [htrace s ops]
  exact (run_simulation_guarded (stepC G) (SC28.step [0] G SC28.full) α (opsOf G) CInv (fun _ => True)
    (fun s o _ hi => cinv_step G s o hi) (fun s o _ hi => simulation G s o hi) s ops (fun _ _ => trivial) h).1

theorem simulation_run_agree : @simulation_run_via_transfer = @simulation_run := rfl

theorem concrete_safe_via_transfer (G : ℕ) (ops : List COp) : SC28.Good G (α (runC G cinit ops)) := by
  rw [simulation_run_via_transfer G cinit ops cinv_init, α_cinit]
  exact SC28.sc28_safe [0] G _ (absTrace_legal G cinit ops)

theorem concrete_safe_agree : @concrete_safe_via_transfer = @concrete_safe := rfl

end ControlStack.SC28Refinement

namespace ControlStack.SC26Refinement
open ControlStack.RefinementTransfer ControlStack.RefinementTransferInv
open ControlStack.SC26

theorem simulation_run_via_transfer (R : Roles) (cap : ℕ) (s : CSt) (ops : List COp)
    (hops : ∀ o ∈ ops, legalC R o) (h : CInv s) :
    α (runC R cap true s ops) = run R cap full (α s) (absTrace R cap s ops) ∧
      CInv (runC R cap true s ops) := by
  have htrace : ∀ (s : CSt) (ops : List COp),
      absTrace R cap s ops = emitTrace (stepC R cap true) opsOf s ops := by
    intro s ops
    induction ops generalizing s with
    | nil => rfl
    | cons o ops ih =>
      change opsOf s o ++ absTrace R cap (stepC R cap true s o) ops =
        opsOf s o ++ emitTrace (stepC R cap true) opsOf (stepC R cap true s o) ops
      rw [ih]
  rw [htrace s ops]
  exact run_simulation_guarded (stepC R cap true) (step R cap full) α opsOf CInv (legalC R)
    (fun s o ho hi => (simulation R cap s o ho hi).2)
    (fun s o ho hi => (simulation R cap s o ho hi).1) s ops hops h

theorem simulation_run_agree : @simulation_run_via_transfer = @simulation_run := rfl

theorem concrete_safe_via_transfer (R : Roles) (cap : ℕ) (ops : List COp) (hops : ∀ o ∈ ops, legalC R o) :
    Good R cap (α (runC R cap true cinit ops)) := by
  rw [(simulation_run_via_transfer R cap cinit ops hops cinv_init).1, α_init]
  exact sc26_safe R cap _ (absTrace_legal R cap cinit ops hops)

theorem concrete_safe_agree : @concrete_safe_via_transfer = @concrete_safe := rfl
end ControlStack.SC26Refinement

namespace ControlStack.SC16Refinement
open ControlStack ControlStack.SC16

theorem concrete_safe_via_transfer (R : Roles) (h : ℕ → ℕ) (ops : List COp) : Good R h (α (runC R h false cinit ops)) := by
  rw [simulation_run_via_transfer, α_cinit]
  exact sc16_safe R h _

theorem concrete_reviewed_content_via_transfer (R : Roles) (h : ℕ → ℕ) (ops : List COp)
    (hinj : Set.InjOn h {c | (∃ e ∈ (α (runC R h false cinit ops)).deployed, e.content = c) ∨
      ∃ rv ∈ (α (runC R h false cinit ops)).reviews, rv.content = c}) :
    ∀ e ∈ (α (runC R h false cinit ops)).deployed, ∃ rv ∈ (α (runC R h false cinit ops)).reviews,
      rv.content = e.content ∧ rv.reviewer ∈ R.reviewers ∧ rv.reviewer ≠ rv.stager := by
  rw [simulation_run_via_transfer, α_cinit] at hinj ⊢
  exact sc16_reviewed_content R h _ hinj

theorem concrete_reviewed_content_agree :
    @concrete_reviewed_content_via_transfer = @concrete_reviewed_content := rfl

theorem concrete_safe_agree : @concrete_safe_via_transfer = @concrete_safe := rfl
end ControlStack.SC16Refinement

namespace ControlStack.SC25Refinement
open ControlStack ControlStack.SC25

theorem concrete_safe_via_transfer (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List COp) :
    Good R h cls (α (runC R h cls false cinit ops)) := by
  rw [simulation_run_via_transfer, α_cinit]
  exact sc25_safe R h cls _

theorem concrete_safe_agree : @concrete_safe_via_transfer = @concrete_safe := rfl

theorem concrete_content_safe_via_transfer (R : Roles) (h : ℕ → ℕ) (cls : ℕ → Bool) (ops : List COp)
    (hinj : Set.InjOn h {c | ∃ it ∈ (runC R h cls false cinit ops).items, it.content = c}) :
    ∀ e ∈ (runC R h cls false cinit ops).effects, ∃ a ∈ (runC R h cls false cinit ops).auditLog,
      a.id = e.id ∧ a.content = e.content ∧ a.pass = true ∧ a.by_ ∈ R.auditors := by
  intro e he
  have hg := concrete_safe_via_transfer R h cls ops
  have hc := cinv_run R h cls cinit ops (cinv_init h)
  have he' : toExec e ∈ (α (runC R h cls false cinit ops)).executed := List.mem_map.2 ⟨e, he, rfl⟩
  obtain ⟨⟨v, hv, hid, hpass, hd, b, hby, hb⟩, -⟩ := hg.1 _ he'
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 (List.mem_of_mem_take hv)
  obtain ⟨had, it₁, hit₁, hc₁⟩ := hc.arow a ha
  obtain ⟨it₂, hit₂, hc₂⟩ := hc.erow e he
  refine ⟨a, ha, hid, hinj ⟨it₁, hit₁, hc₁⟩ ⟨it₂, hit₂, hc₂⟩ (by rw [had]; exact hd), hpass, ?_⟩
  simp only [toVerdict, Option.some.injEq] at hby
  rw [hby]; exact hb

theorem concrete_content_safe_agree :
    @concrete_content_safe_via_transfer = @concrete_content_safe := rfl
end ControlStack.SC25Refinement

#print axioms ControlStack.SC07Refinement.simulation_run_via_transfer
#print axioms ControlStack.SC07Refinement.concrete_safe_via_transfer
#print axioms ControlStack.SC18Refinement.simulation_run_via_transfer
#print axioms ControlStack.SC18Refinement.concrete_safe_via_transfer
#print axioms ControlStack.SC28Refinement.simulation_run_via_transfer
#print axioms ControlStack.SC28Refinement.concrete_safe_via_transfer
#print axioms ControlStack.SC26Refinement.simulation_run_via_transfer
#print axioms ControlStack.SC26Refinement.concrete_safe_via_transfer
#print axioms ControlStack.SC16Refinement.concrete_safe_via_transfer
#print axioms ControlStack.SC16Refinement.concrete_reviewed_content_via_transfer
#print axioms ControlStack.SC25Refinement.concrete_safe_via_transfer
#print axioms ControlStack.SC25Refinement.concrete_content_safe_via_transfer
