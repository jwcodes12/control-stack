/-
Authenticated issuers for logged trusted acts: the generic lemma behind the scenario instances of
`Core/Authenticated.lean`.

Most scenario models record a trusted act (a review, an approval, a verdict, a confirmation, a lease) in a list that
only grows through operations claiming the acting principal. For such a model:

- `authRun step claim s ops`: the authenticated run of any step function (an operation claiming identity `x` is
  applied only if issued by `x`). `authRun_eq` says it IS the plain run on the authenticated sub-trace
  `applied claim ops`, so every safety theorem of the scenario applies unchanged.
- `issued_of_mem_log`: if every record entering the log comes from an operation claiming some identity `c` with
  property `P c o x` (typically: `o` is the act, `c` is the record's actor, `c` has the trusted role), then every
  record in the final log has an operation `(c, o)` in the trace, ISSUED by `c`, with `P c o x`.
- `issued_trusted`: if moreover `P` forces `c` into a trusted set `T` disjoint from the adversary's issuers `U`, that
  issuer is not the adversary.

These are inductions over the trace; no new mathematics. What remains a premise is that the platform's reported
identity is the issuer (Core/Authenticated.lean).
-/
import Mathlib.Tactic
import ControlStack.Core.Authenticated

namespace ControlStack.AuthenticatedLog

open ControlStack.Gate ControlStack.Authenticated

variable {St Op R : Type}

/-- the authenticated run of a step function (effects are irrelevant here) -/
def authRun (step : St → Op → St) (claim : Op → Option ℕ) (s : St) (ops : List (ℕ × Op)) : St :=
  (authed (⟨step, fun _ => ([] : List Unit)⟩ : System St Op Unit) claim).run s ops

/-- **Reduction:** the authenticated run is the plain run on the authenticated sub-trace -/
theorem authRun_eq (step : St → Op → St) (claim : Op → Option ℕ) (s : St) (ops : List (ℕ × Op)) :
    authRun step claim s ops = (applied claim ops).foldl step s :=
  authed_run _ claim s ops

/-- records in a log that grows only through steps satisfying `P` come from the initial log or from such a step -/
theorem log_origin (step : St → Op → St) (rec : St → List R) (P : Op → R → Prop)
    (hstep : ∀ s o x, x ∈ rec (step s o) → x ∈ rec s ∨ P o x) :
    ∀ (L : List Op) (s : St) (x : R), x ∈ rec (L.foldl step s) → x ∈ rec s ∨ ∃ o ∈ L, P o x := by
  intro L
  induction L with
  | nil => intro s x hx; exact Or.inl hx
  | cons o L ih =>
    intro s x hx
    rcases ih (step s o) x hx with h | ⟨o', ho', hp⟩
    · rcases hstep s o x h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨o, List.mem_cons_self, h⟩
    · exact Or.inr ⟨o', List.mem_cons_of_mem _ ho', hp⟩

/-- **Logged trusted acts were issued by their actor.** -/
theorem issued_of_mem_log (step : St → Op → St) (claim : Op → Option ℕ) (rec : St → List R)
    (P : ℕ → Op → R → Prop)
    (hstep : ∀ s o x, x ∈ rec (step s o) → x ∈ rec s ∨ ∃ c, claim o = some c ∧ P c o x)
    (s0 : St) (h0 : rec s0 = []) (ops : List (ℕ × Op)) :
    ∀ x ∈ rec (authRun step claim s0 ops), ∃ c o, (c, o) ∈ ops ∧ P c o x := by
  intro x hx
  rw [authRun_eq] at hx
  rcases log_origin step rec (fun o x => ∃ c, claim o = some c ∧ P c o x) hstep _ s0 x hx with h | ⟨o, ho, c, hc, hp⟩
  · simp [h0] at h
  · exact ⟨c, o, claim_issued_by claim ops o c ho hc, hp⟩

/-- **...and not by the adversary**, when the act requires a trusted role disjoint from the adversary's issuers -/
theorem issued_trusted (step : St → Op → St) (claim : Op → Option ℕ) (rec : St → List R)
    (P : ℕ → Op → R → Prop) (T U : List ℕ)
    (hstep : ∀ s o x, x ∈ rec (step s o) → x ∈ rec s ∨ ∃ c, claim o = some c ∧ P c o x)
    (hT : ∀ c o x, P c o x → c ∈ T) (hU : ∀ u ∈ U, u ∉ T)
    (s0 : St) (h0 : rec s0 = []) (ops : List (ℕ × Op)) :
    ∀ x ∈ rec (authRun step claim s0 ops), ∃ c o, (c, o) ∈ ops ∧ c ∉ U ∧ P c o x := by
  intro x hx
  obtain ⟨c, o, hmem, hp⟩ := issued_of_mem_log step claim rec P hstep s0 h0 ops x hx
  exact ⟨c, o, hmem, fun hu => hU c hu (hT c o x hp), hp⟩

/-- every operation of the authenticated sub-trace occurs in the trace -/
theorem mem_of_applied (claim : Op → Option ℕ) (ops : List (ℕ × Op)) (o : Op) (ho : o ∈ applied claim ops) :
    ∃ i, (i, o) ∈ ops := by
  simp only [applied, List.mem_map, List.mem_filter] at ho
  obtain ⟨⟨i, o'⟩, ⟨hm, -⟩, rfl⟩ := ho
  exact ⟨i, hm⟩

/-- an applied operation claiming an identity was issued by it -/
theorem applied_claim (claim : Op → Option ℕ) (ops : List (ℕ × Op)) (o : Op) (ho : o ∈ applied claim ops) :
    claim o = none ∨ ∃ i, claim o = some i ∧ (i, o) ∈ ops := by
  cases hc : claim o with
  | none => exact Or.inl rfl
  | some i => exact Or.inr ⟨i, rfl, claim_issued_by claim ops o i ho hc⟩

end ControlStack.AuthenticatedLog

#print axioms ControlStack.AuthenticatedLog.authRun_eq
#print axioms ControlStack.AuthenticatedLog.issued_of_mem_log
#print axioms ControlStack.AuthenticatedLog.issued_trusted
