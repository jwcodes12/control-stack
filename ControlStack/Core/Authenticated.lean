/-
Authenticated issuers for any gate: closes review finding 1 structurally (REVIEW-PACKET-2026-10-09.md §0.1).

In every scenario model, an operation carries a CLAIMED identity (a caller field), and `step` reads it as the act of
that principal. Nothing distinguishes a forged claim from a genuine one; "credential separation" is an informal
premise. This file makes the premise precise.

- An operation is now issued by a TRUE issuer: a pair `(issuer, o)`. The issuer is what the platform reports (e.g.
  `SO_PEERCRED`, a workload identity); it is not chosen per operation by the adversary. The adversary controls only
  operations whose issuer lies in an untrusted set `U`.
- `authed G claim` applies `o` only if it claims no identity or claims exactly its issuer (`Authentic`); otherwise
  the operation is a no-op.

Results:
- `authed_run`: running `authed G claim` equals running `G` on the authenticated sub-trace `applied claim ops`, so
  every theorem about `G`'s traces applies to it;
- `claim_issued_by`: every applied operation that claims identity `x` was issued by `x` (it occurs in the trace as
  `(x, o)`); `trusted_claim_not_adversary`: so if `x ∉ U`, the adversary did not issue it;
- `authedSpec`: any `Spec` of `G` lifts to `authed G claim` (same invariant, same effects: rejected operations change
  nothing), with `authed_trace_safe` as the trace-level corollary.

The SC-26 instance (`sc26_safe_authenticated`, and the forged-approval witness) is in
`Scenarios/SC26Authenticated.lean`.

What this does NOT do: it does not prove that a real platform's identity mechanism provides `issuer`; that is now the
single, explicit correspondence premise "the OS-reported identity is the issuer". It also does not authenticate
operations whose `claim` is `none` (environment events and gate-internal steps must be identity-free by design).
No new mathematics.
-/
import Mathlib.Tactic
import ControlStack.Core.Gate

namespace ControlStack.Authenticated

open ControlStack.Gate

variable {St Op Eff : Type}

/-- the authentication guard: an operation claiming identity `x` is applied only if its true issuer is `x` -/
def Authentic (claim : Op → Option ℕ) (io : ℕ × Op) : Prop := claim io.2 = none ∨ claim io.2 = some io.1

instance (claim : Op → Option ℕ) : DecidablePred (Authentic claim) :=
  fun io => inferInstanceAs (Decidable (claim io.2 = none ∨ claim io.2 = some io.1))

/-- the gate with authenticated issuers -/
def authed (G : System St Op Eff) (claim : Op → Option ℕ) : System St (ℕ × Op) Eff where
  step s io := if Authentic claim io then G.step s io.2 else s
  effects := G.effects

/-- the operations actually applied: the authentic ones, without their issuers -/
def applied (claim : Op → Option ℕ) (ops : List (ℕ × Op)) : List Op :=
  (ops.filter (fun io => decide (Authentic claim io))).map Prod.snd

/-- **Reduction.** The authenticated gate runs `G` on the authenticated sub-trace. -/
theorem authed_run (G : System St Op Eff) (claim : Op → Option ℕ) (s : St) (ops : List (ℕ × Op)) :
    (authed G claim).run s ops = G.run s (applied claim ops) := by
  induction ops generalizing s with
  | nil => rfl
  | cons io ops ih =>
    by_cases ha : Authentic claim io
    · simp only [System.run_cons, applied, List.filter_cons, ha, decide_true, ite_true, List.map_cons] at ih ⊢
      rw [show (authed G claim).step s io = G.step s io.2 by simp [authed, ha]]
      exact ih _
    · simp only [System.run_cons, applied, List.filter_cons, ha, decide_false] at ih ⊢
      rw [show (authed G claim).step s io = s by simp [authed, ha]]
      exact ih _

/-- **Claims are issued by the claimed principal.** Every applied operation claiming `x` occurs in the trace with
issuer `x`. -/
theorem claim_issued_by (claim : Op → Option ℕ) (ops : List (ℕ × Op)) (o : Op) (x : ℕ)
    (ho : o ∈ applied claim ops) (hc : claim o = some x) : (x, o) ∈ ops := by
  simp only [applied, List.mem_map, List.mem_filter, decide_eq_true_eq] at ho
  obtain ⟨⟨i, o'⟩, ⟨hmem, ha⟩, rfl⟩ := ho
  rcases ha with ha | ha
  · simp_all
  · have : i = x := by simp_all
    subst this; exact hmem

/-- **Trusted identities come only from trusted issuers.** If the adversary issues only from `U`, an applied operation
claiming an identity outside `U` was issued by that (trusted) principal itself, not by the adversary. -/
theorem trusted_claim_not_adversary (claim : Op → Option ℕ) (U : List ℕ) (ops : List (ℕ × Op)) (o : Op) (x : ℕ)
    (ho : o ∈ applied claim ops) (hc : claim o = some x) (hx : x ∉ U) :
    ∃ io ∈ ops, io.1 = x ∧ io.1 ∉ U ∧ io.2 = o :=
  ⟨(x, o), claim_issued_by claim ops o x ho hc, rfl, hx, rfl⟩

/-- **Lifting.** Any spec of `G` is a spec of `authed G claim`: rejected operations change nothing, accepted ones are
steps of `G`, and the effect log is `G`'s. -/
def authedSpec (G : System St Op Eff) (claim : Op → Option ℕ) (S : Spec G) : Spec (authed G claim) where
  Inv := S.Inv
  ok := S.ok
  step_inv s io h := by
    by_cases ha : Authentic claim io
    · simpa [authed, ha] using S.step_inv s io.2 h
    · simpa [authed, ha] using h
  log_prefix s io := by
    by_cases ha : Authentic claim io
    · simpa [authed, ha] using S.log_prefix s io.2
    · simp [authed, ha]
  inv_ok := S.inv_ok

/-- trace safety for the authenticated gate, inherited from `G`'s spec -/
theorem authed_trace_safe (G : System St Op Eff) (claim : Op → Option ℕ) (S : Spec G) (s : St) (ops : List (ℕ × Op))
    (h : S.Inv s) :
    S.Inv ((authed G claim).run s ops) ∧ G.effects s <+: G.effects ((authed G claim).run s ops) ∧
      ∀ e ∈ G.effects ((authed G claim).run s ops), S.ok ((authed G claim).run s ops) e :=
  (authedSpec G claim S).trace_safe s ops h

end ControlStack.Authenticated
