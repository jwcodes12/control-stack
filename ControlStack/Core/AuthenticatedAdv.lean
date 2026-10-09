/-
A formally CONSTRAINED adversary for `Core/Authenticated.lean` (review: Gemini, "`trusted_claim_not_adversary` is
trivial because the trace is unconstrained").

`Authenticated` quantifies over every issued trace, and its consequence ("the adversary did not issue it") was a
reading of `x ∉ U`. Here the adversary is a separate object. A trace is admissible (`AdvTrace U hon ops`) when it is an
order-preserving interleaving (`Shuffle`) of
- an HONEST SCRIPT `hon`: the operations the trusted principals actually issue, and
- an ADVERSARY SCRIPT `adv`, every operation of which is issued from the untrusted set `U` (the adversary's physical
  capability: it can only act through identities in `U`).

The adversary script is arbitrary: any length, any contents, any claims, interleaved anywhere. An adaptive adversary
is covered pointwise, since each realised run is one such script.

Results:
- `Shuffle.mem`: every operation of the interleaving comes from one of the two scripts;
- `applied_trusted_claim_from_honest`: every APPLIED operation claiming an identity outside `U` is an operation of the
  honest script, issued by that principal. The conclusion is about the honest script, not about `U`-membership;
- `adversary_acts_only_as_U`: every applied adversary operation claims no identity or an identity in `U`;
- SC-26 corollary `sc26_consent_from_honest_script`: if `U` excludes the approvers and the gate, and the honest script
  contains no gate-issued direct bank call, then every payment is backed by an `approve` of exactly its payload that
  occurs in the HONEST SCRIPT, issued by an approver. The adversary can schedule, request, execute, retry and forge
  claims, but cannot manufacture consent;
- `honest_payment_admissible` (non-vacuity: an admissible trace pays) and `forged_claim_admissible_pays_nothing`.

Residual premise: issuer authenticity, i.e. the platform-reported identity is the true issuer, so the adversary
really is confined to `U`. That is now the definition of the adversary class, stated once. No new mathematics.
-/
import Mathlib.Tactic
import ControlStack.Core.Authenticated
import ControlStack.Scenarios.SC26Authenticated

namespace ControlStack.AuthenticatedAdv

open ControlStack.Gate ControlStack.Authenticated

/-- order-preserving interleaving of two lists -/
inductive Shuffle {α : Type} : List α → List α → List α → Prop where
  | nil : Shuffle [] [] []
  | left (a : α) {l r m : List α} : Shuffle l r m → Shuffle (a :: l) r (a :: m)
  | right (a : α) {l r m : List α} : Shuffle l r m → Shuffle l (a :: r) (a :: m)

theorem Shuffle.mem {α : Type} {l r m : List α} (h : Shuffle l r m) {x : α} (hx : x ∈ m) : x ∈ l ∨ x ∈ r := by
  induction h with
  | nil => simp at hx
  | left a _ ih =>
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Or.inl List.mem_cons_self
    · rcases ih hx with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h
  | right a _ ih =>
    rcases List.mem_cons.1 hx with rfl | hx
    · exact Or.inr List.mem_cons_self
    · rcases ih hx with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

/-- **The adversary class**: the trace interleaves the honest script with an adversary script issued only from `U` -/
def AdvTrace {Op : Type} (U : List ℕ) (hon ops : List (ℕ × Op)) : Prop :=
  ∃ adv : List (ℕ × Op), (∀ io ∈ adv, io.1 ∈ U) ∧ Shuffle hon adv ops

/-- **Trusted claims come from the honest script.** In an admissible trace, every applied operation claiming an
identity `x ∉ U` is an operation of the honest script, issued by `x`. -/
theorem applied_trusted_claim_from_honest {Op : Type} (claim : Op → Option ℕ) (U : List ℕ) (hon ops : List (ℕ × Op))
    (hadv : AdvTrace U hon ops) (o : Op) (x : ℕ) (ho : o ∈ applied claim ops) (hc : claim o = some x) (hx : x ∉ U) :
    (x, o) ∈ hon := by
  obtain ⟨adv, hU, hsh⟩ := hadv
  rcases hsh.mem (claim_issued_by claim ops o x ho hc) with h | h
  · exact h
  · exact absurd (hU _ h) hx

/-- **The adversary acts only as `U`.** Every applied operation of the adversary script claims no identity or an
identity in `U`. -/
theorem adversary_acts_only_as_U {Op : Type} (claim : Op → Option ℕ) (U : List ℕ) (adv : List (ℕ × Op))
    (hU : ∀ io ∈ adv, io.1 ∈ U) (io : ℕ × Op) (hio : io ∈ adv) (ha : Authentic claim io) :
    claim io.2 = none ∨ ∃ x ∈ U, claim io.2 = some x := by
  rcases ha with h | h
  · exact Or.inl h
  · exact Or.inr ⟨io.1, hU io hio, h⟩

/-! ## SC-26 corollary -/

open ControlStack.SC26 ControlStack.SC26Authenticated

/-- **Consent comes from the honest script.** If `U` excludes the approvers and the gate, and the honest script has no
gate-issued direct bank call, then in every admissible trace the authenticated SC-26 run satisfies `Good`, and every
payment is backed by an `approve` of exactly its payload IN THE HONEST SCRIPT, issued by an approver. -/
theorem sc26_consent_from_honest_script (R : Roles) (cap : ℕ) (U : List ℕ) (hon ops : List (ℕ × Op))
    (hadv : AdvTrace U hon ops) (hUa : ∀ u ∈ U, u ∉ R.approvers) (hUg : R.gate ∉ U)
    (hhon : ∀ io ∈ hon, ∀ c k tx, io.2 = .bankCall c k tx → io.1 ≠ R.gate) :
    Good R cap ((authed (raw R cap) claim).run init ops) ∧
      ∀ e ∈ ((authed (raw R cap) claim).run init ops).bank,
        ∃ a, a ∈ R.approvers ∧ (a, Op.approve a e.1 e.2) ∈ hon := by
  obtain ⟨adv, hU, hsh⟩ := hadv
  have hgate : ∀ io ∈ ops, ∀ c k tx, io.2 = .bankCall c k tx → io.1 ≠ R.gate := by
    intro io hio c k tx hb
    rcases hsh.mem hio with h | h
    · exact hhon io h c k tx hb
    · intro hg; exact hUg (hg ▸ hU io h)
  obtain ⟨hgood, hpay⟩ := sc26_safe_authenticated R cap U ops hUa hgate
  refine ⟨hgood, fun e he => ?_⟩
  obtain ⟨a, ha, haU, hmem⟩ := hpay e he
  rcases hsh.mem hmem with h | h
  · exact ⟨a, ha, h⟩
  · exact absurd (hU _ h) haU

/-! ## Witnesses (SC-26 roles `R0`: agent 1, approver 2) -/

/-- the honest approver's script -/
def honScript : List (ℕ × SC26.Op) := [(2, .approve 2 0 tx1)]

/-- the adversary's script: request, execute, deliver, arrive, all issued by agent 1 -/
def advScript : List (ℕ × SC26.Op) := [(1, .request 1 tx1), (1, .execute 1 0), (1, .deliver 0), (1, .arrive 0)]

def honestTrace : List (ℕ × SC26.Op) :=
  [(1, .request 1 tx1), (2, .approve 2 0 tx1), (1, .execute 1 0), (1, .deliver 0), (1, .arrive 0)]

/-- **Non-vacuity**: the interleaving of the honest approval with the adversary's operations is admissible and pays. -/
theorem honest_payment_admissible :
    AdvTrace [1] honScript honestTrace ∧ ((authed (raw R0 20) claim).run init honestTrace).bank = [(0, tx1)] := by
  refine ⟨⟨advScript, by decide, ?_⟩, by decide⟩
  exact .right _ (.left _ (.right _ (.right _ (.right _ .nil))))

/-- **Forged claims are admissible but pay nothing**: with an empty honest script, the adversary's trace that claims
approver 2 (SC26Authenticated's `forged`) is admissible for `U = [1]`, and the authenticated run pays nothing. -/
theorem forged_claim_admissible_pays_nothing :
    AdvTrace [1] [] forged ∧ ((authed (raw R0 20) claim).run init forged).bank = [] := by
  refine ⟨⟨forged, by decide, ?_⟩, by decide⟩
  exact .right _ (.right _ (.right _ (.right _ (.right _ .nil))))

end ControlStack.AuthenticatedAdv

#print axioms ControlStack.AuthenticatedAdv.Shuffle.mem
#print axioms ControlStack.AuthenticatedAdv.applied_trusted_claim_from_honest
#print axioms ControlStack.AuthenticatedAdv.adversary_acts_only_as_U
#print axioms ControlStack.AuthenticatedAdv.sc26_consent_from_honest_script
#print axioms ControlStack.AuthenticatedAdv.honest_payment_admissible
#print axioms ControlStack.AuthenticatedAdv.forged_claim_admissible_pays_nothing
