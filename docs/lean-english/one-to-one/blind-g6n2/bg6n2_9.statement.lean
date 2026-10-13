namespace PL_bg6n2_9
open ControlStack.SC26
open ControlStack.SC26Authenticated ControlStack.Authenticated ControlStack.Gate
open ControlStack.AuthenticatedAdv

open ControlStack.SC26 ControlStack.SC26Authenticated
open ControlStack.Authenticated ControlStack.Gate

def Back : Prop :=
  ∀ (R : Roles) (cap : ℕ) (U : List ℕ)
    (hon ops : List (ℕ × Op)),
    AdvTrace U hon ops →
    (∀ a ∈ R.approvers, a ∉ U) →
    R.gate ∉ U →
    (∀ io ∈ hon,
      match io.2 with
      | .bankCall _ _ _ => io.1 ≠ R.gate
      | _ => True) →
    let s := (authed (raw R cap) claim).run init ops
    Good R cap s ∧
    (∀ e ∈ s.bank,
      ∃ a : ℕ,
        a ∈ R.approvers ∧
        (a, Op.approve a e.1 e.2) ∈ hon)


def BackAt (R : Roles) (cap : ℕ) (hon : List (ℕ × Op)) (s : St) : Prop :=
  Good R cap s ∧ ∀ e ∈ s.bank, ∃ a : ℕ,
    a ∈ R.approvers ∧ (a, Op.approve a e.1 e.2) ∈ hon
def OrigAt (R : Roles) (cap : ℕ) (hon : List (ℕ × Op)) (s : St) : Prop :=
  Good R cap s ∧ ∀ e ∈ s.bank, ∃ a : ℕ,
    a ∈ R.approvers ∧ (a, Op.approve a e.1 e.2) ∈ hon
def BankHyp (R : Roles) (ops : List (ℕ × Op)) : Prop :=
  ∀ io ∈ ops, match io.2 with
  | .bankCall _ _ _ => io.1 ≠ R.gate
  | _ => True
def OrigBankHyp (R : Roles) (ops : List (ℕ × Op)) : Prop :=
  ∀ io ∈ ops, ∀ c k tx, io.2 = .bankCall c k tx → io.1 ≠ R.gate
def HypAgreement : Prop := ∀ (R : Roles) (U : List ℕ) (ops : List (ℕ × Op)),
  ((∀ a ∈ R.approvers, a ∉ U) ↔ (∀ u ∈ U, u ∉ R.approvers)) ∧
  (BankHyp R ops ↔ OrigBankHyp R ops)
def BackEnvelope : Prop := ∀ (R : Roles) (cap : ℕ) (U : List ℕ) (hon ops : List (ℕ × Op)), AdvTrace U hon ops → (∀ a ∈ R.approvers, a ∉ U) → R.gate ∉ U → BankHyp R hon →
    BackAt R cap hon ((authed (raw R cap) ControlStack.SC26Authenticated.claim).run init ops)
def OrigEnvelope : Prop := ∀ (R : Roles) (cap : ℕ) (U : List ℕ) (hon ops : List (ℕ × Op)), AdvTrace U hon ops → (∀ u ∈ U, u ∉ R.approvers) → R.gate ∉ U → OrigBankHyp R hon →
    OrigAt R cap hon ((authed (raw R cap) ControlStack.SC26Authenticated.claim).run init ops)
def Claim : Prop := (Back ↔ BackEnvelope) ∧ (∀ (R : Roles) (cap : ℕ) (hon : List (ℕ × Op)) (s : St), BackAt R cap hon s ↔ OrigAt R cap hon s) ∧ HypAgreement
def Witness : Prop := AdvTrace [1] honScript honestTrace ∧ (∀ a ∈ R0.approvers, a ∉ ([1] : List ℕ)) ∧
  R0.gate ∉ ([1] : List ℕ) ∧ BankHyp R0 honScript ∧
  ((authed (raw R0 20) ControlStack.SC26Authenticated.claim).run init honestTrace).bank = [(0, tx1)]
end PL_bg6n2_9
