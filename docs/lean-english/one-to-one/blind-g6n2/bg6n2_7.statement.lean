namespace PL_bg6n2_7
open ControlStack.SC26
open ControlStack.SC26Authenticated ControlStack.Authenticated ControlStack.Gate
open ControlStack.AuthenticatedAdv

open ControlStack.SC26 ControlStack.Authenticated ControlStack.Gate

def Back : Prop :=
  ∀ (R : Roles) (cap : ℕ) (U : List ℕ) (ops : List (ℕ × Op)),
    (∀ a ∈ R.approvers, a ∉ U) →
    (∀ io ∈ ops,
      match io.2 with
      | .bankCall _ _ _ => io.1 ≠ R.gate
      | _ => True) →
    let s := (authed (raw R cap) claim).run init ops
    Good R cap s ∧
    (∀ e ∈ s.bank,
      ∃ a : ℕ,
        a ∈ R.approvers ∧
        a ∉ U ∧
        (a, Op.approve a e.1 e.2) ∈ ops)


def BackAt (R : Roles) (cap : ℕ) (U : List ℕ) (ops : List (ℕ × Op)) (s : St) : Prop :=
  Good R cap s ∧ ∀ e ∈ s.bank, ∃ a : ℕ,
    a ∈ R.approvers ∧ a ∉ U ∧ (a, Op.approve a e.1 e.2) ∈ ops
def OrigAt (R : Roles) (cap : ℕ) (U : List ℕ) (ops : List (ℕ × Op)) (s : St) : Prop :=
  Good R cap s ∧ ∀ e ∈ s.bank, ∃ a : ℕ,
    a ∈ R.approvers ∧ a ∉ U ∧ (a, Op.approve a e.1 e.2) ∈ ops
def BankHyp (R : Roles) (ops : List (ℕ × Op)) : Prop :=
  ∀ io ∈ ops, match io.2 with
  | .bankCall _ _ _ => io.1 ≠ R.gate
  | _ => True
def OrigBankHyp (R : Roles) (ops : List (ℕ × Op)) : Prop :=
  ∀ io ∈ ops, ∀ c k tx, io.2 = .bankCall c k tx → io.1 ≠ R.gate
def HypAgreement : Prop := ∀ (R : Roles) (U : List ℕ) (ops : List (ℕ × Op)),
  ((∀ a ∈ R.approvers, a ∉ U) ↔ (∀ u ∈ U, u ∉ R.approvers)) ∧
  (BankHyp R ops ↔ OrigBankHyp R ops)
def BackEnvelope : Prop := ∀ (R : Roles) (cap : ℕ) (U : List ℕ) (ops : List (ℕ × Op)), (∀ a ∈ R.approvers, a ∉ U) → BankHyp R ops →
    BackAt R cap U ops ((authed (raw R cap) ControlStack.SC26Authenticated.claim).run init ops)
def OrigEnvelope : Prop := ∀ (R : Roles) (cap : ℕ) (U : List ℕ) (ops : List (ℕ × Op)), (∀ u ∈ U, u ∉ R.approvers) → OrigBankHyp R ops →
    OrigAt R cap U ops ((authed (raw R cap) ControlStack.SC26Authenticated.claim).run init ops)
def Claim : Prop := (Back ↔ BackEnvelope) ∧ (∀ (R : Roles) (cap : ℕ) (U : List ℕ) (ops : List (ℕ × Op)) (s : St), BackAt R cap U ops s ↔ OrigAt R cap U ops s) ∧ HypAgreement
def Witness : Prop := (∀ a ∈ R0.approvers, a ∉ ([1] : List ℕ)) ∧ BankHyp R0 honestTrace ∧
  ((authed (raw R0 20) ControlStack.SC26Authenticated.claim).run init honestTrace).bank = [(0, tx1)]
end PL_bg6n2_7
