namespace PL_bg0n1_2
open ControlStack ControlStack.Deployment

def Back : Prop :=
  ∀ (d : IR) (r a : Node) (approvers admins : List Nat)
      (key : Nat) (tx : SC26.Tx),
    Accepted d → r ∈ d.nodes → r.id = d.receiver →
    a ∈ d.nodes → a.agent = true →
    SC26.legal (roles d r.uid approvers admins)
      (SC26.Op.bankCall a.uid key tx)

def Orig : Prop :=
  ∀ (d : IR) (h : Accepted d) (r a : Node)
    (hr : r ∈ d.nodes) (rid : r.id = d.receiver) (ha : a ∈ d.nodes)
    (agent : a.agent = true) (approvers admins : List Nat) (k : Nat) (tx : SC26.Tx),
    SC26.legal (roles d r.uid approvers admins) (.bankCall a.uid k tx)

def BackConclusion (d : IR) (r a : Node) (approvers admins : List Nat) (key : Nat) (tx : SC26.Tx) : Prop :=
  SC26.legal (roles d r.uid approvers admins)
      (SC26.Op.bankCall a.uid key tx)

def OrigConclusion (d : IR) (r a : Node) (approvers admins : List Nat) (key : Nat) (tx : SC26.Tx) : Prop :=
  SC26.legal (roles d r.uid approvers admins) (.bankCall a.uid key tx)

def Claim : Prop :=
  (Back ↔ (∀ (d : IR) (r a : Node) (approvers admins : List Nat)
      (key : Nat) (tx : SC26.Tx),
    Accepted d → r ∈ d.nodes → r.id = d.receiver →
    a ∈ d.nodes → a.agent = true →
    BackConclusion d r a approvers admins key tx)) ∧
  (Orig ↔ (∀ (d : IR) (h : Accepted d) (r a : Node)
    (hr : r ∈ d.nodes) (rid : r.id = d.receiver) (ha : a ∈ d.nodes)
    (agent : a.agent = true) (approvers admins : List Nat) (k : Nat) (tx : SC26.Tx),
    OrigConclusion d r a approvers admins k tx)) ∧
  (∀ (d : IR) (r a : Node) (approvers admins : List Nat) (key : Nat) (tx : SC26.Tx), Accepted d → r ∈ d.nodes → r.id = d.receiver → a ∈ d.nodes → a.agent = true →
    (BackConclusion d r a approvers admins key tx ↔ OrigConclusion d r a approvers admins key tx))

def Witness : Prop :=
  Accepted clean ∧ ControlStack.Deployment.Witnesses.receiverNode ∈ clean.nodes ∧ ControlStack.Deployment.Witnesses.receiverNode.id = clean.receiver ∧ ControlStack.Deployment.Witnesses.agentA ∈ clean.nodes ∧ ControlStack.Deployment.Witnesses.agentA.agent = true ∧ SC26.legal (roles clean ControlStack.Deployment.Witnesses.receiverNode.uid [23703] [23704]) (.bankCall ControlStack.Deployment.Witnesses.agentA.uid 0 payload)

end PL_bg0n1_2
