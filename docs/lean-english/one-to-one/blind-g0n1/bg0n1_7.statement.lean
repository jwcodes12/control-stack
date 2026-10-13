namespace PL_bg0n1_7
open ControlStack ControlStack.Deployment

def Back : Prop :=
  ∀ (d : IR) (r : Node) (actualEdges : List Edge)
      (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op)
      (sinkEffects : List (Nat × SC26.Tx)),
    Accepted d → ExtractionFaithful d r actualEdges →
    ProtocolRefinement d r R cap ops sinkEffects →
    let s := SC26.run R cap SC26.full SC26.init ops
    (∀ e ∈ actualEdges, e.authority = true → e.target = d.sink →
      e.source = d.receiver) ∧
    (∀ e ∈ sinkEffects, ∃ req,
      SC26.reqOf s e.1 = some req ∧ req.tx = e.2 ∧
        e.1 ∈ s.reserved ∧ SC26.Approved R s e.1 req) ∧
    (sinkEffects.map Prod.fst).Nodup ∧
    (sinkEffects.map (fun e => e.2.amount)).sum ≤ cap ∧
    sinkEffects.length ≤ cap

def Orig : Prop :=
  ∀ (d : IR) (r : Node) (R : SC26.Roles) (cap : Nat)
    (ops : List SC26.Op) (actualEdges : List Edge) (sinkEffects : List (Nat × SC26.Tx))
    (h : Accepted d) (extraction : ExtractionFaithful d r actualEdges)
    (refinement : ProtocolRefinement d r R cap ops sinkEffects),
    (∀ e ∈ actualEdges, e.authority = true → e.target = d.sink → e.source = d.receiver) ∧
    (∀ e ∈ sinkEffects, ∃ req, SC26.reqOf (SC26.run R cap SC26.full SC26.init ops) e.1 = some req ∧
      req.tx = e.2 ∧ e.1 ∈ (SC26.run R cap SC26.full SC26.init ops).reserved ∧
      SC26.Approved R (SC26.run R cap SC26.full SC26.init ops) e.1 req) ∧
    (sinkEffects.map Prod.fst).Nodup ∧ (sinkEffects.map (fun e => e.2.amount)).sum ≤ cap ∧
    sinkEffects.length ≤ cap

def BackConclusion (d : IR) (r : Node) (actualEdges : List Edge) (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op) (sinkEffects : List (Nat × SC26.Tx)) : Prop :=
  let s := SC26.run R cap SC26.full SC26.init ops
  (∀ e ∈ actualEdges, e.authority = true → e.target = d.sink →
    e.source = d.receiver) ∧
  (∀ e ∈ sinkEffects, ∃ req,
    SC26.reqOf s e.1 = some req ∧ req.tx = e.2 ∧
      e.1 ∈ s.reserved ∧ SC26.Approved R s e.1 req) ∧
  (sinkEffects.map Prod.fst).Nodup ∧
  (sinkEffects.map (fun e => e.2.amount)).sum ≤ cap ∧
  sinkEffects.length ≤ cap

def OrigConclusion (d : IR) (r : Node) (actualEdges : List Edge) (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op) (sinkEffects : List (Nat × SC26.Tx)) : Prop :=
  (∀ e ∈ actualEdges, e.authority = true → e.target = d.sink → e.source = d.receiver) ∧
    (∀ e ∈ sinkEffects, ∃ req, SC26.reqOf (SC26.run R cap SC26.full SC26.init ops) e.1 = some req ∧
      req.tx = e.2 ∧ e.1 ∈ (SC26.run R cap SC26.full SC26.init ops).reserved ∧
      SC26.Approved R (SC26.run R cap SC26.full SC26.init ops) e.1 req) ∧
    (sinkEffects.map Prod.fst).Nodup ∧ (sinkEffects.map (fun e => e.2.amount)).sum ≤ cap ∧
    sinkEffects.length ≤ cap

def Claim : Prop :=
  (Back ↔ (∀ (d : IR) (r : Node) (actualEdges : List Edge)
      (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op)
      (sinkEffects : List (Nat × SC26.Tx)),
    Accepted d → ExtractionFaithful d r actualEdges →
    ProtocolRefinement d r R cap ops sinkEffects →
    BackConclusion d r actualEdges R cap ops sinkEffects)) ∧
  (Orig ↔ (∀ (d : IR) (r : Node) (R : SC26.Roles) (cap : Nat)
    (ops : List SC26.Op) (actualEdges : List Edge) (sinkEffects : List (Nat × SC26.Tx))
    (h : Accepted d) (extraction : ExtractionFaithful d r actualEdges)
    (refinement : ProtocolRefinement d r R cap ops sinkEffects),
    OrigConclusion d r actualEdges R cap ops sinkEffects)) ∧
  (∀ (d : IR) (r : Node) (actualEdges : List Edge) (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op) (sinkEffects : List (Nat × SC26.Tx)), Accepted d → ExtractionFaithful d r actualEdges → ProtocolRefinement d r R cap ops sinkEffects →
    (BackConclusion d r actualEdges R cap ops sinkEffects ↔ OrigConclusion d r actualEdges R cap ops sinkEffects))

def Witness : Prop :=
  Accepted clean ∧ ExtractionFaithful clean ControlStack.Deployment.Witnesses.receiverNode clean.edges ∧ ProtocolRefinement clean ControlStack.Deployment.Witnesses.receiverNode twoRoles 1 ControlStack.Deployment.Witnesses.modelOps [(0,payload)] ∧ ([(0,payload)] : List (Nat × SC26.Tx)).length = 1

end PL_bg0n1_7
