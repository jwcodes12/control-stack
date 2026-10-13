namespace PL_bg0n1_8
open ControlStack ControlStack.Deployment

def Back : Prop :=
  ∀ (d larger : IR),
    (∀ e ∈ d.edges, e ∈ larger.edges) →
    d.nodes = larger.nodes → d.broker = larger.broker →
    d.receiver = larger.receiver → d.sink = larger.sink →
    d.database = larger.database → Accepted larger →
    ∀ a ∈ d.nodes, a.agent = true →
      ¬ AvoidedPath d a.id d.sink ∧ ¬ AvoidedPath d a.id d.database

def Orig : Prop :=
  ∀ (d larger : IR)
    (subset : ∀ e ∈ d.edges, e ∈ larger.edges)
    (nodes : d.nodes = larger.nodes)
    (broker : d.broker = larger.broker) (receiver : d.receiver = larger.receiver)
    (sink : d.sink = larger.sink) (database : d.database = larger.database)
    (accepted : Accepted larger) (a : Node) (member : a ∈ d.nodes)
    (agent : a.agent = true),
    ¬ AvoidedPath d a.id d.sink ∧ ¬ AvoidedPath d a.id d.database

def BackConclusion (d : IR) (a : Node) : Prop :=
  ¬ AvoidedPath d a.id d.sink ∧ ¬ AvoidedPath d a.id d.database

def OrigConclusion (d : IR) (a : Node) : Prop :=
  ¬ AvoidedPath d a.id d.sink ∧ ¬ AvoidedPath d a.id d.database

def Claim : Prop :=
  (Back ↔ (∀ (d larger : IR),
    (∀ e ∈ d.edges, e ∈ larger.edges) →
    d.nodes = larger.nodes → d.broker = larger.broker →
    d.receiver = larger.receiver → d.sink = larger.sink →
    d.database = larger.database → Accepted larger →
    ∀ a ∈ d.nodes, a.agent = true →
      BackConclusion d a)) ∧
  (Orig ↔ (∀ (d larger : IR)
    (subset : ∀ e ∈ d.edges, e ∈ larger.edges)
    (nodes : d.nodes = larger.nodes)
    (broker : d.broker = larger.broker) (receiver : d.receiver = larger.receiver)
    (sink : d.sink = larger.sink) (database : d.database = larger.database)
    (accepted : Accepted larger) (a : Node) (member : a ∈ d.nodes)
    (agent : a.agent = true),
    OrigConclusion d a)) ∧
  (∀ (d larger : IR) (a : Node), (∀ e ∈ d.edges, e ∈ larger.edges) → d.nodes = larger.nodes → d.broker = larger.broker → d.receiver = larger.receiver → d.sink = larger.sink → d.database = larger.database → Accepted larger → a ∈ d.nodes → a.agent = true →
    (BackConclusion d a ↔ OrigConclusion d a))

def Witness : Prop :=
  (∀ e ∈ sinkOnly.edges, e ∈ clean.edges) ∧ sinkOnly.nodes = clean.nodes ∧ sinkOnly.broker = clean.broker ∧ sinkOnly.receiver = clean.receiver ∧ sinkOnly.sink = clean.sink ∧ sinkOnly.database = clean.database ∧ Accepted clean ∧ ControlStack.Deployment.Witnesses.agentA ∈ sinkOnly.nodes ∧ ControlStack.Deployment.Witnesses.agentA.agent = true ∧ ¬ Accepted sinkOnly ∧ sinkOnly.edges ≠ clean.edges

end PL_bg0n1_8
