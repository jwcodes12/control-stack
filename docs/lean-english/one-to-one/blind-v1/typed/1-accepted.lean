import ControlStack.Deployment.Witnesses
import ControlStack.Deployment.TranscriptReplay

namespace ControlStack.Deployment

-- NOTE
-- AMBIGUOUS: The writers prose calls the sink sources both a "set" and a
-- "source list": duplicates could be ignored or counted. Here the filtered
-- source list is exactly [d.receiver], so duplicate write edges count.
-- "Distinct nodes" could mean unequal Node records or different node IDs;
-- here it means unequal Node records. The roles prose has no separate
-- isBroker/isReceiver field; here role 1 iff broker ID, and role 2 iff receiver
-- ID, encode those identities. Reviewer and approver mean roles 3 and 4.
-- The six groups below use only the supplied fields and reachable function.
def BackAccepted (d : IR) : Prop :=
  -- Basic.
  ((∀ e ∈ d.edges, e.unknown = false) ∧
   (∀ e ∈ d.edges, e.authority = true → e.target = d.sink →
     e.source = d.receiver) ∧
   (∀ e ∈ d.edges, e.authority = true → e.target = d.database →
     e.source = d.receiver ∨ e.source = d.broker) ∧
   (∀ n ∈ d.nodes, n.privileged = false ∧ n.hostNetwork = false) ∧
   (∀ r ∈ d.nodes, r.id = d.receiver →
     ∀ a ∈ d.nodes, a.agent = true → a.uid ≠ r.uid) ∧
   (∃ e ∈ d.edges, e.source = d.receiver ∧ e.target = d.sink ∧
     e.authority = true) ∧
   (∀ n ∈ d.nodes, 0 < n.uid)) ∧
  -- Roles.
  (d.nodes.length = 6 ∧
   (d.nodes.filter (fun n => n.agent)).length = 2 ∧
   (d.nodes.filter (fun n => n.role == 1)).length = 1 ∧
   (d.nodes.filter (fun n => n.role == 2)).length = 1 ∧
   (d.nodes.filter (fun n => n.role == 3)).length = 1 ∧
   (d.nodes.filter (fun n => n.role == 4)).length = 1 ∧
   (∀ n ∈ d.nodes,
     (n.agent = true ↔ n.role = 0) ∧
     (n.id = d.broker ↔ n.role = 1) ∧
     (n.id = d.receiver ↔ n.role = 2))) ∧
  -- Identities.
  (∀ n ∈ d.nodes, ∀ m ∈ d.nodes, n ≠ m →
    (n.uid = m.uid ↔
      (n.id = d.broker ∧ m.id = d.receiver) ∨
      (n.id = d.receiver ∧ m.id = d.broker))) ∧
  -- Runtime.
  (∀ n ∈ d.nodes, n.runtimeMatch = true) ∧
  -- Writers.
  ((∀ e ∈ d.edges, e.target = d.sink →
     e.source = d.receiver ∧ e.write = true) ∧
   ((d.edges.filter (fun e => e.write && (e.target == d.sink))).map
     Edge.source = [d.receiver]) ∧
   (∀ e ∈ d.edges, e.target = d.database →
     e.source = d.broker ∨ e.source = d.receiver) ∧
   (let sources :=
      (d.edges.filter (fun e => e.write && (e.target == d.database))).map
        Edge.source
    sources = [d.broker, d.receiver] ∨
      sources = [d.receiver, d.broker])) ∧
  -- No-bypass.
  (∀ a ∈ d.nodes, a.agent = true →
    d.sink ∉ reachable d a.id ∧
    d.database ∉ reachable d a.id ∧
    (∀ e ∈ d.edges, e.source ∈ reachable d a.id →
      e.target ≠ d.broker → e.target ≠ d.receiver →
      e.target ∈ reachable d a.id))

end ControlStack.Deployment
