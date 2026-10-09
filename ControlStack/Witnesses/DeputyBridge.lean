/-
The confused deputy across two real scenario gates (`Core/Compose.lean` bridge results, instantiated).

G₁ = the SC-26 payment gate, G₂ = the SC-16 deployment gate. Each is safe on its own (`SC26.sc26_safe`,
`SC16.sc16_safe`). A deputy that deploys whenever a PAYMENT approval exists (it treats G₁'s approval as authority for
G₂'s effect) breaks G₂'s spec in the joint system: `payment_deputy_breaks_deploy_gate`, and it is not admissible
(`payment_deputy_not_admissible`). A deputy that instead issues an SC-16 `deploy` operation, so that G₂'s own checks
run, is admissible (`gated_deputy_admissible`), and in the same trace deploys nothing (`gated_deputy_deploys_nothing`).

Adversary class: TRACE_ARBITRARY over the bridged product. Not claimed: that a real deputy is one of these two shapes.
No new mathematics.
-/
import ControlStack.Core.Compose
import ControlStack.Scenarios.SC26Transaction
import ControlStack.Scenarios.SC16Deploy

namespace ControlStack.DeputyBridge

open ControlStack.Gate ControlStack.Compose

/-- SC-16 roles: agent 1, reviewer 2, approver 3, admin 4 -/
def R16 : SC16.Roles := ⟨[1], [2], [3], [4]⟩

/-- the confused deputy: deploys content 7 to target 5 whenever any payment approval exists -/
def paymentDeputy (s₁ : SC26.St) (s₂ : SC16.St) : SC16.St :=
  if s₁.approvals ≠ [] then { s₂ with deployed := s₂.deployed ++ [⟨0, 5, 7⟩] } else s₂

/-- the gated deputy: asks the SC-16 gate to deploy (its checks run), whatever the payment state -/
def gatedDeputy (h : ℕ → ℕ) (_ : SC26.St) (s₂ : SC16.St) : SC16.St := SC16.step R16 h SC16.full s₂ (.deploy 0 0 5 7)

/-- the joint trace: a payment is requested and approved in G₁, then the deputy acts -/
def trace : List (BOp {o : SC26.Op // SC26.legal SC26.R0 o} SC16.Op) :=
  [.left ⟨.request 1 SC26.tx1, trivial⟩, .left ⟨.approve 2 0 SC26.tx1, trivial⟩, .bridge]

def start : PSt SC26.St SC16.St (ℕ × SC26.Tx) SC16.Dep :=
  prodInit (SC26.sys SC26.R0 20) (SC16.sys R16 id) SC26.init SC16.init

/-- **The confused deputy breaks the deployment gate**: after a payment approval, the deputy deploys content that has
no SC-16 approval or review, so SC-16's safety property fails in the joint state. -/
theorem payment_deputy_breaks_deploy_gate :
    let p := (withBridge (SC26.sys SC26.R0 20) (SC16.sys R16 id) paymentDeputy).run start trace
    p.s₂.deployed = [⟨0, 5, 7⟩] ∧ p.s₂.approvals = [] ∧ ¬ SC16.Good R16 id p.s₂ := by
  refine ⟨by decide, by decide, fun hg => ?_⟩
  have hd : ((withBridge (SC26.sys SC26.R0 20) (SC16.sys R16 id) paymentDeputy).run start trace).s₂.deployed =
      [⟨0, 5, 7⟩] := by decide
  have ha : ((withBridge (SC26.sys SC26.R0 20) (SC16.sys R16 id) paymentDeputy).run start trace).s₂.approvals =
      [] := by decide
  obtain ⟨ap, hap, _⟩ := hg.1 ⟨0, 5, 7⟩ (by rw [hd]; simp)
  rw [ha] at hap
  simp at hap

/-- the payment-approved state used below satisfies the SC-26 invariant -/
theorem approved_inv :
    SC26.Inv SC26.R0 20 (SC26.run SC26.R0 20 SC26.full SC26.init [.request 1 SC26.tx1, .approve 2 0 SC26.tx1]) :=
  SC26.run_inv _ _ SC26.sound_full _ _ (by simp [SC26.legal]) (SC26.inv_init _ _)

/-- **The confused deputy is not admissible** (`BridgeAdmissible` fails at a reachable pair of invariant states). -/
theorem payment_deputy_not_admissible :
    ¬ BridgeAdmissible (SC26.spec SC26.R0 20) (SC16.spec R16 id) paymentDeputy := by
  intro hb
  have h := (hb _ SC16.init approved_inv (SC16.inv_init R16 id)).1
  have hd : (paymentDeputy (SC26.run SC26.R0 20 SC26.full SC26.init [.request 1 SC26.tx1, .approve 2 0 SC26.tx1])
      SC16.init).deployed = [⟨0, 5, 7⟩] := by decide
  have ha : (paymentDeputy (SC26.run SC26.R0 20 SC26.full SC26.init [.request 1 SC26.tx1, .approve 2 0 SC26.tx1])
      SC16.init).approvals = [] := by decide
  obtain ⟨_, ap, hap, _⟩ := h.dep_ok ⟨0, 5, 7⟩ (by rw [hd]; simp)
  rw [ha] at hap
  simp at hap

/-- **A deputy that goes through the SC-16 gate is admissible**, so the joint SC-26 × SC-16 spec holds with it. -/
theorem gated_deputy_admissible (h : ℕ → ℕ) (cap : ℕ) (R : SC26.Roles) :
    BridgeAdmissible (SC26.spec R cap) (SC16.spec R16 h) (gatedDeputy h) :=
  admissible_of_step _ _ _ (fun _ _ => .deploy 0 0 5 7) (fun _ _ => rfl)

def gatedSpec (h : ℕ → ℕ) (cap : ℕ) (R : SC26.Roles) :=
  bridgeSpec (SC26.spec R cap) (SC16.spec R16 h) (gatedDeputy h) (gated_deputy_admissible h cap R)

/-- in the same trace, the gated deputy deploys nothing (no SC-16 review or approval exists) -/
theorem gated_deputy_deploys_nothing :
    ((withBridge (SC26.sys SC26.R0 20) (SC16.sys R16 id) (gatedDeputy id)).run start trace).s₂.deployed = [] := by
  decide

end ControlStack.DeputyBridge

#print axioms ControlStack.DeputyBridge.payment_deputy_breaks_deploy_gate
#print axioms ControlStack.DeputyBridge.payment_deputy_not_admissible
#print axioms ControlStack.DeputyBridge.gated_deputy_admissible
#print axioms ControlStack.DeputyBridge.gatedSpec
#print axioms ControlStack.DeputyBridge.gated_deputy_deploys_nothing
