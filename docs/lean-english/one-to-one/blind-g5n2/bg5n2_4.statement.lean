namespace PL_bg5n2_4
open ControlStack.SC23IsolationV2 ControlStack.Authenticated ControlStack.Gate
def Back_noninterference_authed : Prop :=
  ∀ (E : Env) (ops ops' : List (ℕ × Op)),
    List.Forall₂
      (fun io io' => io.1 = io'.1 ∧ SameExceptContent io.2 io'.2)
      ops ops' →
      Rel ((authed (raw E) claim).run init ops)
        ((authed (raw E) claim).run init ops')

def Claim : Prop :=
  (Back_noninterference_authed = (∀ (E : Env) (ops ops' : List (ℕ × Op)),
    List.Forall₂ (fun io io' => io.1 = io'.1 ∧ SameExceptContent io.2 io'.2) ops ops' →
      Rel ((authed (raw E) ControlStack.SC23IsolationV2.claim).run init ops)
        ((authed (raw E) ControlStack.SC23IsolationV2.claim).run init ops'))) ∧
  (∀ (E : Env) (ops ops' : List (ℕ × Op)),
    List.Forall₂ (fun io io' => io.1 = io'.1 ∧ SameExceptContent io.2 io'.2) ops ops' →
    (Rel ((authed (raw E) ControlStack.SC23IsolationV2.claim).run init ops)
       ((authed (raw E) ControlStack.SC23IsolationV2.claim).run init ops') ↔
     Rel ((authed (raw E) ControlStack.SC23IsolationV2.claim).run init ops)
       ((authed (raw E) ControlStack.SC23IsolationV2.claim).run init ops')))
def Witness : Prop :=
  List.Forall₂ (fun io io' : ℕ × Op => io.1 = io'.1 ∧ SameExceptContent io.2 io'.2)
    [(7,.toolResult 66), (1,.derive), (1,.act 5 [1] 0)]
    [(7,.toolResult 0), (1,.derive), (1,.act 5 [1] 0)] ∧
  ((authed (raw E0) ControlStack.SC23IsolationV2.claim).run init
    [(7,.toolResult 66), (1,.derive), (1,.act 5 [1] 0)]).executed = [⟨5,[0],false,none⟩]
end PL_bg5n2_4
