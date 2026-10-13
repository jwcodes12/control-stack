namespace PL_bg7n1_8
open ControlStack.SC27ExtensionOnly


def FrozenBack : Prop :=
  ∀ (E : Env) (s : St),
    let next := step E true s .anchor
    (next.alarms = s.alarms ++ [s.log] ↔ extendsLast s = false) ∧
    (extendsLast s = false → next.anchors = s.anchors)

def BackAt (E : Env) (s : St) : Prop :=
  let next := step E true s .anchor
  (next.alarms = s.alarms ++ [s.log] ↔ extendsLast s = false) ∧
  (extendsLast s = false → next.anchors = s.anchors)

def OrigAt (E : Env) (s : St) : Prop :=
  ((step E true s .anchor).alarms = s.alarms ++ [s.log] ↔ extendsLast s = false) ∧
  (extendsLast s = false → (step E true s .anchor).anchors = s.anchors)

def Claim : Prop :=
  (FrozenBack ↔ (∀ (E : Env) (s : St), BackAt E s)) ∧
  (∀ (E : Env) (s : St), (BackAt E s ↔ OrigAt E s))

def Witness : Prop :=
  let s := run E0 true init [.append 5, .anchor, .rewrite [7]]
  extendsLast s = false ∧ (step E0 true s .anchor).alarms = [[7]] ∧
  (step E0 true s .anchor).anchors = s.anchors ∧
  (step E0 true init .anchor).alarms = []

end PL_bg7n1_8
