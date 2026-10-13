namespace ControlStack.SC27ExtensionOnly

def Back_alarm_iff : Prop :=
  ∀ (E : Env) (s : St),
    let next := step E true s .anchor
    (next.alarms = s.alarms ++ [s.log] ↔ extendsLast s = false) ∧
    (extendsLast s = false → next.anchors = s.anchors)

end ControlStack.SC27ExtensionOnly
