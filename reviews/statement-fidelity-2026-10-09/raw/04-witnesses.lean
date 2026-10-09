/- Reviewer witnesses (statement-fidelity review 2026-10-09). Each is a concrete trace on which the headline
theorem's conclusion HOLDS, yet the scenario's prose would call the outcome a failure. They do not refute any theorem;
they show where the formal statement is weaker than the prose. Compile: `lake env lean <this file>` from the repo. -/
import ControlStack.Scenarios.SC23Injection
import ControlStack.Scenarios.SC17Infra
import ControlStack.Scenarios.SC25Audit
import ControlStack.Scenarios.SC16Deploy

namespace ReviewWitness

/-- W1 (SC-23): content equal to an injected tool result (66) is re-entered through `derive` with NO sources, so its
ghost provenance is "untrusted-free"; a sensitive tool (5) then runs on it without any confirmation, and `Good` holds
(`sc23_safe`). The adversary of `sc23_safe` controls `derive`/`userInput`, so `prov = false` means "derived from no
`toolResult`", not "not attacker-influenced". -/
example :
    (ControlStack.SC23.run ControlStack.SC23.P0 ControlStack.SC23.full ControlStack.SC23.init
      [.toolResult 0 66, .derive 1 [] 66, .act 5 [1] 0]).executed =
      [{ tool := 5, vals := [66], prov := false, conf := none }] := by decide

example : ControlStack.SC23.Good ControlStack.SC23.P0
    (ControlStack.SC23.run ControlStack.SC23.P0 ControlStack.SC23.full ControlStack.SC23.init
      [.toolResult 0 66, .derive 1 [] 66, .act 5 [1] 0]) :=
  ControlStack.SC23.sc23_safe _ _

/-- W2 (SC-17): two out-of-band grants put the LIVE state above the ceiling (`allowed` = false), and `Good` holds
(`sc17_safe`), because `Good` constrains only states recorded at applies. The SC-17 manifest bad_event begins "Live
permissions exceed the policy ceiling". -/
example :
    let s := ControlStack.SC17.run ControlStack.SC17.E0 ControlStack.SC17.full (ControlStack.SC17.init [])
      [.oob (1, 1, 1), .oob (1, 2, 1)]
    ControlStack.SC17.E0.allowed s.live = false := by decide

example : ControlStack.SC17.Good ControlStack.SC17.E0
    (ControlStack.SC17.run ControlStack.SC17.E0 ControlStack.SC17.full (ControlStack.SC17.init [])
      [.oob (1, 1, 1), .oob (1, 2, 1)]) :=
  ControlStack.SC17.sc17_safe _ _ _

/-- W3 (SC-25): with a non-injective digest (here constant), the auditor passes content 7, the agent amends it to
50, and 50 executes; `Good` holds (`sc25_safe` quantifies over every `h`). "Audit PASS for exactly its content" in
the manifest needs injectivity of `h` on the contents in play, which no SC-25 theorem states (contrast SC-16's
`sc16_reviewed_content`). -/
example :
    (ControlStack.SC25.run ControlStack.SC25.R0 (fun _ => 0) ControlStack.SC25.cls0 ControlStack.SC25.full
      ControlStack.SC25.init [.submit 1 0 7 false, .audit 2 0 true, .amend 1 0 50, .check 0, .fire 0]).executed.map
      ControlStack.SC25.Exec.content = [50] := by decide

example : ControlStack.SC25.Good ControlStack.SC25.R0 (fun _ => 0) ControlStack.SC25.cls0
    (ControlStack.SC25.run ControlStack.SC25.R0 (fun _ => 0) ControlStack.SC25.cls0 ControlStack.SC25.full
      ControlStack.SC25.init [.submit 1 0 7 false, .audit 2 0 true, .amend 1 0 50, .check 0, .fire 0]) :=
  ControlStack.SC25.sc25_safe _ _ _ _

/-- W4 (SC-16): with overlapping roles (agent 2 is also a reviewer), content staged by agent 1 and "reviewed" by
agent 2 deploys, and `Good` holds. `sc16_safe` has no role-disjointness hypothesis and no disjoint variant (contrast
SC-26's `sc26_safe_disjoint`). -/
def Rov : ControlStack.SC16.Roles := ⟨[1, 2], [2], [3], [4]⟩

example :
    (ControlStack.SC16.run Rov id ControlStack.SC16.full ControlStack.SC16.init
      [.stage 1 7, .review 2 7, .approve 3 0 7 5 0, .deploy 1 0 5 7]).deployed = [⟨0, 5, 7⟩] := by decide

example : ControlStack.SC16.Good Rov id
    (ControlStack.SC16.run Rov id ControlStack.SC16.full ControlStack.SC16.init
      [.stage 1 7, .review 2 7, .approve 3 0 7 5 0, .deploy 1 0 5 7]) :=
  ControlStack.SC16.sc16_safe _ _ _

end ReviewWitness
