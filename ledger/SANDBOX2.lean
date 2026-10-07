namespace PL_SANDBOX2F1
open PL_SANDBOXF1

/-! Control stack, ACTION layer step 1b (campaign SANDBOX2): the corrected sandbox fix.
Depends on PL_SANDBOXF1 (mount-table model, `effective`, `WritesHost`, `ReadsHost`, `currentPolicy`,
`fixedPolicy`, `hiddenDirs`, `mathlibProj`).

Reviewer B's final review found that SANDBOXF1's proposed `fixedPolicy` places the writable state-directory
binds AFTER the hiding tmpfs mounts. A declared state directory that is an ancestor of a hidden directory
(e.g. a CLI state directory over its hidden session-log subdirectory) therefore re-exposes it.
(a) That regression, as a counterexample.
(b), (c) A corrected policy: state binds BEFORE the hiding tmpfs mounts.
  (b) Host writes stay inside scratch or a declared state directory.
  (c) Hiding holds for EVERY choice of state directories: any host path inside a hidden directory that a
      sandbox read reveals lies inside the read-only Mathlib re-bind.
Same model and boundary assumptions as PL_SANDBOXF1: these are statements about modelled pathname
resolution. Hard links, symlinks, other aliases, `/proc/<pid>/root`, and network side channels are outside
the model. -/

/-- corrected fixed policy: read-only host root; scratch; declared state directories; THEN the hiding
tmpfs mounts; then the read-only Mathlib re-bind -/
def fixedPolicy2 (W : Path) (stateDirs : List Path) : Policy :=
  [.bind [] [] .ro, .tmpfs ["var", "tmp"], .bind W ["var", "tmp", "work"] .rw] ++
  stateDirs.map (fun d => .bind d d .rw) ++ hiddenDirs.map .tmpfs ++
  [.bind mathlibProj mathlibProj .ro]

def Claim : Prop :=
  -- (a) the SANDBOXF1 fix re-exposes a hidden directory when a CLI state directory that is an ancestor of
  --     a hidden session-log directory is declared
  (∀ W : Path, ["var", "tmp"] <+: W →
    ReadsHost (fixedPolicy W [home ++ [".agent-b"]]) (home ++ [".agent-b", "sessions", "s.jsonl"])
      (home ++ [".agent-b", "sessions", "s.jsonl"])) ∧
  -- (b) corrected policy: host writes are confined to scratch and the declared state directories
  (∀ (W : Path) (stateDirs : List Path) (canWrite : Path → Prop) (p hp : Path),
    WritesHost (fixedPolicy2 W stateDirs) canWrite p hp →
      W <+: hp ∨ ∃ d ∈ stateDirs, d <+: hp) ∧
  -- (c) corrected policy: hiding holds for every choice of state directories
  (∀ (W : Path) (stateDirs : List Path) (p hp H : Path), ["var", "tmp"] <+: W → H ∈ hiddenDirs →
    H <+: hp → ReadsHost (fixedPolicy2 W stateDirs) p hp → mathlibProj <+: hp)

/-- Non-vacuity: with one CLI state directory declared, the corrected policy still lets the CLI write a
credential file inside it, still lets scratch be written, and still lets Mathlib be read. -/
def Witness : Prop :=
  WritesHost (fixedPolicy2 ["var", "tmp", "job-x"] [home ++ [".agent-b"]]) (fun _ => True)
    (home ++ [".agent-b", "auth.json"]) (home ++ [".agent-b", "auth.json"]) ∧
  WritesHost (fixedPolicy2 ["var", "tmp", "job-x"] [home ++ [".agent-b"]]) (fun _ => True)
    ["var", "tmp", "work", "out.md"] ["var", "tmp", "job-x", "out.md"] ∧
  ReadsHost (fixedPolicy2 ["var", "tmp", "job-x"] [home ++ [".agent-b"]]) (mathlibProj ++ ["x.lean"])
    (mathlibProj ++ ["x.lean"])

end PL_SANDBOX2F1
