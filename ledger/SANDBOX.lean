namespace PL_SANDBOXF1

/-! Control stack, ACTION layer (first step): a reference-monitor model of a research harness's bubblewrap
sandbox for untrusted provers (a mount table) and its intended properties.

Model.
- Paths are lists of components.
- A policy is a list of mount operations applied in order.
- The effective mount of a path is the LAST operation whose target is an initial segment of it (a later mount on an
  initial segment covers earlier deeper mounts; a later deeper mount shows through an earlier shallower one).
- A host-backed mount maps sandbox path `t ++ rest` to host path `src ++ rest`; a tmpfs is private,
  empty and ephemeral, so writes to it never reach the host.
- An action WRITE p reaches the host iff the effective mount is host-backed and read-write, and the host
  permission predicate allows the write.

Boundary assumption (named, not modelled): every file access goes through the mount table. In
particular there is no `/proc/<pid>/root` alias into another mount namespace (requires
`--unshare-pid --proc /proc`), and no network or other side channel is considered here. -/

abbrev Path := List String

inductive Mode | ro | rw
  deriving DecidableEq

inductive Mount where
  /-- `--bind src tgt` / `--dev-bind src tgt` (rw) or `--ro-bind src tgt` (ro) -/
  | bind (src tgt : Path) (mode : Mode)
  /-- `--tmpfs tgt` -/
  | tmpfs (tgt : Path)
  deriving DecidableEq

def Mount.tgt : Mount → Path
  | .bind _ t _ => t
  | .tmpfs t => t

abbrev Policy := List Mount

/-- the effective mount of `p`: the last operation whose target is an initial segment of `p` -/
def effective (pol : Policy) (p : Path) : Option Mount :=
  (pol.filter (fun m => m.tgt <+: p)).getLast?

/-- the host path that sandbox path `p` resolves to, if host-backed -/
def hostOf (pol : Policy) (p : Path) : Option Path :=
  match effective pol p with
  | some (.bind src t _) => some (src ++ p.drop t.length)
  | _ => none

/-- a write to sandbox path `p` modifies host path `hp` -/
def WritesHost (pol : Policy) (canWrite : Path → Prop) (p hp : Path) : Prop :=
  ∃ src t, effective pol p = some (.bind src t .rw) ∧ hp = src ++ p.drop t.length ∧ canWrite hp

/-- a read of sandbox path `p` reveals host path `hp` -/
def ReadsHost (pol : Policy) (p hp : Path) : Prop :=
  ∃ src t m, effective pol p = some (.bind src t m) ∧ hp = src ++ p.drop t.length

-- The concrete paths below are instances (a home directory, CLI state directories, the Mathlib project);
-- the theorems do not depend on their particular names.
def home : Path := ["home", "user"]
def research : Path := home ++ ["research"]
def mathlibProj : Path := research ++ ["proj", "lean", "lean-proj"]
def hiddenDirs : List Path :=
  [research, home ++ [".agent-a"], ["tmp"], home ++ [".agent-b", "sessions"], home ++ [".agent-b", "log"],
   home ++ [".agent-b", "shell_snapshots"], home ++ [".agent-c", "tmp"],
   home ++ [".agent-c", "agent-cli", "memory"], home ++ [".agent-c", "agent-cli", "conversations"],
   home ++ [".agent-c", "agent-cli", "scratch"], home ++ [".agent-c", "agent-cli", "log"]]

/-- the policy as found when modelled: a WRITABLE host root (hidden files omitted; all hidden dirs assumed to
exist): `--dev-bind / /`, `--tmpfs /var/tmp`, `--bind W /var/tmp/work`, a tmpfs over each hidden
directory, `--ro-bind MATHLIB MATHLIB`. -/
def currentPolicy (W : Path) : Policy :=
  [.bind [] [] .rw, .tmpfs ["var", "tmp"], .bind W ["var", "tmp", "work"] .rw] ++
  hiddenDirs.map .tmpfs ++ [.bind mathlibProj mathlibProj .ro]

/-- a FIXED policy: read-only host root; writable scratch and declared CLI state directories only. -/
def fixedPolicy (W : Path) (stateDirs : List Path) : Policy :=
  [.bind [] [] .ro, .tmpfs ["var", "tmp"], .bind W ["var", "tmp", "work"] .rw] ++
  hiddenDirs.map .tmpfs ++ stateDirs.map (fun d => .bind d d .rw) ++
  [.bind mathlibProj mathlibProj .ro]

def Claim : Prop :=
  -- (a) the current policy does NOT confine host writes to the scratch directory: with the user's own
  --     write permission on its home, a toolchain directory that a later, unsandboxed checker executes is
  --     writable from inside the sandbox.
  (∀ W : Path, ["var", "tmp"] <+: W →
    WritesHost (currentPolicy W) (fun hp => home <+: hp ∨ ["var", "tmp"] <+: hp)
      (home ++ [".toolchain", "bin", "lake"]) (home ++ [".toolchain", "bin", "lake"])) ∧
  -- (b) the fixed policy confines host writes to the scratch directory and the declared state
  --     directories, for EVERY sandbox path and every host permission predicate.
  (∀ (W : Path) (stateDirs : List Path) (canWrite : Path → Prop) (p hp : Path),
    WritesHost (fixedPolicy W stateDirs) canWrite p hp →
      W <+: hp ∨ ∃ d ∈ stateDirs, d <+: hp) ∧
  -- (c) the current policy does hide the hidden directories: when the scratch directory lies under
  --     the scratch tmpfs root (where the harness creates it), any host path inside a hidden directory that a sandbox read
  --     reveals lies inside the read-only Mathlib re-bind
  (∀ (W p hp H : Path), ["var", "tmp"] <+: W → H ∈ hiddenDirs → H <+: hp →
    ReadsHost (currentPolicy W) p hp → mathlibProj <+: hp)

/-- Non-vacuity: the fixed policy still lets the scratch directory be written, and still lets the
Mathlib project be read (read-only). -/
def Witness : Prop :=
  WritesHost (fixedPolicy ["var", "tmp", "job-x"] []) (fun _ => True)
    ["var", "tmp", "work", "out.md"] ["var", "tmp", "job-x", "out.md"] ∧
  ReadsHost (fixedPolicy ["var", "tmp", "job-x"] []) (mathlibProj ++ ["lakefile.toml"])
    (mathlibProj ++ ["lakefile.toml"])

end PL_SANDBOXF1
