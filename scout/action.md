# ACTION-layer source scout (Cedar, Veil, dispatch.py sandbox)

Date 2026-10-06. Read-only scout: all facts below come from raw GitHub source and local files; nothing was built, cloned or run.
Items marked UNVERIFIED are inferences that need a build or an experiment.

## 0. Verdict (read this first)

1. Cedar is usable as a dependency. At cedar-spec commit `3f51c8f7b301681da9e6a8f968c1c8070093884a` (the last commit on Lean `v4.34.0`) it matches our toolchain exactly.
   - Its Batteries rev `f2effa3d803fda822b1f97b806c47cf2adfbcbc2` is the SAME rev ControlStack already locks (see /home/opc/research/control-stack/lake-manifest.json).
   - It needs only Batteries, not Mathlib.
2. Veil is NOT usable as a dependency. It pins Lean `v4.32.0` with its own pinned Batteries, aesop, proofwidgets, Loom, lean-smt and lean-cvc5, and it needs npm and clang at build time.
   - Its default SMT mode closes goals with `sorry`.
   - Only the ~60 lines in `Veil/Core/Tools/ModelChecker/TransitionSystem.lean` (`RelationalTransitionSystem` plus `reachable`) are worth borrowing, as a design reference to re-derive.
3. The sandbox in `dispatch.py` `sandbox()` is a CONFIDENTIALITY mask over a fully writable, fully networked host.
   - It is not an integrity sandbox: only `MATHLIB_PROJ` is read-only, there is no network, PID, env or resource isolation, and the only hard limit is a 300 MB scratch watchdog.
   - The Lean model must say that, or the reachability theorem will be vacuous against the real code.
4. Recommendation: hybrid of (a) and (c). Depend on Cedar for decision semantics, and write the stateful transition-system / reachability layer as plain Lean. See §4.

---

## 1. Cedar (cedar-policy/cedar-spec, directory `cedar-lean/`)

### 1.1 Metadata
- Licence: Apache-2.0 (repo LICENSE, `license.spdx_id = Apache-2.0`).
- HEAD at scout time: `8060e8973618ee02ccb7ab35cfff8ac0935a2df6` (2026-10-06), toolchain `leanprover/lean4:v4.34.1`.
- Toolchain history (`cedar-lean/lean-toolchain`):

  | Commit | Date | Toolchain |
  |---|---|---|
  | `017c35c3d1` | 2026-09-25 | v4.34.1 |
  | `3f51c8f7b3...` (parent of the above) | | v4.34.0 |
  | `acb0db7daa` | 2026-09-15 | v4.34.0 |

  Earlier: v4.33.1 (08-25), v4.33.0 (08-14), v4.31.0 (06-23).
- `cedar-lean/lakefile.lean` requires (verbatim):
  ```
  meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
  require "leanprover" / "doc-gen4" @ git "v4.34.1"
  require "leanprover-community" / "batteries" @ git "v4.34.0"
  package Cedar
  ```
  At 3f51c8f both tags are `v4.34.0`.
  - doc-gen4 is only fetched under `-Kenv=dev`.
  - The only runtime dependency is Batteries, locked at `f2effa3d803fda822b1f97b806c47cf2adfbcbc2` in `lake-manifest.json`.
- Suggested require line for our lakefile (Lake `/ "subdir"` syntax; verify `lake update` accepts it):
  `require Cedar from git "https://github.com/cedar-policy/cedar-spec" @ "3f51c8f7b301681da9e6a8f968c1c8070093884a" / "cedar-lean"`
- Mathlib: NOT a dependency (no `import Mathlib` anywhere in the Authorization closure).
  - `Cedar/Thm/Data/List/Lemmas.lean` has 10 comments saying "Copied from Mathlib", and re-states those lemmas in namespace `Cedar.List` (no clash).
  - External imports of the closure: `Batteries.Data.List{,.Basic,.Lemmas}`, `Batteries.Data.String`, `Batteries.Data.UInt`, `Batteries.Tactic.{Init,Case}`, plus Lean core (`Init.Classical`, `Std.Data.HashMap`, `Std.Time{,.Format}`, `Lean.Data.Json.*`, `Lean.Elab.Tactic.Basic`).
- Cedar's `Cedar/Spec/*` files use Lean's `module` system (`module`, `public import`, `@[expose] public section`). The `Cedar/Thm/*` files do not.

### 1.2 Core definitions (verbatim)

`Cedar/Spec/Request.lean`:
```lean
public structure Request where
  principal : EntityUID
  action : EntityUID
  resource : EntityUID
  context : Map Attr Value
```
`Cedar/Spec/Value.lean`:
```lean
public structure EntityUID where
  ty : EntityType        -- EntityType := Name
  eid : String
public inductive Prim where
  | bool (b : Bool) | int (i : Int64) | string (s : String) | entityUID (uid : EntityUID)
public inductive Value where
  | prim (p : Prim) | set (s : Set Value) | record (m : Map Attr Value) | ext (x : Ext)
public inductive Error where
  | entityDoesNotExist | attrDoesNotExist | tagDoesNotExist | typeError | arithBoundsError | extensionError
public abbrev Result (α) := Except Error α
```
`Cedar/Spec/Entities.lean`:
```lean
public structure EntityData where
  attrs : Map Attr Value
  ancestors : Set EntityUID
  tags : Map Tag Value
public abbrev Entities := Map EntityUID EntityData
```
`Cedar/Spec/Policy.lean`:
```lean
public inductive Effect where | permit | forbid
public inductive Scope where
  | any | eq (entity : EntityUID) | mem (entity : EntityUID) | is (ety : EntityType) | isMem (ety : EntityType) (entity : EntityUID)
public inductive ActionScope where
  | actionScope (scope : Scope) | actionInAny (ls : List EntityUID)
public abbrev PolicyID := String
public structure Condition where
  kind : ConditionKind   -- when | unless
  body : Expr
public structure Policy where
  id : PolicyID
  effect : Effect
  principalScope : PrincipalScope
  actionScope : ActionScope
  resourceScope : ResourceScope
  condition : Conditions   -- List Condition
public abbrev Policies := List Policy
@[expose] public def Policy.toExpr (p : Policy) : Expr
public def Policy.allowAll : Policy   -- trivial permit-all
```
`Cedar/Spec/Response.lean`:
```lean
public inductive Decision where | allow | deny
public structure Response where
  decision : Decision
  determiningPolicies : Set PolicyID
  erroringPolicies : Set PolicyID
```
`Cedar/Spec/Evaluator.lean`:
```lean
public def evaluate (x : Expr) (req : Request) (es : Entities) : Result Value
public def inₑ (uid₁ uid₂ : EntityUID) (es : Entities) : Bool :=
  uid₁ == uid₂ || (es.ancestorsOrEmpty uid₁).contains uid₂
```
`inₑ` is ONE lookup of `ancestors`, so the `Entities` store must already hold the transitive closure. Path-prefix via `in` therefore needs a closed ancestor set for every path. The alternative is `like` (`UnaryOp.like (p : Pattern)`, `Pattern := List PatElem`, `PatElem := star | justChar c`, so `*` only).

`Cedar/Spec/Authorizer.lean`:
```lean
public def satisfied (policy : Policy) (req : Request) (entities : Entities) : Bool :=
  (evaluate policy.toExpr req entities) = .ok true
public def satisfiedPolicies (effect : Effect) (policies : Policies) (req : Request) (entities : Entities) : Set PolicyID
public def errorPolicies (policies : Policies) (req : Request) (entities : Entities) : Set PolicyID
public def isAuthorized (req : Request) (entities : Entities) (policies : Policies) : Response :=
  let forbids := satisfiedPolicies .forbid policies req entities
  let permits := satisfiedPolicies .permit policies req entities
  let erroringPolicies := errorPolicies policies req entities
  if forbids.isEmpty && !permits.isEmpty
  then { decision := .allow, determiningPolicies := permits, erroringPolicies }
  else { decision := .deny,  determiningPolicies := forbids, erroringPolicies }
```
Note that a policy that ERRORS is not satisfied, so it neither permits nor forbids. An erroring `forbid` therefore fails open if another permit applies. This matters for encoding hidden paths: the forbid must be total on its request class.

### 1.3 Proved properties (file `Cedar/Thm/Authorization.lean`, namespace `Cedar.Thm`, no `sorry`)
```lean
def PolicyIdsUnique (policies : Policies) :=
  ∀ p₁ ∈ policies, ∀ p₂ ∈ policies, p₁.id = p₂.id → p₁ = p₂
def HasSatisfiedEffect (effect : Effect) (request : Request) (entities : Entities) (policies : Policies) : Prop :=
  ∃ (policy : Policy), policy ∈ policies ∧ policy.effect = effect ∧ satisfied policy request entities
def IsExplicitlyForbidden := HasSatisfiedEffect .forbid
def IsExplicitlyPermitted := HasSatisfiedEffect .permit

theorem forbid_trumps_permit (request : Request) (entities : Entities) (policies : Policies) :
  (IsExplicitlyForbidden request entities policies) →
  (isAuthorized request entities policies).decision = .deny

theorem allowed_only_if_explicitly_permitted (request : Request) (entities : Entities) (policies : Policies) :
  (isAuthorized request entities policies).decision = .allow →
  IsExplicitlyPermitted request entities policies

theorem default_deny (request : Request) (entities : Entities) (policies : Policies) :
  ¬ IsExplicitlyPermitted request entities policies →
  (isAuthorized request entities policies).decision = .deny

theorem allowed_iff_explicitly_permitted_and_not_denied (request : Request) (entities : Entities) (policies : Policies) :
  (IsExplicitlyPermitted request entities policies ∧ ¬ IsExplicitlyForbidden request entities policies) ↔
  (isAuthorized request entities policies).decision = .allow

theorem denied_iff_explicitly_denied_or_not_permitted (request: Request) (entities : Entities) (policies: Policies) :
  (IsExplicitlyForbidden request entities policies ∨ ¬ IsExplicitlyPermitted request entities policies) ↔
    (isAuthorized request entities policies).decision = .deny

theorem order_and_dup_independent (request : Request) (entities : Entities) (policies₁ policies₂ : Policies) :
  policies₁ ≡ policies₂ →
  isAuthorized request entities policies₁ = isAuthorized request entities policies₂

theorem unchanged_allow_when_add_permit (request: Request) (entities: Entities) (policies: Policies) (policy₂: Policy) :
  policy₂.effect = .permit →
  (isAuthorized request entities policies).decision = .allow →
  (isAuthorized request entities (policy₂ :: policies)).decision = .allow

theorem unchanged_deny_when_add_forbid (request : Request) (entities: Entities) (policies: Policies) (policy₂: Policy) :
  policy₂.effect = .forbid →
  (isAuthorized request entities policies).decision = .deny →
  (isAuthorized request entities (policy₂ :: policies)).decision = .deny

theorem determiningPolicies_of (request: Request) (entities: Entities) (policies: Policies) :
  let auth := isAuthorized request entities policies
  auth.determiningPolicies = satisfiedPolicies (if auth.decision = .allow then .permit else .forbid) policies request entities

theorem unchanged_determining_when_add_policy_and_decision_unchanged ...   -- determiningPolicies monotone
theorem unchanged_erroring_when_add_policy ...                              -- erroringPolicies monotone
theorem determining_erroring_disjoint_when_unique_ids (request : Request) (entities : Entities) (policies : Policies) :
  PolicyIdsUnique policies →
    ((isAuthorized request entities policies).determiningPolicies ∩ (isAuthorized request entities policies).erroringPolicies).isEmpty
```
Also in the same file: `satisfied_iff_satisfiedPolicies_non_empty`, `explicitly_forbidden_iff_satisfying_forbid`, `explicitly_permitted_iff_satisfying_permit`.

Slicing (`Cedar/Thm/PolicySlice.lean`; defs in `Cedar/Slice/PolicySlice.lean`):
```lean
theorem isAuthorized_eq_for_sound_policy_slice (req : Request) (entities : Entities) (slice policies : Policies) :
  IsSoundPolicySlice req entities slice policies →
  isAuthorized req entities slice = isAuthorized req entities policies
theorem sound_bound_analysis_produces_sound_slices (ba : BoundAnalysis) (request : Request) (entities : Entities) (policies : Policies) :
  IsSoundBoundAnalysis ba → IsSoundPolicySlice request entities (ba.slice request entities policies) policies
theorem scope_bound_is_sound (policy : Policy) : IsSoundPolicyBound (scopeAnalysis policy) policy
theorem scope_analysis_is_sound : IsSoundBoundAnalysis scopeAnalysis
theorem isAuthorized_eq_for_scope_based_policy_slice (request : Request) (entities : Entities) (policies : Policies) :
  isAuthorized request entities (BoundAnalysis.slice scopeAnalysis request entities policies) =
  isAuthorized request entities policies
```

Typechecking (`Cedar/Thm/Typechecking.lean`):
```lean
def typecheck (policy : Policy) (env : TypeEnv) : Except TypeError CedarType
theorem typecheck_is_sound (policy : Policy) (env : TypeEnv) (t : CedarType) (request : Request) (entities : Entities) :
  InstanceOfWellFormedEnvironment request entities env →
  typecheck policy env = .ok t →
  (∃ (b : Bool), EvaluatesTo policy.toExpr request entities b)
```
`EvaluatesTo` allows a bool or the errors `entityDoesNotExist`, `extensionError`, `arithBoundsError`.

Validation (`Cedar/Thm/Validation.lean`):
```lean
theorem validation_is_sound (policies : Policies) (schema : Schema) (request : Request) (entities : Entities) :
  schema.validateWellFormed = .ok () → validate policies schema = .ok () →
  validateRequest schema request = .ok () → validateEntities schema entities = .ok () →
  AllEvaluateToBool policies request entities
theorem validate_with_level_is_sound {ps : Policies} {schema : Schema} {n : Nat} {request : Request} {entities : Entities}
  (hwf : schema.validateWellFormed = .ok ()) (hr : validateRequest schema request = .ok ())
  (he : validateEntities schema entities = .ok ()) (htl : validateWithLevel ps schema n = .ok ()) :
  isAuthorized request entities ps = isAuthorized request (entities.sliceAtLevel request n) ps
theorem validate_with_level_no_dne ...   -- no policy evaluates to .entityDoesNotExist when entities closedAtLevel
theorem validation_is_sound_response ... -- erroring policies only fail with the 3 unavoidable errors (needs PolicyIdsUnique)
theorem error_of_mem_erroringPolicies ...
```
Other directories in `Cedar/Thm/`: `Thm/SymbolicCompilation.lean`, `Thm/Verification.lean` (SMT-based equivalence and implication checks, sound and complete), `Thm/TPE.lean` (partial evaluation), `Thm/WellTyped*`. These are irrelevant for us.

### 1.4 Size of the import closure (computed by BFS over `import` lines from raw source)

| Root module | .lean files | Lines |
|---|---|---|
| `Cedar.Spec` (isAuthorized + evaluator, no theorems) | 25 | 3,208 |
| `Cedar.Thm.Authorization` (all theorems in §1.3 first block + slice) | 75 | ~21.8k |
| `Cedar.Thm.PolicySlice` | 75 | ~21.6k |
| `Cedar.Thm.Typechecking` | 83 | ~25.1k |
| `Cedar.Thm.Validation` | 117 | ~31.7k |

- Whole `cedar-lean/`: 360 .lean files in 414 blobs (279 under `Cedar/`, of which 206 under `Cedar/Thm/`).
- Why `Thm.Authorization` is not tiny: `Thm/Authorization/Authorizer.lean` imports `Cedar.Thm.Validation.Typechecker.BinaryApp`. That drags in the TPE, Validation and WellTyped proof files.
- Biggest files in the closure: `Cedar.Thm.Data.List.Lemmas` (2,255 lines), `Cedar.Thm.Data.Map` (1,859), `Cedar.Thm.WellTyped.Expr.Typechecking` (1,704).
- Only the imported closure is built when we `import` just these modules. Cold build time is UNMEASURED (not allowed to build).
- Cedar.Spec by itself cannot be shrunk cheaply, because Evaluator, Expr and ExtFun pull in `Cedar.Spec.Ext.{Datetime,IPAddr,Decimal}` (~700 lines).

### 1.5 Axiom hygiene of the Authorization closure (textual scan of the 75 files)
- 0 `sorry`, 0 `axiom`, 0 `unsafe`, 0 `implemented_by`, 0 `partial def`, 0 `ofReduceBool`.
- ONE `native_decide` hit: `Cedar/Data/Int64.lean` lines 101 and 106, inside `toInt_nonneg_of_ge_zero` and `toInt_neg_of_not_ge_zero`.
  - Both lemmas have no other textual use in the closure, so downstream theorems should not inherit `Lean.ofReduceBool`.
  - UNVERIFIED: run `#print axioms Cedar.Thm.forbid_trumps_permit` etc. once Cedar is built.
  - If we vendor Int64, replace those two with `by decide` or `rfl`.
- `Classical` appears in 4 files (standard).

### 1.6 Fit for the action layer
- Cedar is stateless and per-request. It has no sequences, no reachability and no resource accounting.
  - Reachability must be ours.
  - Cedar supplies the monitor's decision function and its default-deny and forbid-wins lemmas.
- Natural encoding of the sandbox: entity types `File`, `Dir`, `Proc`, `Net`; actions `Action::"read" | "write" | "exec" | "connect"`.
  - Hidden dirs become `forbid (principal, action, resource) when { resource in Dir::"/home/opc/research" }`.
  - The base rule is `permit (principal, action, resource)` (default-allow, like `--dev-bind / /`).
  - `forbid_trumps_permit` is then exactly the "hidden path is never readable" lemma.
  - Caveat: the entity store must supply the transitive ancestor sets (`inₑ` is 1-step). Symlinks and `..` are not in Cedar at all.

---

## 2. Veil (verse-lab/veil)

### 2.1 Metadata
- Licence: Apache-2.0. HEAD `626901534a8c788e45b350328021cd4d7a942c32` (2026-10-06). README: "Veil 2.0 Pre-Release".
- `lean-toolchain`: `leanprover/lean4:v4.32.0`.
  - It cannot share a Lake workspace with a v4.34.0 project: Batteries, aesop, lean-smt, Loom and cvc5 are all pinned to 4.32.
  - ControlStack's own comment says "Never make a third Lake project".
- `lakefile.lean` requires (verbatim):
  ```
  require smt from git "https://github.com/verse-lab/lean-smt.git" @ "v4.32.0-veil-no-mathlib"
  require Loom from git "https://github.com/verse-lab/loom.git" @ "v4.32.0-for-veil"
  require VerifiedHAMT from git "https://github.com/verse-lab/VerifiedHAMT.git" @ "cf6ee753ee223be0d23ba82e21feecbd0833819f"
  require batteries from git "https://github.com/leanprover-community/batteries" @ "v4.32.0"
  require aesop from git "https://github.com/leanprover-community/aesop" @ "v4.32.0"
  require proofwidgets from git "https://github.com/leanprover-community/ProofWidgets4" @ "6e311e2a844da9b2cc3971187df2fe0066947b93"
  ```
  Transitive: lean-cvc5 (`a3ffc29`, builds the cvc5 solver in-process via FFI), lean-auto (`1175ff6`), Qq, ProofWidgets.
- No Mathlib (the lean-smt branch is the "no-mathlib" fork), so there is no Mathlib clash.
- All of these dependencies are Apache-2.0.
- Build needs: NodeJS and npm (`Veil` lib has `needs := #[widgetJsAll]`, a rollup/TypeScript widget build) and clang/lld/libc++ (lean-cvc5; the CI installs clang-15).
- Size: 247 .lean files and ~45k lines in `Veil/`.

### 2.2 Core interface (relevant definitions, `Veil/Core/Tools/ModelChecker/TransitionSystem.lean`)
```lean
structure RelationalTransitionSystem (ρ : Type) (σ : Type) (l : outParam Type) extends TransitionSystem ρ σ l where
  assumptions : ρ → Prop
  init : ρ → σ → Prop
  tr : ρ → σ → l → σ → Prop
def RelationalTransitionSystem.next (sys : RelationalTransitionSystem ρ σ l) (th : ρ) (s s' : σ) : Prop :=
  ∃ label, sys.tr th s label s'
inductive RelationalTransitionSystem.reachable (sys : RelationalTransitionSystem ρ σ l) (th : ρ) : σ → Prop where
  | init : ∀ (s : σ), sys.assumptions th → sys.init th s → sys.reachable th s
  | step : ∀ (s s' : σ), sys.reachable th s → sys.next th s s' → sys.reachable th s'
theorem reachable_assumptions ...
theorem reachable_inclusion (sys sys') (hass_implies) (hinit_implies) (hnext_implies) :
  ∀ r st, sys.reachable r st → sys'.reachable r st
theorem EnumerableTransitionSystem.reachable_equiv_relational ...
```
- This is a ~60-line, Mathlib-free pattern worth copying. It lives in a `module` file that imports only `Veil.Core.Tools.ModelChecker.ExecutionOutcome` (40 lines, no further imports).
- Veil's DSL (`veil module`, `type`, `relation`, `action`, `invariant`, `safety`, `#check_invariants`, `#model_check`) generates induction VCs (init ⇒ inv, inv ∧ action ⇒ inv'). The DSL targets first-order protocol specs with `Bool`-valued relations.
  - A `grep` of `Veil/` (excluding the model checker) finds NO generated theorem of the form `reachable → safety`. The only `.reachable` uses are in `ModelChecker/` (e.g. `MapReduceLemmas.lean:70`).
  - The DSL does assemble a `RelationalTransitionSystem` instance for each module (`Module/Util/Assemble.lean:338-359`), but nothing links it to the invariant VCs. So even with Veil, the `Reachable → ¬Bad` bridge would be ours.
- Veil is a poor fit for path and string state, which is not an EPR/FOL fragment.

### 2.3 Solvers and axioms (matters for the "standard axioms only" gate)
- `register_option veil.smt.trust : Bool := { defValue := true, descr := "If true, `veil_smt` trusts unsat results from the SMT solver. If false, `veil_smt` asks the SMT backend to reconstruct Lean proofs." }` (`Veil/Base.lean:144`).
  - DEFAULT = TRUST. A trusted VC is closed with a non-synthetic `sorry`, i.e. `sorryAx`. The tool prints "Trusting SMT solver for N goals. `set_option veil.smt.trust false` to enable proof reconstruction." (`Verification.lean:164`).
  - That kernel-fails the gate. VeilTest sets `weak.veil.smt.trust false`.
- With `veil.smt.trust false`, lean-smt reconstructs proofs from cvc5 output. The solver is cvc5 linked in-process through `lean-cvc5` FFI, not an external z3/cvc5 binary at proof time, but it is built from source at install.
  - Kernel checks the reconstruction, so the solver is not in the TCB in that mode.
  - UNVERIFIED which axioms reconstruction uses. lean-smt textually has `Classical.propDecidable` (standard).
  - lean-smt ALSO contains literal `sorry` in lemma libraries: `Smt/Reconstruct/Rat/Lemmas.lean:81`, `Rat/Rewrites.lean:59,71,75` and `BitVec/Bitblast.lean:42`. Any proof using those rule families carries `sorryAx`. Per-theorem `#print axioms` is mandatory.
  - No literal `axiom` declarations exist in lean-smt (scan of 156 files) or in Veil (scan of 247 files).
- `native_decide`: Veil's default finite-sort discharge is `first | decide | native_decide` (`Module/Elaborators/Core.lean:614`). `native_decide` is also a default argument in `Veil/Util/ShardedSetUInt.lean:217-250` and `MapReduceLemmas.lean:12-13`.
  - That introduces `Lean.ofReduceBool`, which conflicts with the gate unless overridden. The compiled `#model_check` runtime is a test tool, not a proof.
- The interactive path `@[veil] theorem` (`TheoremDischarger.lean`) is plain Lean and gate-compatible.
- Conclusion: Veil can only be used under the gate with `trust=false`, no `native_decide` fallback and per-theorem axiom audit. It cannot be used from our v4.34.0 project at all.

---

## 3. `~/research/proofledger/harness/dispatch.py`: the policy actually implemented

Source: `sandbox(work)` lines 48-62 (plus `HIDE_DIRS`/`HIDE_FILES` at 38-45, `MATHLIB_PROJ` and `WORK_CAP_BYTES` at 65-66, `_du` and `_run_capped` at 69-98, `call()` at 101-150).
- The `sandbox()` docstring claims "host fs visible EXCEPT the hidden paths; private /tmp; writable scratch only". The last clause is not true of the code (G1).
- Rules S1-S5 below refer to the processes started under the `bwrap` prefix, i.e. the model CLI (`codex exec` or `agy-gemini`) and everything it spawns.

### 3.1 Exact bwrap command prefix (order matters; bwrap applies args left to right)
```
bwrap --dev-bind / /  --tmpfs /var/tmp  --bind <W> /var/tmp/work
      [--tmpfs <d> for d in HIDE_DIRS if d.exists()]
      [--bind <W>/.empty <f> for f in HIDE_FILES if f.exists()]
      --ro-bind <MATHLIB_PROJ> <MATHLIB_PROJ>
      --chdir /var/tmp/work --
```
with `HOME=/home/opc`. W is the per-call scratch `/var/tmp/pl-<token_hex(6)>` created with mode 0o700, containing `.empty` and, on the codex path, `prompt.md`.
Flags NOT present: `--unshare-*` (all), `--clearenv`, `--unsetenv`, `--die-with-parent`, `--new-session`, `--cap-drop`, `--seccomp`, `--proc`, `--dev`, `--size`.

### 3.2 Rules a Lean model could encode (state: set of mounts, per-path visibility and mode)
- S1 (base visibility). Every host path is visible. `--dev-bind / /` is READ-WRITE and includes devices. bwrap binds are recursive, so sub-mounts like host `/proc`, `/sys`, `/dev` come along. Access is limited only by Unix perms of uid 1000 (`opc`, groups adm, systemd-journal, docker).
- S2 (private /var/tmp). Path `p` is visible iff `p` is not under `/var/tmp`, or `p` is under `/var/tmp/work`. `/var/tmp/work` is W, read-write. Everything else under `/var/tmp` is an empty RAM tmpfs (writable, discarded at exit). This hides sibling scratch dirs such as other `pl-*` dirs and `/var/tmp/opus-provers`.
- S3 (hidden dirs). If the dir exists at call time, its entire subtree is replaced by an empty writable tmpfs (reads see nothing; writes are discarded at exit):
  - `/home/opc/research` (proofledger ledger, campaigns, `.gate`, control-stack, all research)
  - `/home/opc/.claude` (transcripts, memory)
  - `/tmp`
  - `/home/opc/.codex/sessions`, `.codex/log`, `.codex/shell_snapshots`
  - `/home/opc/.gemini/tmp`
  - `/home/opc/.gemini/antigravity-cli/brain`, `.../conversations`, `.../scratch`, `.../log`
- S4 (hidden file). `/home/opc/.codex/history.jsonl` is replaced by `W/.empty` (empty file; reads see empty, writes land in W and count toward the cap). The bind is read-write.
- S5 (single read-only exception, inside hidden space). `MATHLIB_PROJ = /home/opc/research/alignment-contrib/lean/StabilityDebate` is mounted READ-ONLY after the `~/research` tmpfs. Only this path, plus auto-created parent dirs, is visible under `~/research`; siblings stay hidden. `proofledger` is a sibling and stays hidden. Writes to it return EROFS.
- S6 (cwd). `/var/tmp/work` (= W).
- Network: NONE of it is restricted at the bwrap level (shared net namespace: all interfaces, loopback services, tailnet). The codex path additionally runs `codex exec --sandbox read-only` (Codex's own tool sandbox: tool-call FS read-only, network off by default, UNVERIFIED for this CLI version); the codex CLI process itself and `agy-gemini` use the network to reach their APIs. The agy path has no inner sandbox.
- Environment: `ENV = {**os.environ, "AI_BUDGET_ALLOW": "1"}` is passed to Popen, so bwrap and the model CLI inherit the ENTIRE harness environment (no scrubbing) plus `AI_BUDGET_ALLOW=1`, which makes `~/.local/bin/ai-budget` bypass the budget guard (lines 430-431 of that script). `PATH` is inherited. `HOME` is not remapped.
- Process limits: none. No rlimits, no cgroup, no PID namespace, no seccomp. The only mechanisms are the following.
  - W1. `Popen(..., start_new_session=True)`: a new session and process group, so there is no controlling tty (mitigates TIOCSTI).
  - W2. Scratch watchdog: `communicate(timeout=10)` is polled in a loop. Every ~10 s, if `_du(W) > WORK_CAP_BYTES = 300 * 2**20` (314,572,800 B) OR elapsed > `timeout` (default `call(timeout=2400)` = 40 min), then `os.killpg(p.pid, SIGKILL)`. The `err` string gets `"KILLED: scratch {n} MB or timeout"` appended.
  - W3. `_du(W)` = sum of `lstat().st_size` over non-directory entries from `os.walk(W)` (no symlink following; apparent size, not blocks; only W is counted).
  - W4. After the call, `shutil.rmtree(W, ignore_errors=True)`.
- Other facts: the `agy` prompt is passed in argv (limit 120,000 bytes, else `ValueError`); the `codex` prompt is passed via stdin from `W/prompt.md` and output is written with `-o /var/tmp/work/out.md` then copied to the caller's `out`.
- Lean gate (`leangate.py`) is separate and NOT sandboxed: `lake env lean` runs in `PROJ` (the same StabilityDebate project) with `PATH=~/.elan/bin:...`, and `OK_AXIOMS = {"propext","Classical.choice","Quot.sound"}`.

### 3.3 Gaps (V = verified from source, H = hypothesis needing a test)
- G1 (V). Writes are NOT confined to scratch. Because `--dev-bind / /` is read-write, a sandboxed model can write anywhere uid `opc` can: `~/.bashrc` and other dotfiles, `~/.local/bin` (this is where `ai-budget`, `agy-gemini` and `codex` live), crontabs, projects, `~/loops`, `~/.config/claude-sandbox/tech-radar.env`, and the elan toolchain `~/.elan` that the unsandboxed Lean gate executes (forging the gate verdict). Only `MATHLIB_PROJ` is read-only. The 300 MB cap covers only W.
  - Unmetered write paths: `~/.cache/mathlib` (the original incident's `lake` cache), `~/.cache` generally, `~/.elan`, `~/`.
  - Also unmetered: RAM tmpfs writes to `/tmp`, `/var/tmp/*` (other than W) and the hidden dirs. These have no `--size`, so an OOM is possible.
- G2 (V). Credentials and logs outside `HIDE_*` are readable: `~/.codex/auth.json` (not in `HIDE_FILES`), `~/.config/claude-sandbox/tech-radar.env` (Gemini key per memory), `~/.gnupg`, `~/.cloudflared`, `~/.mozilla`, `~/.megaCmd`, `~/.bash_history`, `~/.codex/*.sqlite` (`state_5`, `logs_2`, `thread_history_1`, `memories_1`, `queue_1`: other models' conversation state NOT hidden; only `sessions`, `log`, `shell_snapshots` and `history.jsonl` are), `~/loops`, `~/handoff`, `~/CLAUDE.md`, `~/AGENTS.md`. Whether `~/.ssh` exists was not probed.
- G3 (V). Network unrestricted for the agy path (and for the CLI process itself): any file visible per S1 can be exfiltrated, including via the tailnet. The memory note says `opc` = root-equivalent on the tailnet; the service-user egress guard does not apply to `opc`.
- G4 (V). Full env inheritance: any secrets exported in the harness shell are visible to the model and its tools (`/proc/self/environ`). `AI_BUDGET_ALLOW=1` additionally disables the budget guard.
- G5 (H, likely). No PID namespace and `kernel.yama.ptrace_scope = 0` on this box (read from /proc/sys). A sandboxed process can enumerate host `/proc`.
  - It can read `/proc/*/cmdline` of sibling provers (agy prompts are in argv, up to 120 KB).
  - It can read `/proc/<pid>/environ`.
  - It can traverse `/proc/<pid>/root` and `/proc/<pid>/cwd` of the unsandboxed harness parent, which sees the REAL `~/research` and `/tmp`. This reaches around the S3 tmpfs hiding.
  - It can traverse the root of sibling sandboxed processes, e.g. `/proc/<sibling>/root/var/tmp/work` (their `out.md` and `prompt.md`).
  - Same-uid `kill` of any host process is possible.
  - This is exactly the cross-prover copy channel the hiding is meant to close. UNTESTED, because we were told not to run anything.
- G6 (V). `--die-with-parent` is absent. If the harness dies the sandboxed tree survives; `killpg` also misses descendants that `setsid`/`setpgid` out (no PID ns reaping). Combined with no PID ns, a malicious child can survive the watchdog and keep writing after `rmtree`.
- G7 (V). Watchdog weaknesses.
  - Poll interval 10 s, so a fast writer can overshoot the cap by (write-rate × 10 s).
  - `_du` uses apparent sizes: sparse files over-count (false kills) and many tiny files, inodes and directories under-count.
  - It ignores everything outside W (G1).
  - `call()`'s `except subprocess.TimeoutExpired` (rc 124) is dead code, because the loop swallows `TimeoutExpired`. Real timeouts appear as rc = −9 with a "KILLED" tail.
- G8 (V/H). `/var/tmp` hiding works by mount path only; the underlying host `/var/tmp/pl-*` directories are visible to any unsandboxed process or via G5.
- G9 (H, from `id`). `opc` is in group `docker` (gid 985). If `/var/run/docker.sock` exists (not probed), it is visible through `--dev-bind /` and gives a root-equivalent full escape (`docker run -v /:/h`). Also relevant: the box note says `opc` = root on the tailnet.
- G10 (V). Symlinks and `..`: no normalisation is enforced. Hiding is by mount point. A symlink elsewhere pointing into a hidden dir resolves inside the sandbox's mount namespace to the empty tmpfs (safe). A path reachable by a different mount (e.g. a bind of the same filesystem at another path, or `/proc/<pid>/root`) is NOT hidden. The hidden-path predicate is on mount-namespace paths, not inode identity.
- G11 (V). `HIDE_DIRS` entries are only applied `if d.exists()` at call time. A dir created later (e.g. a new `~/.gemini/antigravity-cli/...` subdir or another `~/.codex/*` store) is not hidden. The list is a denylist (default visible).
- G12 (V). The codex inner `--sandbox read-only` applies only to the codex path; Gemini (agy) tool use is wholly un-sandboxed beyond S1-S6.

### 3.4 What a faithful Lean model must therefore say (suggested abstraction)
- Policy is a denylist: `visible p := ¬ hiddenTmpfs p ∨ p ∈ roExceptions`.
  - `read p` is allowed for all `p` except under the hidden set. For hidden `p` it returns an empty view, not an error.
  - `write p` is allowed everywhere uid-permitted except under `MATHLIB_PROJ` (EROFS). Writes under hidden dirs, `/tmp` and non-W `/var/tmp` are discarded at exit; writes under W persist until `rmtree`.
  - Writes to W increase `scratchBytes`; `scratchBytes > 300 MiB` at a poll tick (10 s granularity) kills the group, which a model can express as "bound overshoot ≤ rate·10 s".
- A theorem like "no allowed action sequence reads path P" is TRUE only for `P ∈ hiddenSet` modulo G5; for P outside the hidden set it is false by construction.
- Network and `exec` are unconstrained. The model should include `connect` as an always-allowed action and state exfiltration as "read ∘ connect".
- The meaningful guarantee is therefore narrow: "no action sequence confined to the mount-namespace file API reads a hidden path", plus "writes to MATHLIB_PROJ fail". Anything stronger needs the fixes above: `--unshare-pid` (plus `--die-with-parent`, `--proc /proc`, `--dev /dev`), `--ro-bind / /` with explicit `--bind` for W, `--unshare-net` or an allowlist proxy, `--clearenv`, and a cgroup or rlimit memory/pid cap.

---

## 4. Recommendation for the action layer

Choose the hybrid (a)+(c): depend on Cedar for decision semantics, and write plain Lean for the transition system and reachability. Do not vendor (b) and do not depend on Veil.

Justification:
1. Toolchain and size.
   - Cedar @ `3f51c8f` is Lean v4.34.0 with Batteries rev `f2effa3d...`, byte-identical to ControlStack's locked Batteries. No Mathlib needed, so no new Lake project and no version conflict.
   - Importing only `Cedar.Spec` costs 25 files / 3.2k lines. Importing `Cedar.Thm.Authorization` costs 75 files / 21.8k lines (the theorems are in the same chain), which is affordable beside the Mathlib/VCVio build we already carry.
   - Veil is Lean v4.32.0 with a dependency stack (lean-cvc5, npm, clang) that cannot coexist with the 4.34.0 workspace.
2. Why not vendor a slice (b).
   - The toolchain matches, so vendoring adds drift and duplicates Apache-2.0 notices for no gain.
   - A slice of `isAuthorized` still needs Evaluator, Expr, Value and Ext (~25 files) and, for the theorems, ~7k lines of `Cedar.Thm.Data` lemmas.
   - Only a hand-made mini-policy language would be small, and that is (c) with extra steps.
3. What Cedar gives us.
   - `forbid_trumps_permit`, `default_deny`, `allowed_iff_explicitly_permitted_and_not_denied`, `order_and_dup_independent`, `unchanged_*`, and slicing soundness for policy sets.
   - The sandbox's "default-visible, denylist-hidden" shape is `permit` + `forbid when resource in Dir::"..."`, and `forbid_trumps_permit` is the hidden-path lemma.
4. What we must write ourselves (Cedar cannot).
   - The transition system: state = (mount view, scratchBytes, process alive, net), steps = tool calls (`read`, `write`, `exec`, `connect`), and a `Reachable` inductive in the style of Veil's `RelationalTransitionSystem.reachable` (cite it, re-derive; do not import).
   - The bridge: `monitorAllows s call ↔ (Cedar.Spec.isAuthorized (encode call) entitiesOf(s) policiesOf(sandboxRules)).decision = .allow` for the fragment we use, plus the `Reachable → ¬ReadsHidden` theorem.
   - A faithful model of the gaps in §3.3 as explicit assumptions or as "model is of the intended policy, not of dispatch.py", rather than silently idealising them.
5. Cheap pre-flight checks before committing (none were possible in this read-only task).
   - `#print axioms Cedar.Thm.forbid_trumps_permit` and `Cedar.Thm.default_deny` must show only `propext`, `Classical.choice`, `Quot.sound`.
   - Confirm `lake update` accepts the `/ "cedar-lean"` subdir require against Mathlib+VCVio (Batteries rev is shared, so no conflict expected).
   - Measure cold build of the 75-file closure.
6. Design risks for the Cedar encoding.
   - `inₑ` is 1-step, so `Entities` must be pre-closed under ancestors (or encode prefixes via `like "/home/opc/research/*"`).
   - A policy that errors is neither satisfied nor determining, so an erroring `forbid` fails open under a `permit`. Keep forbid conditions total, and prove totality (`validation_is_sound` and the scope-does-not-throw lemmas help).
   - Cedar has no path normalisation or symlink semantics; model paths as already-resolved canonical strings and state that as an assumption (G10).

## 5. Housekeeping
Scratch files used during the scout were fetched into `/tmp/cedar_scout`, `/tmp/leansmt_src`, `/tmp/veil_src`, `/tmp/cedar_tree.tsv`, `/tmp/veil_tree.txt`, `/tmp/lean-smt_tree.txt` and `/tmp/loom_tree.txt`, and were deleted at the end. No repository was cloned, nothing was built, and nothing was written under `/home/opc` except this file.
