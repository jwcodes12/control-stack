/-
SC-08: no unauthorized process or executable runs.

An abstract exec-mediation model (family F1):
- a filesystem of paths with mutable contents; which paths are writable and which mounts are `noexec` is trusted
  configuration (`Env`);
- every exec is decided by a trusted policy at exec time on the content actually loaded: the content's DIGEST must be on
  an allowlist (`byDigest`); exec from a `noexec` mount is refused;
- interpreters are binaries whose script ARGUMENT is also code: an allowlisted interpreter runs only with a script whose
  digest is on the script allowlist (`scriptCheck`), never without one (REPL / stdin);
- an absorbing admin HALT.

Main results (adversary class TRACE_ARBITRARY: any writes to writable paths, any exec requests with any script
argument):
- `safe_of_sound`: for every configuration that checks digests and scripts (`Sound`), after any trace from an initial
  state with no runs, every exec'd program has an allowlisted digest, and every interpreter run had a script with an
  allowlisted digest. `sc08_safe` is the deployed instance; `digest_design_needs_no_noexec` records that with digest
  allowlisting the `noexec` mount check is defence in depth, not needed for this property;
- `halt_freezes`; `sys`/`spec` (client of `Core/Gate.lean`); non-vacuity `honest_execs`.

Necessity witnesses: `path_allowlist_toctou_breaks` (identity by path: the agent replaces the content behind an
allowlisted path), `writable_exec_mount_breaks` (with a path allowlist, a writable mount that is not `noexec` is
exploitable while a `noexec` one is not), `interpreter_loophole_breaks` (allowlisted interpreter, arbitrary script),
`interpreter_repl_breaks`, `no_halt_check_breaks`.

Premises outside the model: exec is mediated for every process (no other loader, no JIT/`memfd` path unless it is also
mediated), the loaded bytes are the bytes hashed (fd-pinned), the digest is collision-resistant, and interpreters are
correctly identified by digest. Not claimed: that allowlisted programs are harmless or cannot be misused through
their own legitimate features. No new mathematics.
-/
import Mathlib.Tactic
import ControlStack.Core.Gate

namespace ControlStack.SC08

open ControlStack.Gate

/-- trusted configuration -/
structure Env where
  h : ℕ → ℕ
  writable : ℕ → Bool
  noexecMount : ℕ → Bool
  allow : List ℕ
  interp : List ℕ
  scripts : List ℕ
  pathAllow : List ℕ
  admins : List ℕ

structure St where
  /-- (path, content), newest write first -/
  files : List (ℕ × ℕ)
  /-- runs: (program content, script content) -/
  ran : List (ℕ × Option ℕ)
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | write (path content : ℕ)
  | exec (path : ℕ) (script : Option ℕ)
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  byDigest : Bool
  noexec : Bool
  scriptCheck : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true⟩

def fileAt (s : St) (p : ℕ) : Option ℕ := (s.files.find? (fun e => e.1 = p)).map Prod.snd

/-- the exec decision on the CURRENT contents: the run it produces, or none if refused -/
def execResult (E : Env) (C : Checks) (s : St) (path : ℕ) (script : Option ℕ) : Option (ℕ × Option ℕ) :=
  match fileAt s path with
  | none => none
  | some c =>
    if (C.noexec = true → E.noexecMount path = false) ∧ (if C.byDigest then E.h c ∈ E.allow else path ∈ E.pathAllow)
    then
      if E.h c ∈ E.interp then
        match script with
        | none => if C.scriptCheck then none else some (c, none)
        | some sp =>
          match fileAt s sp with
          | none => none
          | some sc => if C.scriptCheck = true → E.h sc ∈ E.scripts then some (c, some sc) else none
      else some (c, none)
    else none

def step (E : Env) (C : Checks) (s : St) : Op → St
  | .write p x =>
    if s.halted ∧ C.haltCheck then s else if E.writable p then { s with files := (p, x) :: s.files } else s
  | .exec p sc =>
    if s.halted ∧ C.haltCheck then s
    else match execResult E C s p sc with
      | none => s
      | some r => { s with ran := s.ran ++ [r] }
  | .halt c => if c ∈ E.admins then { s with halted := true } else s

def run (E : Env) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step E C) s

theorem run_cons (E : Env) (C : Checks) (s : St) (o : Op) (ops : List Op) :
    run E C s (o :: ops) = run E C (step E C s o) ops := rfl

/-! ## Safety -/

/-- an allowlisted program, and for an interpreter an allowlisted script -/
def RunOk (E : Env) (r : ℕ × Option ℕ) : Prop :=
  E.h r.1 ∈ E.allow ∧ (E.h r.1 ∈ E.interp → ∃ sc, r.2 = some sc ∧ E.h sc ∈ E.scripts)

def Good (E : Env) (s : St) : Prop := ∀ r ∈ s.ran, RunOk E r

/-- configurations that check digests of programs and scripts -/
structure Sound (C : Checks) : Prop where
  byDigest : C.byDigest = true
  scriptCheck : C.scriptCheck = true

theorem sound_full : Sound full := ⟨rfl, rfl⟩

theorem execResult_ok (E : Env) {C : Checks} (hC : Sound C) (s : St) (p : ℕ) (sc : Option ℕ) (r : ℕ × Option ℕ)
    (h : execResult E C s p sc = some r) : RunOk E r := by
  unfold execResult at h
  rw [hC.byDigest, hC.scriptCheck] at h
  split at h
  · simp at h
  · rename_i c _
    simp only [ite_true, true_implies] at h
    split_ifs at h with h1 h2
    · split at h
      · simp at h
      · split at h
        · simp at h
        · rename_i sc' _
          split_ifs at h with h3
          · cases h; exact ⟨h1.2, fun _ => ⟨sc', rfl, h3⟩⟩
    · cases h; exact ⟨h1.2, fun hi => absurd hi h2⟩

theorem step_good (E : Env) {C : Checks} (hC : Sound C) (s : St) (o : Op) (h : Good E s) : Good E (step E C s o) := by
  cases o with
  | write p x => simp only [step]; split_ifs <;> exact h
  | exec p sc =>
    simp only [step]
    split_ifs
    · exact h
    · split
      · exact h
      · rename_i r hr
        intro x hx
        rcases List.mem_append.1 hx with hx | hx
        · exact h x hx
        · simp at hx; subst hx; exact execResult_ok E hC s p sc _ hr
  | halt c => simp only [step]; split_ifs <;> exact h

theorem run_good (E : Env) {C : Checks} (hC : Sound C) (s : St) (ops : List Op) (h : Good E s) :
    Good E (run E C s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => rw [run_cons]; exact ih _ (step_good E hC s o h)

/-- **SC-08 safety for any digest-checking configuration.** From any state with no runs yet (any initial files),
after any trace, every exec'd program has an allowlisted digest, and every interpreter run had a script with an
allowlisted digest. Adversary: TRACE_ARBITRARY. -/
theorem safe_of_sound (E : Env) {C : Checks} (hC : Sound C) (files : List (ℕ × ℕ)) (ops : List Op) :
    Good E (run E C ⟨files, [], false⟩ ops) :=
  run_good E hC _ ops (by simp [Good])

/-- **SC-08 safety with all checks on (model):** from any initial files and no runs, after any trace every recorded
run satisfies `RunOk` (allowlisted program digest; allowlisted script digest for interpreter runs). This is
`safe_of_sound` at the `full` configuration. -/
theorem sc08_safe (E : Env) (files : List (ℕ × ℕ)) (ops : List Op) : Good E (run E full ⟨files, [], false⟩ ops) :=
  safe_of_sound E sound_full files ops

/-- with digest allowlisting, the property holds even without the `noexec` mount check (defence in depth) -/
theorem digest_design_needs_no_noexec (E : Env) (files : List (ℕ × ℕ)) (ops : List Op) :
    Good E (run E { full with noexec := false } ⟨files, [], false⟩ ops) :=
  safe_of_sound E ⟨rfl, rfl⟩ files ops

/-! ## Halt -/

theorem step_halted (E : Env) (s : St) (o : Op) (hh : s.halted = true) : step E full s o = s := by
  cases o with
  | halt c =>
    simp only [step]
    split_ifs
    · cases s; simp_all
    · rfl
  | _ => simp [step, full, hh]

/-- **Halt freezes execution**: once halted, no trace changes the state. -/
theorem halt_freezes (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s := by
  induction ops with
  | nil => rfl
  | cons o ops ih => rw [run_cons, step_halted E s o hh, ih]

/-! ## Client of the shared gate interface -/

theorem ran_prefix (E : Env) (C : Checks) (s : St) (o : Op) : s.ran <+: (step E C s o).ran := by
  cases o with
  | exec p sc =>
    simp only [step]
    split_ifs
    · exact List.prefix_refl _
    · split
      · exact List.prefix_refl _
      · exact List.prefix_append _ _
  | _ => simp only [step]; split_ifs <;> exact List.prefix_refl _

def sys (E : Env) : System St Op (ℕ × Option ℕ) where
  step := step E full
  effects := St.ran

def spec (E : Env) : Spec (sys E) where
  Inv := Good E
  ok := fun _ r => RunOk E r
  step_inv := fun s o h => step_good E sound_full s o h
  log_prefix := fun s o => ran_prefix E full s o
  inv_ok := fun _ h r hr => h r hr

/-! ## Non-vacuity and necessity witnesses

Paths: 1 a system tool (read-only), 2 a writable `noexec` scratch dir, 3 a writable mount that is NOT `noexec`
(misconfiguration), 4 an interpreter (read-only), 5 an allowlisted script (read-only). Digest = content. Allowlisted
programs 10 (tool) and 20 (interpreter); allowlisted script 30. A path allowlist (the weaker design) lists 1, 2, 3, 4. -/

def E0 : Env where
  h := id
  writable := fun p => p = 2 ∨ p = 3
  noexecMount := fun p => p = 2
  allow := [10, 20]
  interp := [20]
  scripts := [30]
  pathAllow := [1, 2, 3, 4]
  admins := [9]

def s0 : St := ⟨[(1, 10), (4, 20), (5, 30)], [], false⟩

/-- **Non-vacuity**: the allowlisted tool runs, and the interpreter runs the allowlisted script. -/
theorem honest_execs : (run E0 full s0 [.exec 1 none, .exec 4 (some 5)]).ran = [(10, none), (20, some 30)] := by
  decide

/-- identity by PATH: replacing the content behind an allowlisted path runs it (no `noexec` check); identity by
digest refuses -/
theorem path_allowlist_toctou_breaks :
    (run E0 { full with byDigest := false, noexec := false } s0 [.write 2 666, .exec 2 none]).ran = [(666, none)] ∧
    (run E0 full s0 [.write 2 666, .exec 2 none]).ran = [] := by
  decide

/-- with a path allowlist, a writable mount that is not `noexec` is exploitable; the `noexec` scratch mount is not -/
theorem writable_exec_mount_breaks :
    (run E0 { full with byDigest := false } s0 [.write 3 666, .exec 3 none]).ran = [(666, none)] ∧
    (run E0 { full with byDigest := false } s0 [.write 2 666, .exec 2 none]).ran = [] ∧
    (run E0 full s0 [.write 3 666, .exec 3 none]).ran = [] := by
  decide

/-- an allowlisted interpreter runs an arbitrary script unless scripts are allowlisted too -/
theorem interpreter_loophole_breaks :
    (run E0 { full with scriptCheck := false } s0 [.write 2 777, .exec 4 (some 2)]).ran = [(20, some 777)] ∧
    (run E0 full s0 [.write 2 777, .exec 4 (some 2)]).ran = [] := by
  decide

/-- an allowlisted interpreter with no script (interactive / stdin) runs arbitrary code unless refused -/
theorem interpreter_repl_breaks :
    (run E0 { full with scriptCheck := false } s0 [.exec 4 none]).ran = [(20, none)] ∧
    (run E0 full s0 [.exec 4 none]).ran = [] := by
  decide

/-- without the halt check, execution continues after a halt -/
theorem no_halt_check_breaks :
    (run E0 { full with haltCheck := false } s0 [.halt 9, .exec 1 none]).ran = [(10, none)] ∧
    (run E0 full s0 [.halt 9, .exec 1 none]).ran = [] := by
  decide

end ControlStack.SC08

#print axioms ControlStack.SC08.safe_of_sound
#print axioms ControlStack.SC08.sc08_safe
#print axioms ControlStack.SC08.digest_design_needs_no_noexec
#print axioms ControlStack.SC08.halt_freezes
#print axioms ControlStack.SC08.spec
#print axioms ControlStack.SC08.honest_execs
#print axioms ControlStack.SC08.path_allowlist_toctou_breaks
#print axioms ControlStack.SC08.writable_exec_mount_breaks
#print axioms ControlStack.SC08.interpreter_loophole_breaks
#print axioms ControlStack.SC08.interpreter_repl_breaks
#print axioms ControlStack.SC08.no_halt_check_breaks
