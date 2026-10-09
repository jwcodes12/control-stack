/-
SC-10 / SC-11: policy and toolchain integrity.

Relation to `ControlStack/PolicyTamper.lean`: there, one active egress policy is preserved exactly when the attacker
has no write authority, and attacker write authority is a boolean premise (`policy_preserved_if_protected`,
`tamper_possible_if_writable`). Here write authority is an implemented check (`adminOnly`), and three further ways the
EFFECTIVE policy can diverge from the trusted one are modelled: a stale cached copy, an alternate evaluator reading an
agent-writable file, and a toolchain resolved through an agent-writable search path.

The model (family F1/F3 configuration integrity):
- a trusted configuration store keeps an append-only, versioned log of policy values (firewall policy, mount table,
  ...), each with its writer; only admins may write;
- every enforcement decision reads the CURRENT (latest) version from the store, not a cached copy (`fresh`), and
  there is a single evaluator (`singleEval`): no decision path reads the agent-writable policy file;
- builds use the toolchain at a pinned trusted location (`pinnedPath`), whose content has the pinned digest (premise);
- an absorbing admin HALT.

Main results (deployed configuration `full`; adversary class TRACE_ARBITRARY: any policy writes by any caller, cache
refreshes, decisions through either path, edits of the agent-writable file and search path, builds):
- `sc10_safe`: from `init`, every enforcement decision used the LATEST policy version at that moment (cut at the
  log length then), written by an admin, and every build used a toolchain with the pinned digest;
- `policy_admin_only`: every stored policy version was written by an admin;
- `halt_freezes`; `sys`/`spec` (client of `Core/Gate.lean`, effect log = decisions); non-vacuity
  `honest_enforcement_and_build`.

Necessity witnesses: `agent_writable_policy_breaks`, `stale_cache_breaks` (a tightened policy is not applied in the
window before a refresh), `alternate_evaluator_breaks`, `path_toolchain_breaks`, `no_halt_check_breaks`.

Premises outside the model: the store's access control and storage are trusted (no rollback), the store is the only
policy source of the deployed evaluator, the pinned location is not agent-writable and holds the pinned content, and
admin credentials are not held by agents. Not claimed: that admin-written policy is correct. No new mathematics.
-/
import Mathlib.Tactic
import ControlStack.Core.Gate

namespace ControlStack.SC10

open ControlStack.Gate

structure Env where
  admins : List ℕ
  h : ℕ → ℕ
  pinned : ℕ
  pinnedDigest : ℕ

/-- an enforcement decision: request, policy version used (none = not from the store), value used, store length then -/
structure Dec where
  req : ℕ
  ver : Option ℕ
  val : ℕ
  curLen : ℕ
deriving DecidableEq, Repr

structure St where
  /-- append-only policy log: (value, writer); the version is the index -/
  versions : List (ℕ × ℕ)
  cache : Option ℕ
  /-- an agent-writable policy file -/
  altFile : ℕ
  /-- the toolchain found through an agent-writable search path -/
  pathTool : ℕ
  decisions : List Dec
  builds : List ℕ
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | writePolicy (caller v : ℕ)
  | refresh
  | decide (req : ℕ)
  | writeAlt (v : ℕ)
  | altDecide (req : ℕ)
  | writePath (x : ℕ)
  | build
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  adminOnly : Bool
  fresh : Bool
  singleEval : Bool
  pinnedPath : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true, true⟩

def init : St := ⟨[], none, 0, 0, [], [], false⟩

def latest (s : St) : Option ℕ := if s.versions = [] then none else some (s.versions.length - 1)

def step (E : Env) (C : Checks) (s : St) : Op → St
  | .writePolicy c v =>
    if s.halted ∧ C.haltCheck then s
    else if C.adminOnly = true → c ∈ E.admins then { s with versions := s.versions ++ [(v, c)] } else s
  | .refresh => if s.halted ∧ C.haltCheck then s else { s with cache := latest s }
  | .decide req =>
    if s.halted ∧ C.haltCheck then s
    else match (if C.fresh then latest s else s.cache) with
      | none => s
      | some i =>
        match s.versions[i]? with
        | none => s
        | some vw => { s with decisions := s.decisions ++ [⟨req, some i, vw.1, s.versions.length⟩] }
  | .writeAlt v => if s.halted ∧ C.haltCheck then s else { s with altFile := v }
  | .altDecide req =>
    if s.halted ∧ C.haltCheck then s
    else if C.singleEval then s
    else { s with decisions := s.decisions ++ [⟨req, none, s.altFile, s.versions.length⟩] }
  | .writePath x => if s.halted ∧ C.haltCheck then s else { s with pathTool := x }
  | .build =>
    if s.halted ∧ C.haltCheck then s
    else { s with builds := s.builds ++ [if C.pinnedPath then E.pinned else s.pathTool] }
  | .halt c => if c ∈ E.admins then { s with halted := true } else s

def run (E : Env) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step E C) s

theorem run_cons (E : Env) (C : Checks) (s : St) (o : Op) (ops : List Op) :
    run E C s (o :: ops) = run E C (step E C s o) ops := rfl

/-! ## Invariant and safety -/

/-- a decision that used the latest stored version at that moment, written by an admin -/
def DecOk (E : Env) (s : St) (d : Dec) : Prop :=
  ∃ i w, d.ver = some i ∧ s.versions[i]? = some (d.val, w) ∧ w ∈ E.admins ∧ i + 1 = d.curLen

structure Good (E : Env) (s : St) : Prop where
  decs : ∀ d ∈ s.decisions, DecOk E s d
  builds : ∀ b ∈ s.builds, E.h b = E.pinnedDigest

structure Inv (E : Env) (s : St) : Prop where
  vers : ∀ pv ∈ s.versions, pv.2 ∈ E.admins
  decs : ∀ d ∈ s.decisions, DecOk E s d
  builds : ∀ b ∈ s.builds, E.h b = E.pinnedDigest

theorem inv_init (E : Env) : Inv E init := ⟨by simp [init], by simp [init], by simp [init]⟩

theorem DecOk.mono {E : Env} {s t : St} (hp : s.versions <+: t.versions) {d : Dec} (h : DecOk E s d) : DecOk E t d := by
  obtain ⟨i, w, h1, h2, h3, h4⟩ := h
  obtain ⟨u, hu⟩ := hp
  refine ⟨i, w, h1, ?_, h3, h4⟩
  have hi : i < s.versions.length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at h2
    simp at h2
  rw [← hu, List.getElem?_append_left hi]
  exact h2

/-- steps that change neither the policy log, the decisions nor the builds -/
theorem inv_same {E : Env} {s t : St} (h : Inv E s) (hv : t.versions = s.versions) (hd : t.decisions = s.decisions)
    (hb : t.builds = s.builds) : Inv E t :=
  ⟨hv ▸ h.vers, hd ▸ fun d hd' => DecOk.mono (hv ▸ List.prefix_refl _) (h.decs d hd'), hb ▸ h.builds⟩

theorem step_inv (E : Env) (hpin : E.h E.pinned = E.pinnedDigest) (s : St) (o : Op) (h : Inv E s) :
    Inv E (step E full s o) := by
  cases o with
  | writePolicy c v =>
    simp only [step, show full.adminOnly = true from rfl, true_implies]
    split_ifs with h1 h2
    · exact h
    · refine ⟨fun pv hpv => ?_, fun d hd => DecOk.mono (List.prefix_append _ _) (h.decs d hd), h.builds⟩
      rcases List.mem_append.1 hpv with hpv | hpv
      · exact h.vers pv hpv
      · simp at hpv; subst hpv; exact h2
    · exact h
  | decide req =>
    simp only [step, show full.fresh = true from rfl, ite_true]
    split_ifs with h1
    · exact h
    · cases hl : latest s with
      | none => exact h
      | some i =>
        dsimp only
        cases hv : s.versions[i]? with
        | none => exact h
        | some vw =>
          dsimp only
          refine ⟨h.vers, fun d hd => ?_, h.builds⟩
          rcases List.mem_append.1 hd with hd | hd
          · exact h.decs d hd
          · simp at hd; subst hd
            have hne : s.versions ≠ [] := by
              intro he; simp [latest, he] at hl
            have hi : i = s.versions.length - 1 := by simp [latest, hne] at hl; omega
            have hpos : 0 < s.versions.length := List.length_pos_of_ne_nil hne
            refine ⟨i, vw.2, rfl, by rw [hv], h.vers vw (List.mem_of_getElem? hv), by show i + 1 = s.versions.length; omega⟩
  | altDecide req =>
    simp only [step, show full.singleEval = true from rfl, ite_true]
    split_ifs <;> exact h
  | build =>
    simp only [step, show full.pinnedPath = true from rfl, ite_true]
    split_ifs
    · exact h
    · refine ⟨h.vers, h.decs, fun b hb => ?_⟩
      rcases List.mem_append.1 hb with hb | hb
      · exact h.builds b hb
      · simp at hb; subst hb; exact hpin
  | refresh => simp only [step]; split_ifs <;> first | exact h | exact inv_same h rfl rfl rfl
  | writeAlt v => simp only [step]; split_ifs <;> first | exact h | exact inv_same h rfl rfl rfl
  | writePath x => simp only [step]; split_ifs <;> first | exact h | exact inv_same h rfl rfl rfl
  | halt c => simp only [step]; split_ifs <;> first | exact h | exact inv_same h rfl rfl rfl

theorem run_inv (E : Env) (hpin : E.h E.pinned = E.pinnedDigest) (s : St) (ops : List Op) (h : Inv E s) :
    Inv E (run E full s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => rw [run_cons]; exact ih _ (step_inv E hpin s o h)

/-- **SC-10/SC-11 safety.** After any trace from `init`, every enforcement decision used the latest policy version at
that moment, written by an admin, and every build used a toolchain with the pinned digest (premise: the pinned
location holds the pinned content). Adversary: TRACE_ARBITRARY. -/
theorem sc10_safe (E : Env) (hpin : E.h E.pinned = E.pinnedDigest) (ops : List Op) : Good E (run E full init ops) :=
  let h := run_inv E hpin init ops (inv_init E)
  ⟨h.decs, h.builds⟩

/-- **Admin-only policy**: every stored version was written by an admin. -/
theorem policy_admin_only (E : Env) (hpin : E.h E.pinned = E.pinnedDigest) (ops : List Op) :
    ∀ pv ∈ (run E full init ops).versions, pv.2 ∈ E.admins :=
  (run_inv E hpin init ops (inv_init E)).vers

/-! ## Halt -/

theorem step_halted (E : Env) (s : St) (o : Op) (hh : s.halted = true) : step E full s o = s := by
  cases o with
  | halt c =>
    simp only [step]
    split_ifs
    · cases s; simp_all
    · rfl
  | _ => simp [step, full, hh]

/-- **Halt freezes**: once halted, no trace changes the state. -/
theorem halt_freezes (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s := by
  induction ops with
  | nil => rfl
  | cons o ops ih => rw [run_cons, step_halted E s o hh, ih]

/-! ## Client of the shared gate interface -/

theorem decisions_prefix (E : Env) (C : Checks) (s : St) (o : Op) : s.decisions <+: (step E C s o).decisions := by
  cases o with
  | decide req =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals first | exact List.prefix_refl _ | exact List.prefix_append _ _
  | altDecide req =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals first | exact List.prefix_refl _ | exact List.prefix_append _ _
  | _ =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals exact List.prefix_refl _

def sys (E : Env) : System St Op Dec where
  step := step E full
  effects := St.decisions

def spec (E : Env) (hpin : E.h E.pinned = E.pinnedDigest) : Spec (sys E) where
  Inv := Inv E
  ok := DecOk E
  step_inv := fun s o h => step_inv E hpin s o h
  log_prefix := fun s o => decisions_prefix E full s o
  inv_ok := fun _ h d hd => h.decs d hd

/-! ## Non-vacuity and necessity witnesses

Admin 9, agent 1; digest = content; pinned toolchain content 40 with digest 40. -/

def E0 : Env := ⟨[9], id, 40, 40⟩

/-- **Non-vacuity**: an admin policy is enforced and a build uses the pinned toolchain. -/
theorem honest_enforcement_and_build :
    let s := run E0 full init [.writePolicy 9 5, .decide 1, .build]
    s.decisions = [⟨1, some 0, 5, 1⟩] ∧ s.builds = [40] := by
  decide

/-- an agent-writable policy store: the agent's own policy is enforced -/
theorem agent_writable_policy_breaks :
    let s := run E0 { full with adminOnly := false } init [.writePolicy 1 0, .decide 1]
    s.decisions = [⟨1, some 0, 0, 1⟩] ∧ s.versions = [(0, 1)] ∧
    (run E0 full init [.writePolicy 1 0, .decide 1]).decisions = [] := by
  decide

/-- a stale cached copy: after a tightening (version 1), decisions still use version 0 until a refresh -/
theorem stale_cache_breaks :
    (run E0 { full with fresh := false } init [.writePolicy 9 5, .refresh, .writePolicy 9 6, .decide 1]).decisions =
      [⟨1, some 0, 5, 2⟩] ∧
    (run E0 full init [.writePolicy 9 5, .refresh, .writePolicy 9 6, .decide 1]).decisions = [⟨1, some 1, 6, 2⟩] := by
  decide

/-- an alternate evaluator reading the agent-writable file decides by the agent's policy -/
theorem alternate_evaluator_breaks :
    (run E0 { full with singleEval := false } init [.writePolicy 9 5, .writeAlt 0, .altDecide 1]).decisions =
      [⟨1, none, 0, 1⟩] ∧
    (run E0 full init [.writePolicy 9 5, .writeAlt 0, .altDecide 1]).decisions = [] := by
  decide

/-- a toolchain resolved through an agent-writable search path builds with the agent's toolchain -/
theorem path_toolchain_breaks :
    (run E0 { full with pinnedPath := false } init [.writePath 666, .build]).builds = [666] ∧
    (run E0 full init [.writePath 666, .build]).builds = [40] := by
  decide

/-- without the halt check, enforcement and builds continue after a halt -/
theorem no_halt_check_breaks :
    (run E0 { full with haltCheck := false } init [.writePolicy 9 5, .halt 9, .build]).builds = [40] ∧
    (run E0 full init [.writePolicy 9 5, .halt 9, .build]).builds = [] := by
  decide

end ControlStack.SC10

#print axioms ControlStack.SC10.sc10_safe
#print axioms ControlStack.SC10.policy_admin_only
#print axioms ControlStack.SC10.halt_freezes
#print axioms ControlStack.SC10.spec
#print axioms ControlStack.SC10.honest_enforcement_and_build
#print axioms ControlStack.SC10.agent_writable_policy_breaks
#print axioms ControlStack.SC10.stale_cache_breaks
#print axioms ControlStack.SC10.alternate_evaluator_breaks
#print axioms ControlStack.SC10.path_toolchain_breaks
#print axioms ControlStack.SC10.no_halt_check_breaks
