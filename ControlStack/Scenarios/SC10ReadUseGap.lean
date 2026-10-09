/-
SC-10 time-of-check/use negative witness (2026-10-09).

The existing SC10Policy.sc10_safe theorem models a decision that reads and
uses the latest policy in ONE atomic step. The reference PEP in
scenarios/SC-10/harness/pep.py makes a separate RPC to the store and then
computes/logs a decision. In between those operations an admin can write
another policy. The old `t_answer` receipt timestamps the store read, not
necessarily the eventual effect.

This deliberately weakened event machine exposes the interval. It does NOT
claim that such a race happened in any preserved preregistered run, and a
commit during the timestamp interval alone is not proof of a stale decision.
-/
import ControlStack.Scenarios.SC10Policy

namespace ControlStack.SC10ReadUseGap

/-- The single-threaded policy store and a deferred evaluator, with a
pending read-version which may become stale. -/
structure State where
  versions : List (ℕ × ℕ)
  pending : Option ℕ
  applied : List SC10.Dec
deriving DecidableEq, Repr

inductive Event where
  | commit (caller policy : ℕ)
  | readLatest
  | apply (request : ℕ)
deriving DecidableEq, Repr

def init : State := ⟨[], none, []⟩

def current (s : State) : Option ℕ :=
  if s.versions = [] then none else some (s.versions.length - 1)

def step (admins : List ℕ) (s : State) : Event → State
  | .commit c p =>
      if c ∈ admins then { s with versions := s.versions ++ [(p, c)] } else s
  | .readLatest => { s with pending := current s }
  | .apply req =>
      match s.pending with
      | none => s
      | some i =>
          match s.versions[i]? with
          | none => s
          | some pv =>
              { s with applied := s.applied ++ [⟨req, some i, pv.1, s.versions.length⟩],
                       pending := none }

def run (admins : List ℕ) (es : List Event) : State :=
  es.foldl (step admins) init

/-- With a policy update between reading and using, the resulting receipt
names version 0 even though version 1 is current at the use point. -/
theorem intervening_commit_stales_decision :
    let s := run [9] [.commit 9 5, .readLatest, .commit 9 6, .apply 1]
    s.versions = [(5, 9), (6, 9)] ∧
      s.applied = [⟨1, some 0, 5, 2⟩] ∧
      (s.applied.head?).map SC10.Dec.ver = some (some 0) ∧
      current s = some 1 := by
  decide

/-- Without the intervening update, this particular deferred read agrees
with the atomic abstract decision. -/
theorem no_intervening_commit_matches :
    (run [9] [.commit 9 5, .readLatest, .apply 1]).applied =
      (SC10.run SC10.E0 SC10.full SC10.init
        [.writePolicy 9 5, .decide 1]).decisions := by
  decide

/-- Under the SC-10 abstract full checks, the same update sequence uses the
new policy. This identifies the atomicity premise behind sc10_safe. -/
theorem atomic_decision_uses_latest :
    (SC10.run SC10.E0 SC10.full SC10.init
        [.writePolicy 9 5, .writePolicy 9 6, .decide 1]).decisions =
      [⟨1, some 1, 6, 2⟩] := by
  decide

end ControlStack.SC10ReadUseGap

#print axioms ControlStack.SC10ReadUseGap.intervening_commit_stales_decision
#print axioms ControlStack.SC10ReadUseGap.no_intervening_commit_matches
#print axioms ControlStack.SC10ReadUseGap.atomic_decision_uses_latest
