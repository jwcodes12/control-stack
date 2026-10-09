/-
SC-21 (eval corruption / selective suppression of failures) and SC-22 (misreported research findings).

Both scenarios share one shape: an untrusted agent reports results; the question is whether wrong or suppressed results
reach a published record. What CAN be stated formally:

1. A process model (`St`/`step`): a frozen task list and a frozen evaluator digest; an APPEND-ONLY results log (a
   task's result cannot be overwritten once reported); an independent executor re-executes sampled tasks under the frozen
   evaluator and flags any mismatch; publication requires completeness (every task has a result), the frozen evaluator
   digest on every result, and no flags.
   `sc21_safe`: every published record covers every task, used only the frozen evaluator, and every task re-executed
   before publication carries its true result. Witnesses: `suppression_breaks` (no completeness check: a failing task
   is simply omitted), `modified_evaluator_breaks`, `overwrite_after_check_breaks` (no append-only log: the result is
   changed after it passed re-execution).
2. A sampling bound (reusing `AuditBudget`): with deterministic re-execution, corruption of a set A of k results goes
   undetected exactly when the re-executed sample misses A (`undetected_iff_disjoint`); for a uniformly random hidden
   sample of B of N tasks this has probability C(N−k,B)/C(N,B) ≤ ((N−B)/N)^k (`sc21_undetected_prob`,
   `sc21_undetected_le_pow`; N=100, B=10, k=5 gives ≈ 0.584, `sc21_example`). If the sample is observable in advance,
   an agent corrupts only unsampled results and survives with probability 1 (`observable_sample_nogo`).
   SC-22 is the same bound for independent replication of B of N reported findings (`sc22_unreplicated_misreport`).

Adversary classes: the process theorems are TRACE_ARBITRARY; the sampling bound is NON_ADAPTIVE in the corrupted set
(the agent fixes which results to corrupt without seeing the sample; the adaptive-with-feedback version needs the
leakage machinery of `Leakage.audit_leak_bound` / `Families/F6/ReservedAudit.lean`).

What remains semantic: whether the frozen evaluator and task set measure what they should (SC-21), and whether a
numerically reproducible finding is correctly INTERPRETED (SC-22: "semantic truthfulness still needs independent
experts or empirical checks"). Premises: re-execution is deterministic (or its nondeterminism is within a declared
tolerance); the executor and publisher are independent of the agent. No new mathematics.
-/
import Mathlib.Tactic
import ControlStack.Core.Gate
import ControlStack.AuditBudget

namespace ControlStack.EvalIntegrity

open ControlStack.Gate ControlStack.AuditBudget Finset

/-! ## Process model -/

structure Env where
  tasks : List ℕ
  truth : ℕ → ℕ
  frozen : ℕ
  admins : List ℕ

/-- a reported result: (task, value, evaluator digest) -/
abbrev Res := ℕ × ℕ × ℕ

structure St where
  /-- newest first -/
  results : List Res
  reexecuted : List ℕ
  flags : List ℕ
  /-- published records: (results snapshot, tasks re-executed by then) -/
  published : List (List Res × List ℕ)
  halted : Bool
deriving DecidableEq, Repr

inductive Op where
  | report (t r d : ℕ)
  | reexec (t : ℕ)
  | publish
  | halt (caller : ℕ)
deriving DecidableEq, Repr

structure Checks where
  appendOnly : Bool
  complete : Bool
  frozenEval : Bool
  haltCheck : Bool
deriving DecidableEq, Repr

def full : Checks := ⟨true, true, true, true⟩

def init : St := ⟨[], [], [], [], false⟩

def resultOf (s : St) (t : ℕ) : Option Res := s.results.find? (fun e => e.1 = t)

def step (E : Env) (C : Checks) (s : St) : Op → St
  | .report t r d =>
    if s.halted ∧ C.haltCheck then s
    else if C.appendOnly = true → resultOf s t = none then { s with results := (t, r, d) :: s.results } else s
  | .reexec t =>
    if s.halted ∧ C.haltCheck then s
    else match resultOf s t with
      | none => s
      | some e =>
        { s with reexecuted := s.reexecuted ++ [t],
                 flags := if e.2.1 = E.truth t then s.flags else s.flags ++ [t] }
  | .publish =>
    if s.halted ∧ C.haltCheck then s
    else if (C.complete = true → ∀ t ∈ E.tasks, resultOf s t ≠ none) ∧
        (C.frozenEval = true → ∀ e ∈ s.results, e.2.2 = E.frozen) ∧ s.flags = [] then
      { s with published := s.published ++ [(s.results, s.reexecuted)] }
    else s
  | .halt c => if c ∈ E.admins then { s with halted := true } else s

def run (E : Env) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step E C) s

theorem run_cons (E : Env) (C : Checks) (s : St) (o : Op) (ops : List Op) :
    run E C s (o :: ops) = run E C (step E C s o) ops := rfl

/-- a published record: complete, frozen evaluator only, and true values for every re-executed task -/
def PubOk (E : Env) (p : List Res × List ℕ) : Prop :=
  (∀ t ∈ E.tasks, ∃ e ∈ p.1, e.1 = t) ∧ (∀ e ∈ p.1, e.2.2 = E.frozen) ∧
    (∀ e ∈ p.1, e.1 ∈ p.2 → e.2.1 = E.truth e.1)

structure Inv (E : Env) (s : St) : Prop where
  nodup : (s.results.map Prod.fst).Nodup
  checked : ∀ t ∈ s.reexecuted, t ∈ s.flags ∨ ∀ e ∈ s.results, e.1 = t → e.2.1 = E.truth t
  rx_has : ∀ t ∈ s.reexecuted, ∃ e ∈ s.results, e.1 = t
  pub : ∀ p ∈ s.published, PubOk E p

theorem inv_init (E : Env) : Inv E init := ⟨by simp [init], by simp [init], by simp [init], by simp [init]⟩

theorem resultOf_none {s : St} {t : ℕ} (h : resultOf s t = none) : ∀ e ∈ s.results, e.1 ≠ t := by
  intro e he het
  have := List.find?_eq_none.1 h e he
  simp [het] at this

theorem resultOf_some {s : St} {t : ℕ} (h : (s.results.map Prod.fst).Nodup) {e : Res} (he : e ∈ s.results)
    (ht : e.1 = t) : resultOf s t = some e := by
  cases hr : resultOf s t with
  | none => exact absurd ht (resultOf_none hr e he)
  | some e' =>
    have hm := List.mem_of_find?_eq_some hr
    have ht' : e'.1 = t := by simpa using List.find?_some hr
    have : e = e' := List.inj_on_of_nodup_map h he hm (by rw [ht, ht'])
    rw [this]

theorem step_inv (E : Env) (s : St) (o : Op) (h : Inv E s) : Inv E (step E full s o) := by
  cases o with
  | report t r d =>
    simp only [step, show full.appendOnly = true from rfl, true_implies]
    split_ifs with h1 h2
    · exact h
    · refine ⟨?_, fun x hx => ?_, fun x hx => ?_, h.pub⟩
      · simp only [List.map_cons, List.nodup_cons]
        exact ⟨fun hm => by
          obtain ⟨e, he, het⟩ := List.mem_map.1 hm
          exact resultOf_none h2 e he het, h.nodup⟩
      · rcases h.checked x hx with hf | hc
        · exact Or.inl hf
        · refine Or.inr fun e he hex => ?_
          simp only [List.mem_cons] at he
          rcases he with rfl | he
          · -- a task that was re-executed already had a result, so the new report is for a fresh task
            exfalso
            simp only at hex
            subst hex
            obtain ⟨e, he, het⟩ := h.rx_has _ hx
            exact resultOf_none h2 e he het
          · exact hc e he hex
      · obtain ⟨e, he, het⟩ := h.rx_has x hx
        exact ⟨e, List.mem_cons_of_mem _ he, het⟩
    · exact h
  | reexec t =>
    simp only [step]
    split_ifs
    · exact h
    · cases hr : resultOf s t with
      | none => exact h
      | some e =>
        dsimp only
        have hm := List.mem_of_find?_eq_some hr
        have ht : e.1 = t := by simpa using List.find?_some hr
        refine ⟨h.nodup, fun x hx => ?_, fun x hx => ?_, h.pub⟩
        swap
        · rcases List.mem_append.1 hx with hx | hx
          · exact h.rx_has x hx
          · simp at hx; subst hx; exact ⟨e, hm, ht⟩
        rcases List.mem_append.1 hx with hx | hx
        · rcases h.checked x hx with hf | hc
          · left; split_ifs <;> simp [hf]
          · exact Or.inr hc
        · simp at hx; subst hx
          split_ifs with heq
          · right
            intro e' he' het
            have : e' = e := by
              have h1 := resultOf_some h.nodup he' het
              rw [hr] at h1; exact (Option.some.inj h1).symm
            rw [this]; exact heq
          · left; simp
  | publish =>
    simp only [step]
    split_ifs with h1 h2
    · exact h
    · obtain ⟨hc, hf, hfl⟩ := h2
      simp only [full, true_implies] at hc hf
      refine ⟨h.nodup, h.checked, h.rx_has, fun p hp => ?_⟩
      rcases List.mem_append.1 hp with hp | hp
      · exact h.pub p hp
      · simp at hp; subst hp
        refine ⟨fun t ht => ?_, hf, fun e he hx => ?_⟩
        · cases hr : resultOf s t with
          | none => exact absurd hr (hc t ht)
          | some e => exact ⟨e, List.mem_of_find?_eq_some hr, by simpa using List.find?_some hr⟩
        · rcases h.checked e.1 hx with hfl' | hcc
          · rw [hfl] at hfl'; simp at hfl'
          · exact hcc e he rfl
    · exact h
  | halt c =>
    simp only [step]
    split_ifs
    · exact ⟨h.nodup, h.checked, h.rx_has, h.pub⟩
    · exact h

theorem run_inv (E : Env) (s : St) (ops : List Op) (h : Inv E s) : Inv E (run E full s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => rw [run_cons]; exact ih _ (step_inv E s o h)

/-- **SC-21 process safety.** After any trace from `init`, every published record covers every frozen task, used only
the frozen evaluator, and every task re-executed before publication carries its true result. Adversary:
TRACE_ARBITRARY (any reports, re-execution choices, publication attempts). -/
theorem sc21_safe (E : Env) (ops : List Op) : ∀ p ∈ (run E full init ops).published, PubOk E p :=
  (run_inv E init ops (inv_init E)).pub

theorem step_halted (E : Env) (s : St) (o : Op) (hh : s.halted = true) : step E full s o = s := by
  cases o with
  | halt c =>
    simp only [step]
    split_ifs
    · cases s; simp_all
    · rfl
  | _ => simp [step, full, hh]

/-- **Halt freezes publication**: once halted, no trace changes the state. -/
theorem halt_freezes (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s := by
  induction ops with
  | nil => rfl
  | cons o ops ih => rw [run_cons, step_halted E s o hh, ih]

theorem published_prefix (E : Env) (C : Checks) (s : St) (o : Op) : s.published <+: (step E C s o).published := by
  cases o with
  | publish =>
    simp only [step]
    split_ifs
    · exact List.prefix_refl _
    · exact List.prefix_append _ _
    · exact List.prefix_refl _
  | _ =>
    simp only [step]
    repeat' (first | split | split_ifs)
    all_goals exact List.prefix_refl _

def sys (E : Env) : System St Op (List Res × List ℕ) where
  step := step E full
  effects := St.published

def spec (E : Env) : Spec (sys E) where
  Inv := Inv E
  ok := fun _ p => PubOk E p
  step_inv := fun s o h => step_inv E s o h
  log_prefix := fun s o => published_prefix E full s o
  inv_ok := fun _ h p hp => h.pub p hp

/-! ### Witnesses. Tasks 0 (true result 1, a pass) and 1 (true result 0, a failure); frozen evaluator 5; admin 9. -/

def E0 : Env := ⟨[0, 1], fun t => if t = 1 then 0 else 1, 5, [9]⟩

/-- **Non-vacuity**: complete, frozen, re-executed results are published. -/
theorem honest_publish :
    (run E0 full init [.report 0 1 5, .report 1 0 5, .reexec 1, .publish]).published = [([(1, 0, 5), (0, 1, 5)], [1])] := by
  decide

/-- without the completeness check, the failing task is silently omitted -/
theorem suppression_breaks :
    (run E0 { full with complete := false } init [.report 0 1 5, .publish]).published = [([(0, 1, 5)], [])] ∧
    (run E0 full init [.report 0 1 5, .publish]).published = [] := by
  decide

/-- without the frozen-evaluator check, results from a modified evaluator (digest 6) are published -/
theorem modified_evaluator_breaks :
    (run E0 { full with frozenEval := false } init [.report 0 1 6, .report 1 0 6, .publish]).published =
      [([(1, 0, 6), (0, 1, 6)], [])] ∧
    (run E0 full init [.report 0 1 6, .report 1 0 6, .publish]).published = [] := by
  decide

/-- without an append-only log, a result that passed re-execution is overwritten (the failure becomes a pass) -/
theorem overwrite_after_check_breaks :
    (run E0 { full with appendOnly := false } init
      [.report 1 0 5, .report 0 1 5, .reexec 1, .report 1 1 5, .publish]).published =
      [([(1, 1, 5), (0, 1, 5), (1, 0, 5)], [1])] ∧
    (run E0 full init [.report 1 0 5, .report 0 1 5, .reexec 1, .report 1 1 5, .publish]).published =
      [([(0, 1, 5), (1, 0, 5)], [1])] := by
  decide

/-! ## Sampled independent re-execution -/

variable {N : ℕ}

/-- the corrupted results: reported value differs from the true (re-executed) value -/
def corrupt (rep truth : Fin N → ℕ) : Finset (Fin N) := univ.filter (fun i => rep i ≠ truth i)

/-- deterministic re-execution of sample `S` flags nothing exactly when `S` misses every corrupted result -/
theorem undetected_iff_disjoint (rep truth : Fin N → ℕ) (S : Finset (Fin N)) :
    S.filter (fun i => rep i ≠ truth i) = ∅ ↔ Disjoint S (corrupt rep truth) := by
  simp [corrupt, Finset.filter_eq_empty_iff, Finset.disjoint_left]

/-- the probability that a uniformly random hidden sample of size `B` flags nothing is `survival` -/
theorem survival_is_unflagged_fraction (rep truth : Fin N → ℕ) (B : ℕ) :
    survival (randomSchedules N B) (corrupt rep truth) =
      (((randomSchedules N B).filter (fun S => S.filter (fun i => rep i ≠ truth i) = ∅)).card : ℝ) /
        ((randomSchedules N B).card : ℝ) := by
  unfold survival
  congr 3
  exact Finset.filter_congr (fun S _ => (undetected_iff_disjoint rep truth S).symm)

/-- **SC-21 sampling bound.** Corrupting `k` of `N` results goes undetected by a uniformly random hidden re-execution
sample of size `B` with probability exactly C(N−k,B)/C(N,B). Adversary: NON_ADAPTIVE corrupted set. -/
theorem sc21_undetected_prob (rep truth : Fin N → ℕ) {B k : ℕ} (hk : (corrupt rep truth).card = k) :
    survival (randomSchedules N B) (corrupt rep truth) = (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) :=
  (random_subset_survival (B := B) _ hk).2

theorem sc21_undetected_le_pow (rep truth : Fin N → ℕ) {B k : ℕ} (hN : 0 < N) (hB : B ≤ N)
    (hk : (corrupt rep truth).card = k) :
    survival (randomSchedules N B) (corrupt rep truth) ≤ (((N : ℝ) - B) / N) ^ k :=
  random_survival_le_pow hN (hk ▸ by simpa using Finset.card_le_univ (corrupt rep truth)) hB _ hk

/-- N = 100 results, B = 10 re-executed, 5 corrupted: undetected with probability ≈ 0.584 ≤ 0.59049 -/
theorem sc21_example (rep truth : Fin 100 → ℕ) (hk : (corrupt rep truth).card = 5) :
    survival (randomSchedules 100 10) (corrupt rep truth) ≤ 0.59049 :=
  (budget_example _ hk).2.1

/-- **Observable sample no-go**: if the agent knows the sample in advance, it corrupts only unsampled results and
survives with probability 1. -/
theorem observable_sample_nogo {B k : ℕ} (S : Finset (Fin N)) (hS : S.card = B) (hk : k ≤ N - B) :
    ∃ A : Finset (Fin N), A.card = k ∧ Disjoint S A ∧ survival {S} A = 1 :=
  observable_schedule_nogo S hS hk

/-- **SC-22 replication bound.** Misreporting `k` of `N` findings survives independent replication of a uniformly
random hidden `B` of them with probability exactly C(N−k,B)/C(N,B) (replication checks numerical reproducibility under
the frozen pipeline, not interpretation). -/
theorem sc22_unreplicated_misreport (rep truth : Fin N → ℕ) {B k : ℕ} (hk : (corrupt rep truth).card = k) :
    survival (randomSchedules N B) (corrupt rep truth) = (Nat.choose (N - k) B : ℝ) / (Nat.choose N B : ℝ) :=
  sc21_undetected_prob rep truth hk

end ControlStack.EvalIntegrity

#print axioms ControlStack.EvalIntegrity.sc21_safe
#print axioms ControlStack.EvalIntegrity.halt_freezes
#print axioms ControlStack.EvalIntegrity.spec
#print axioms ControlStack.EvalIntegrity.honest_publish
#print axioms ControlStack.EvalIntegrity.suppression_breaks
#print axioms ControlStack.EvalIntegrity.modified_evaluator_breaks
#print axioms ControlStack.EvalIntegrity.overwrite_after_check_breaks
#print axioms ControlStack.EvalIntegrity.undetected_iff_disjoint
#print axioms ControlStack.EvalIntegrity.survival_is_unflagged_fraction
#print axioms ControlStack.EvalIntegrity.sc21_undetected_prob
#print axioms ControlStack.EvalIntegrity.sc21_undetected_le_pow
#print axioms ControlStack.EvalIntegrity.sc21_example
#print axioms ControlStack.EvalIntegrity.observable_sample_nogo
#print axioms ControlStack.EvalIntegrity.sc22_unreplicated_misreport
