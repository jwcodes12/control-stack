/-
F2 for multi-tenant accelerators: memory RESIDUE between tenants (STACK-MAP `gpu_multitenancy`, premise
`memory_scrub_between_tenants`).

An abstract allocator for device memory pages. Each page cell has a value and a ghost WRITER tag (the tenant whose
write produced the value; `none` for scrubbed or never-written memory). Tenants allocate free pages, write and read
only pages currently allocated to them, and free them. Scrub policies, as implementation checks:
- `scrubOnAlloc`: a page is zeroed when it is handed out, except that `fastSkip` skips the scrub on a fast path
  (allocations smaller than `small`), a shape seen in real allocators;
- `scrubOnFree`: a page is zeroed when it is freed (so free pages are always clean).

Results (adversary class TRACE_ARBITRARY: any allocation, free, write and read sequence by any tenants):
- `residue_safe`: for every SOUND policy (scrub on every allocation, or scrub on free), every read returns either
  scrubbed memory or a value the reading tenant wrote itself;
- `noninterference`: tenant B's reads are identical in two runs that differ only in the VALUES tenant A wrote, so
  A's writes are invisible to B;
- witnesses: `no_scrub_residue` (B reads A's residue), `fast_path_skip_residue` (scrub skipped for small
  allocations), `scrub_on_alloc_clean`, `scrub_on_free_clean`.
- Time-slicing (`Slice`): a per-context local memory (field `scratch`) shared across context switches. `Slice.slice_safe`: if the
  local memory is cleared on every switch, a context reads only its own writes or zeros. `Slice.no_clear_leaks`: not
  cleared, the next tenant's context reads the previous tenant's value.

This is the generic shape of publicly documented GPU local-memory residue classes (e.g. LeftoverLocals, 2024),
described generically; no specific exploit is modelled.

Limits: this models the POLICY layer (allocator and context switch), not hardware or firmware correctness. Whether a
real driver scrubs, on which paths, and whether caches, TLBs or registers retain data is a measurement question
(`prereg/GPU1-RESIDUE-CONTENTION-DRAFT.md`). Timing and contention channels are `F2/ChannelInstances.gpu_bound`, not
this file. No new mathematics.
-/
import Mathlib.Tactic

namespace ControlStack.GPUResidue

structure Cell where
  val : ℕ
  writer : Option ℕ
deriving DecidableEq, Repr

def clean : Cell := ⟨0, none⟩

/-- a read: tenant, page, value returned, ghost writer of that value -/
structure Read where
  tenant : ℕ
  page : ℕ
  val : ℕ
  writer : Option ℕ
deriving DecidableEq, Repr

structure St where
  /-- page ↦ owner (newest first; `none` = free) -/
  owner : List (ℕ × Option ℕ)
  /-- page ↦ cell (newest first) -/
  mem : List (ℕ × Cell)
  reads : List Read
deriving DecidableEq, Repr

inductive Op where
  | alloc (t p size : ℕ)
  | free (t p : ℕ)
  | write (t p v : ℕ)
  | read (t p : ℕ)
deriving DecidableEq, Repr

structure Checks where
  scrubOnAlloc : Bool
  scrubOnFree : Bool
  fastSkip : Bool
deriving DecidableEq, Repr

/-- the deployed policy: scrub every allocation -/
def full : Checks := ⟨true, false, false⟩

/-- policies that prevent residue -/
def Sound (C : Checks) : Prop := (C.scrubOnAlloc = true ∧ C.fastSkip = false) ∨ C.scrubOnFree = true

def init : St := ⟨[], [], []⟩

def ownerOf (s : St) (p : ℕ) : Option ℕ := ((s.owner.find? (fun e => e.1 = p)).map Prod.snd).getD none

def cellOf (s : St) (p : ℕ) : Cell := ((s.mem.find? (fun e => e.1 = p)).map Prod.snd).getD clean

def step (small : ℕ) (C : Checks) (s : St) : Op → St
  | .alloc t p size =>
    if ownerOf s p = none then
      { s with owner := (p, some t) :: s.owner,
               mem := if C.scrubOnAlloc ∧ ¬ (C.fastSkip ∧ size < small) then (p, clean) :: s.mem else s.mem }
    else s
  | .free t p =>
    if ownerOf s p = some t then
      { s with owner := (p, none) :: s.owner, mem := if C.scrubOnFree then (p, clean) :: s.mem else s.mem }
    else s
  | .write t p v => if ownerOf s p = some t then { s with mem := (p, ⟨v, some t⟩) :: s.mem } else s
  | .read t p =>
    if ownerOf s p = some t then { s with reads := s.reads ++ [⟨t, p, (cellOf s p).val, (cellOf s p).writer⟩] }
    else s

def run (small : ℕ) (C : Checks) (s : St) (ops : List Op) : St := ops.foldl (step small C) s

theorem run_cons (small : ℕ) (C : Checks) (s : St) (o : Op) (ops : List Op) :
    run small C s (o :: ops) = run small C (step small C s o) ops := rfl

theorem ownerOf_cons {s t : St} {p : ℕ} {x : Option ℕ} (ht : t.owner = (p, x) :: s.owner) (q : ℕ) :
    ownerOf t q = if p = q then x else ownerOf s q := by
  unfold ownerOf; rw [ht]
  by_cases h : p = q <;> simp [h]

theorem cellOf_cons {s t : St} {p : ℕ} {c : Cell} (ht : t.mem = (p, c) :: s.mem) (q : ℕ) :
    cellOf t q = if p = q then c else cellOf s q := by
  unfold cellOf; rw [ht]
  by_cases h : p = q <;> simp [h]

@[simp] theorem cellOf_owner (s : St) (o : List (ℕ × Option ℕ)) (q : ℕ) : cellOf { s with owner := o } q = cellOf s q :=
  rfl

@[simp] theorem ownerOf_mem (s : St) (m : List (ℕ × Cell)) (q : ℕ) : ownerOf { s with mem := m } q = ownerOf s q := rfl

/-! ## Safety for sound policies -/

/-- a read returns scrubbed memory or the reader's own write -/
def ReadOk (r : Read) : Prop := r.writer = none ∨ r.writer = some r.tenant

structure Inv (C : Checks) (s : St) : Prop where
  owned : ∀ p t, ownerOf s p = some t → (cellOf s p).writer = none ∨ (cellOf s p).writer = some t
  freeClean : C.scrubOnFree = true → ∀ p, ownerOf s p = none → (cellOf s p).writer = none
  reads : ∀ r ∈ s.reads, ReadOk r

theorem inv_init (C : Checks) : Inv C init :=
  ⟨fun p t h => by simp [ownerOf, init] at h, fun _ p _ => by simp [cellOf, init, clean], by simp [init]⟩

theorem step_inv (small : ℕ) (C : Checks) (hC : Sound C) (s : St) (o : Op) (h : Inv C s) :
    Inv C (step small C s o) := by
  cases o with
  | alloc t p size =>
    simp only [step]
    by_cases hfree : ownerOf s p = none
    · rw [ite_eq_left hfree]
      by_cases hs : C.scrubOnAlloc = true ∧ ¬ (C.fastSkip = true ∧ size < small)
      · rw [ite_eq_left hs]
        refine ⟨fun q u hq => ?_, fun hf q hq => ?_, h.reads⟩
        · rw [ownerOf_cons (s := s) rfl] at hq
          rw [cellOf_cons (s := s) rfl]
          by_cases hpq : p = q
          · simp [hpq, clean]
          · rw [ite_eq_right hpq] at hq ⊢; exact h.owned q u hq
        · rw [ownerOf_cons (s := s) rfl] at hq
          rw [cellOf_cons (s := s) rfl]
          by_cases hpq : p = q
          · simp [hpq, clean]
          · rw [ite_eq_right hpq] at hq ⊢; exact h.freeClean hf q hq
      · rw [ite_eq_right hs]
        have hfr : C.scrubOnFree = true := by
          rcases hC with ⟨h1, h2⟩ | h1
          · exfalso; apply hs; simp [h1, h2]
          · exact h1
        refine ⟨fun q u hq => ?_, fun hf q hq => ?_, h.reads⟩
        · rw [ownerOf_cons (s := s) rfl] at hq
          rw [cellOf_owner]
          by_cases hpq : p = q
          · subst hpq; left; exact h.freeClean hfr p hfree
          · rw [ite_eq_right hpq] at hq; exact h.owned q u hq
        · rw [ownerOf_cons (s := s) rfl] at hq
          rw [cellOf_owner]
          by_cases hpq : p = q
          · rw [ite_eq_left hpq] at hq; simp at hq
          · rw [ite_eq_right hpq] at hq; exact h.freeClean hf q hq
    · rw [ite_eq_right hfree]; exact h
  | free t p =>
    simp only [step]
    by_cases hown : ownerOf s p = some t
    · rw [ite_eq_left hown]
      by_cases hsf : C.scrubOnFree = true
      · rw [ite_eq_left hsf]
        refine ⟨fun q u hq => ?_, fun hf q hq => ?_, h.reads⟩
        · rw [ownerOf_cons (s := s) rfl] at hq
          rw [cellOf_cons (s := s) rfl]
          by_cases hpq : p = q
          · rw [ite_eq_left hpq] at hq; simp at hq
          · rw [ite_eq_right hpq] at hq ⊢; exact h.owned q u hq
        · rw [ownerOf_cons (s := s) rfl] at hq
          rw [cellOf_cons (s := s) rfl]
          by_cases hpq : p = q
          · simp [hpq, clean]
          · rw [ite_eq_right hpq] at hq ⊢; exact h.freeClean hf q hq
      · rw [ite_eq_right hsf]
        refine ⟨fun q u hq => ?_, fun hf q hq => absurd hf hsf, h.reads⟩
        rw [ownerOf_cons (s := s) rfl] at hq
        rw [cellOf_owner]
        by_cases hpq : p = q
        · rw [ite_eq_left hpq] at hq; simp at hq
        · rw [ite_eq_right hpq] at hq; exact h.owned q u hq
    · rw [ite_eq_right hown]; exact h
  | write t p v =>
    simp only [step]
    by_cases hown : ownerOf s p = some t
    · rw [ite_eq_left hown]
      refine ⟨fun q u hq => ?_, fun hf q hq => ?_, h.reads⟩
      · rw [ownerOf_mem] at hq
        rw [cellOf_cons (s := s) rfl]
        by_cases hpq : p = q
        · subst hpq; rw [hown] at hq; cases hq; simp
        · rw [ite_eq_right hpq]; exact h.owned q u hq
      · rw [ownerOf_mem] at hq
        rw [cellOf_cons (s := s) rfl]
        by_cases hpq : p = q
        · subst hpq; rw [hown] at hq; cases hq
        · rw [ite_eq_right hpq]; exact h.freeClean hf q hq
    · rw [ite_eq_right hown]; exact h
  | read t p =>
    simp only [step]
    by_cases hown : ownerOf s p = some t
    · rw [ite_eq_left hown]
      refine ⟨fun q u hq => h.owned q u hq, fun hf q hq => h.freeClean hf q hq, fun r hr => ?_⟩
      rcases List.mem_append.1 hr with hr | hr
      · exact h.reads r hr
      · simp at hr; subst hr; exact h.owned p t hown
    · rw [ite_eq_right hown]; exact h

theorem run_inv (small : ℕ) (C : Checks) (hC : Sound C) (s : St) (ops : List Op) (h : Inv C s) :
    Inv C (run small C s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => rw [run_cons]; exact ih _ (step_inv small C hC s o h)

/-- **No residue under a sound policy.** For any trace from `init`, every read returns scrubbed memory or the reading
tenant's own write. Adversary: TRACE_ARBITRARY. -/
theorem residue_safe (small : ℕ) (C : Checks) (hC : Sound C) (ops : List Op) :
    ∀ r ∈ (run small C init ops).reads, ReadOk r :=
  (run_inv small C hC init ops (inv_init C)).reads

/-! ## Noninterference: B's reads do not depend on A's written values -/

/-- two operations equal except for the value of a write by tenant `A` -/
def SameExceptA (A : ℕ) : Op → Op → Prop
  | .write t p v, .write t' p' v' => t = t' ∧ p = p' ∧ (t = A ∨ v = v')
  | o, o' => o = o'

/-- the parts of two states B can observe agree -/
structure Rel (A : ℕ) (s t : St) : Prop where
  owner : s.owner = t.owner
  writer : ∀ p, (cellOf s p).writer = (cellOf t p).writer
  val : ∀ p, (cellOf s p).writer ≠ some A → (cellOf s p).val = (cellOf t p).val
  reads : s.reads.filter (fun r => r.tenant ≠ A) = t.reads.filter (fun r => r.tenant ≠ A)

theorem ownerOf_congr {s t : St} (h : s.owner = t.owner) (p : ℕ) : ownerOf s p = ownerOf t p := by
  simp [ownerOf, h]

theorem step_rel (small : ℕ) (C : Checks) (A : ℕ) (s t : St) (hs : Inv C s) (o o' : Op)
    (ho : SameExceptA A o o') (h : Rel A s t) : Rel A (step small C s o) (step small C t o') := by
  obtain ⟨hown, hw, hv, hr⟩ := h
  have hO := ownerOf_congr hown
  -- same cell prepended on both sides
  have memcons : ∀ (s' t' : St) (p : ℕ) (c : Cell), s'.mem = (p, c) :: s.mem → t'.mem = (p, c) :: t.mem →
      (∀ q, (cellOf s' q).writer = (cellOf t' q).writer) ∧
      (∀ q, (cellOf s' q).writer ≠ some A → (cellOf s' q).val = (cellOf t' q).val) := by
    intro s' t' p c h1 h2
    refine ⟨fun q => ?_, fun q hq => ?_⟩
    · rw [cellOf_cons h1, cellOf_cons h2]
      by_cases hpq : p = q
      · simp [hpq]
      · simp only [hpq, ite_false]; exact hw q
    · rw [cellOf_cons h1] at hq; rw [cellOf_cons h1, cellOf_cons h2]
      by_cases hpq : p = q
      · simp [hpq]
      · simp only [hpq, ite_false] at hq ⊢; exact hv q hq
  cases o with
  | write a p v =>
    cases o' with
    | write a' p' v' =>
      obtain ⟨rfl, rfl, hav⟩ := ho
      simp only [step]
      rw [hO]
      by_cases hown' : ownerOf t p = some a
      · rw [ite_eq_left hown', ite_eq_left hown']
        have e1 : ∀ q, cellOf { s with mem := (p, ⟨v, some a⟩) :: s.mem } q =
            if p = q then ⟨v, some a⟩ else cellOf s q := fun q => cellOf_cons rfl q
        have e2 : ∀ q, cellOf { t with mem := (p, ⟨v', some a⟩) :: t.mem } q =
            if p = q then ⟨v', some a⟩ else cellOf t q := fun q => cellOf_cons rfl q
        refine ⟨hown, fun q => ?_, fun q hq => ?_, hr⟩
        · rw [e1, e2]
          by_cases hpq : p = q
          · simp [hpq]
          · simp only [hpq, ite_false]; exact hw q
        · rw [e1] at hq; rw [e1, e2]
          by_cases hpq : p = q
          · simp only [hpq, ite_true] at hq ⊢
            rcases hav with rfl | rfl
            · exact absurd rfl hq
            · rfl
          · simp only [hpq, ite_false] at hq ⊢; exact hv q hq
      · rw [ite_eq_right hown', ite_eq_right hown']; exact ⟨hown, hw, hv, hr⟩
    | _ => simp [SameExceptA] at ho
  | alloc a p size =>
    simp only [SameExceptA] at ho; subst ho
    simp only [step]
    rw [hO]
    by_cases hf : ownerOf t p = none
    · rw [ite_eq_left hf, ite_eq_left hf]
      by_cases hsc : C.scrubOnAlloc = true ∧ ¬ (C.fastSkip = true ∧ size < small)
      · rw [ite_eq_left hsc, ite_eq_left hsc]
        obtain ⟨m1, m2⟩ := memcons { s with owner := (p, some a) :: s.owner, mem := (p, clean) :: s.mem }
          { t with owner := (p, some a) :: t.owner, mem := (p, clean) :: t.mem } p clean rfl rfl
        exact ⟨by simp [hown], m1, m2, hr⟩
      · rw [ite_eq_right hsc, ite_eq_right hsc]
        exact ⟨by simp [hown], hw, hv, hr⟩
    · rw [ite_eq_right hf, ite_eq_right hf]; exact ⟨hown, hw, hv, hr⟩
  | free a p =>
    simp only [SameExceptA] at ho; subst ho
    simp only [step]
    rw [hO]
    by_cases hf : ownerOf t p = some a
    · rw [ite_eq_left hf, ite_eq_left hf]
      by_cases hsc : C.scrubOnFree = true
      · rw [ite_eq_left hsc, ite_eq_left hsc]
        obtain ⟨m1, m2⟩ := memcons { s with owner := (p, none) :: s.owner, mem := (p, clean) :: s.mem }
          { t with owner := (p, none) :: t.owner, mem := (p, clean) :: t.mem } p clean rfl rfl
        exact ⟨by simp [hown], m1, m2, hr⟩
      · rw [ite_eq_right hsc, ite_eq_right hsc]
        exact ⟨by simp [hown], hw, hv, hr⟩
    · rw [ite_eq_right hf, ite_eq_right hf]; exact ⟨hown, hw, hv, hr⟩
  | read a p =>
    simp only [SameExceptA] at ho; subst ho
    simp only [step]
    rw [hO]
    by_cases hown' : ownerOf t p = some a
    · rw [ite_eq_left hown', ite_eq_left hown']
      refine ⟨hown, hw, hv, ?_⟩
      simp only [List.filter_append, hr]
      congr 1
      by_cases ha : a = A
      · simp [ha]
      · have hok := hs.owned p a (by rw [hO]; exact hown')
        have hnA : (cellOf s p).writer ≠ some A := by
          rcases hok with hok | hok
          · rw [hok]; simp
          · rw [hok]; simpa using ha
        simp [ha, hv p hnA, hw p]
    · rw [ite_eq_right hown', ite_eq_right hown']; exact ⟨hown, hw, hv, hr⟩

theorem step_rel_inv (small : ℕ) (C : Checks) (hC : Sound C) (A : ℕ) (ops ops' : List Op)
    (h : List.Forall₂ (SameExceptA A) ops ops') :
    ∀ s t, Inv C s → Rel A s t → Rel A (run small C s ops) (run small C t ops') := by
  induction h with
  | nil => intro s t _ hr; exact hr
  | cons hx _ ih =>
    intro s t hs hr
    rw [run_cons, run_cons]
    exact ih _ _ (step_inv small C hC s _ hs) (step_rel small C A s t hs _ _ hx hr)

/-- **Noninterference.** Under a sound policy, two traces that differ only in the values tenant `A` writes give every
other tenant exactly the same reads. -/
theorem noninterference (small : ℕ) (C : Checks) (hC : Sound C) (A : ℕ) (ops ops' : List Op)
    (h : List.Forall₂ (SameExceptA A) ops ops') :
    (run small C init ops).reads.filter (fun r => r.tenant ≠ A) =
      (run small C init ops').reads.filter (fun r => r.tenant ≠ A) :=
  (step_rel_inv small C hC A ops ops' h init init (inv_init C) ⟨rfl, fun _ => rfl, fun _ _ => rfl, rfl⟩).reads

/-! ## Witnesses (tenant 1 writes 42 into page 0, frees it; tenant 2 allocates page 0 and reads) -/

def trace (size : ℕ) : List Op := [.alloc 1 0 64, .write 1 0 42, .free 1 0, .alloc 2 0 size, .read 2 0]

/-- **No scrubbing: B reads A's residue.** -/
theorem no_scrub_residue : (run 16 ⟨false, false, false⟩ init (trace 64)).reads = [⟨2, 0, 42, some 1⟩] := by
  decide

/-- **Scrub skipped on a fast path** (allocations below 16): a small allocation returns A's residue. -/
theorem fast_path_skip_residue :
    (run 16 ⟨true, false, true⟩ init (trace 8)).reads = [⟨2, 0, 42, some 1⟩] ∧
    (run 16 ⟨true, false, true⟩ init (trace 64)).reads = [⟨2, 0, 0, none⟩] := by
  decide

theorem scrub_on_alloc_clean : (run 16 full init (trace 8)).reads = [⟨2, 0, 0, none⟩] := by decide

theorem scrub_on_free_clean : (run 16 ⟨false, true, false⟩ init (trace 8)).reads = [⟨2, 0, 0, none⟩] := by decide

/-! ## Time-slicing: per-context local memory across context switches -/

namespace Slice

structure St where
  cur : ℕ
  scratch : List (ℕ × Cell)
  reads : List Read
deriving DecidableEq, Repr

inductive Op where
  | switch (t : ℕ)
  | write (a v : ℕ)
  | read (a : ℕ)
deriving DecidableEq, Repr

def cellOf (s : St) (a : ℕ) : Cell := ((s.scratch.find? (fun e => e.1 = a)).map Prod.snd).getD clean

/-- `clear`: scratch memory is cleared on every context switch -/
def step (clear : Bool) (s : St) : Op → St
  | .switch t => { s with cur := t, scratch := if clear then [] else s.scratch }
  | .write a v => { s with scratch := (a, ⟨v, some s.cur⟩) :: s.scratch }
  | .read a => { s with reads := s.reads ++ [⟨s.cur, a, (cellOf s a).val, (cellOf s a).writer⟩] }

def run (clear : Bool) (s : St) (ops : List Op) : St := ops.foldl (step clear) s

theorem run_cons (clear : Bool) (s : St) (o : Op) (ops : List Op) :
    run clear s (o :: ops) = run clear (step clear s o) ops := rfl

structure Inv (s : St) : Prop where
  scratch_ok : ∀ e ∈ s.scratch, e.2.writer = some s.cur
  reads : ∀ r ∈ s.reads, ReadOk r

theorem cellOf_ok (s : St) (h : ∀ e ∈ s.scratch, e.2.writer = some s.cur) (a : ℕ) :
    (cellOf s a).writer = none ∨ (cellOf s a).writer = some s.cur := by
  unfold cellOf
  cases hf : s.scratch.find? (fun e => e.1 = a) with
  | none => left; rfl
  | some e => right; simpa using h e (List.mem_of_find?_eq_some hf)

theorem step_inv (s : St) (o : Op) (h : Inv s) : Inv (step true s o) := by
  cases o with
  | switch t => exact ⟨by simp [step], h.reads⟩
  | write a v =>
    refine ⟨fun e he => ?_, h.reads⟩
    simp only [step, List.mem_cons] at he
    rcases he with rfl | he
    · rfl
    · exact h.scratch_ok e he
  | read a =>
    refine ⟨h.scratch_ok, fun r hr => ?_⟩
    simp only [step, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact h.reads r hr
    · exact cellOf_ok s h.scratch_ok a

/-- **Cleared on every switch: no cross-context residue.** Every read by a context returns zero or its own write. -/
theorem slice_safe (s : St) (hs : Inv s) (ops : List Op) : ∀ r ∈ (run true s ops).reads, ReadOk r := by
  induction ops generalizing s with
  | nil => exact hs.reads
  | cons o ops ih => rw [run_cons]; exact ih _ (step_inv s o hs)

def init : St := ⟨0, [], []⟩

theorem inv_init : Inv init := ⟨by simp [init], by simp [init]⟩

/-- **Not cleared: the next tenant's context reads the previous tenant's value.** -/
theorem no_clear_leaks :
    (run false init [.switch 1, .write 0 42, .switch 2, .read 0]).reads = [⟨2, 0, 42, some 1⟩] ∧
    (run true init [.switch 1, .write 0 42, .switch 2, .read 0]).reads = [⟨2, 0, 0, none⟩] := by
  decide

end Slice

end ControlStack.GPUResidue

#print axioms ControlStack.GPUResidue.residue_safe
#print axioms ControlStack.GPUResidue.noninterference
#print axioms ControlStack.GPUResidue.no_scrub_residue
#print axioms ControlStack.GPUResidue.fast_path_skip_residue
#print axioms ControlStack.GPUResidue.scrub_on_alloc_clean
#print axioms ControlStack.GPUResidue.scrub_on_free_clean
#print axioms ControlStack.GPUResidue.Slice.slice_safe
#print axioms ControlStack.GPUResidue.Slice.no_clear_leaks
