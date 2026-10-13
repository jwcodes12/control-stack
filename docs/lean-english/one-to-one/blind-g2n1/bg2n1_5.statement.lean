namespace PL_bg2n1_5
open ControlStack.SC09

-- NOTE
-- AMBIGUOUS: "sub-collection" could mean membership inclusion, multiset
-- inclusion (counting repeated capabilities), or an order-preserving
-- sublist. This statement uses membership inclusion: every capability
-- held by a newly appearing process was held by the parent.
def Back_spawn_attenuates : Prop :=
  ∀ (P : Policy) (s : St) (p ch : ℕ) (q : Proc) (keep : List ℕ),
    s.halted = false →
    procOf s p = some q →
    procOf s ch = none →
    ∀ r ∈ (step P full s (.spawn p ch keep)).procs,
      r ∉ s.procs →
      r.lin = q.lin ∧ (∀ c ∈ r.caps, c ∈ q.caps)

def BackAt (P : Policy) (s : St) (p ch : ℕ) (q : Proc) (keep : List ℕ) : Prop :=
  ∀ r ∈ (step P full s (.spawn p ch keep)).procs,
    r ∉ s.procs → r.lin = q.lin ∧ (∀ c ∈ r.caps, c ∈ q.caps)
def OrigAt (P : Policy) (s : St) (p ch : ℕ) (keep : List ℕ) (q : Proc) : Prop :=
  ∀ r ∈ (step P full s (.spawn p ch keep)).procs,
    r ∉ s.procs → r.lin = q.lin ∧ r.caps ⊆ q.caps
def Claim : Prop :=
  (Back_spawn_attenuates = (∀ P s p ch q keep,
    s.halted = false → procOf s p = some q → procOf s ch = none →
      BackAt P s p ch q keep)) ∧
  (∀ P s p ch q keep, s.halted = false → procOf s p = some q →
    procOf s ch = none → (BackAt P s p ch q keep ↔ OrigAt P s p ch keep q)) ∧
  (∀ (xs ys : List ℕ), (∀ c ∈ xs, c ∈ ys) ↔ xs ⊆ ys)
def Witness : Prop :=
  let q : Proc := ⟨1, 3, [7, 7, 8]⟩
  let s : St := ⟨[q], [], [], false⟩
  s.halted = false ∧ procOf s 1 = some q ∧ procOf s 2 = none ∧
  (step P0 full s (.spawn 1 2 [7])).procs = [q, ⟨2, 3, [7, 7]⟩] ∧
  (⟨2, 3, [7, 7]⟩ : Proc) ∉ s.procs ∧
  ([7, 7] : List ℕ) ⊆ [7] ∧ ¬ ([7, 7] : List ℕ).Sublist [7]

end PL_bg2n1_5
