open ControlStack.SC18Refinement ControlStack.SC18Liveness
def LenInv (s : CSt) : Prop := ∀ r ∈ s.released, r.llen ≤ s.ackd.length

theorem len_step (T : ℕ) (s : CSt) (o : COp) (h : LenInv s) : LenInv (stepC real T s o) := by
  cases o <;> simp only [stepC] <;> (repeat' split)
  all_goals try exact h
  · intro r hr
    simpa only [List.length_append, List.length_singleton] using Nat.le_succ_of_le (h r hr)
  · intro r hr
    rcases List.mem_append.1 hr with hr | hr
    · exact h r hr
    · simp only [List.mem_singleton] at hr
      subst r
      exact le_rfl

theorem len_run (T : ℕ) (s : CSt) (ops : List COp) (h : LenInv s) : LenInv (runC real T s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons o ops ih => exact ih (stepC real T s o) (len_step T s o h)

theorem back_shape : ControlStack.SC18Refinement.Back_concrete_safe =
    (∀ T ops, BackPoint T (runC real T cinit ops)) := rfl

theorem original_type (T : ℕ) (ops : List COp) : OrigPoint T (runC real T cinit ops) :=
  concrete_safe T ops

theorem claim : Claim := by
  intro T ops
  have hlen := len_run T cinit ops (by intro r hr; simp [cinit] at hr)
  constructor
  · intro hb
    refine ⟨?_, hb.2⟩
    intro r hr
    exact ⟨by simpa [α] using hlen r hr, (hb.1 r hr).1, (hb.1 r hr).2⟩
  · intro ho
    exact ⟨fun r hr => (ho.1 r hr).2, ho.2⟩

theorem witness : Witness := by simp only [Witness]; decide

theorem unreachable_count_counterexample :
    let c : CSt := { cinit with ackd := [(0, 0)], released := [⟨0, 2, 0, 0⟩] }
    BackPoint 1 c ∧ ¬ OrigPoint 1 c := by
  simp [BackPoint, OrigPoint, α, cinit, Resume.RelOk]
