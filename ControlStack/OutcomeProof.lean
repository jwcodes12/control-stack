import ControlStack.Outcome

open OracleComp

namespace ControlStack.OutcomeGame

open ControlStack.Bridge (honeypotPasses binCDF)
open ControlStack.Refine (Hist catG deploy protocolGame)

/-- the catastrophe indicator -/
def isCat (o : Outcome) : Bool := decide (o = Outcome.catastrophe)

theorem probOutput_isCat (c : ProbComp Outcome) :
    Pr[= true | isCat <$> c] = Pr[= Outcome.catastrophe | c] := by
  rw [probOutput_map_eq_tsum_ite]
  rw [tsum_eq_single Outcome.catastrophe (fun o ho => by cases o <;> simp_all [isCat])]
  simp [isCat]

theorem map_deployO {X Z : Type} (Bad : X → Prop) [DecidablePred Bad] (π : Hist X Z → ProbComp X)
    (M : X → ProbComp Z) (D : Z → ProbComp Bool) (A : Hist X Z → X → Z → ProbComp Bool) (b n : ℕ) :
    ∀ u h, isCat <$> deployO Bad π M D A b n u h = deploy Bad π M D A b n u h := by
  induction n with
  | zero => intro u h; simp [deployO, deploy, isCat]
  | succ n ih =>
    intro u h
    simp only [deployO, deploy, map_bind]
    refine bind_congr fun x => bind_congr fun z => bind_congr fun pass => ?_
    split_ifs <;> simp [ih, isCat, Functor.map_map]

theorem marginal : MarginalClaim := by
  refine ⟨?_, ?_⟩
  · intro X Z Bad _ π M D A b n u h
    rw [← map_deployO, probOutput_isCat]
  · intro X Z Ω Bad _ ρ H M D π A nh ns b N
    have : isCat <$> gameO Bad ρ H M D π A nh ns b N = protocolGame Bad ρ H M D π A nh ns b N := by
      simp only [gameO, protocolGame, map_bind]
      refine bind_congr fun ω => bind_congr fun k => ?_
      split_ifs
      · exact map_deployO _ _ _ _ _ _ _ _ _
      · simp [isCat]
    rw [← this, probOutput_isCat]


theorem probOutput_auditO (c : ProbComp Bool) (o : Outcome) :
    Pr[= o | (fun caught => if caught then Outcome.caught else Outcome.catastrophe) <$> c] =
      Pr[= true | c] * (if o = Outcome.caught then 1 else 0) +
      Pr[= false | c] * (if o = Outcome.catastrophe then 1 else 0) := by
  rw [probOutput_map_eq_tsum, tsum_fintype, Fintype.sum_bool]
  cases o <;> simp

theorem deployO_step {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) (o : Outcome) :
    Pr[= o | deployO Bad π M D A b (n+1) u h] = ∑ x, Pr[= x | π h] * ∑ z, Pr[= z | M x] *
      (Pr[= true | D z] * Pr[= o | (if Bad x then pure .catastrophe
          else deployO Bad π M D A b n u (h ++ [(x, z, true)]) : ProbComp Outcome)] +
       Pr[= false | D z] * Pr[= o | (if u < b then
        (if Bad x then (fun caught => if caught then Outcome.caught else Outcome.catastrophe) <$> A h x z
         else deployO Bad π M D A b n (u + 1) (h ++ [(x, z, false)])) else pure .halted : ProbComp Outcome)]) := by
  rw [deployO]
  simp only [probOutput_bind_eq_tsum, tsum_fintype, Fintype.sum_bool]
  simp

theorem deployO_step_real {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) (o : Outcome) :
    (Pr[= o | deployO Bad π M D A b (n+1) u h]).toReal = ∑ x, (Pr[= x | π h]).toReal * ∑ z, (Pr[= z | M x]).toReal *
      ((Pr[= true | D z]).toReal * (Pr[= o | (if Bad x then pure .catastrophe
          else deployO Bad π M D A b n u (h ++ [(x, z, true)]) : ProbComp Outcome)]).toReal +
       (1 - (Pr[= true | D z]).toReal) * (Pr[= o | (if u < b then
        (if Bad x then (fun caught => if caught then Outcome.caught else Outcome.catastrophe) <$> A h x z
         else deployO Bad π M D A b n (u + 1) (h ++ [(x, z, false)])) else pure .halted : ProbComp Outcome)]).toReal) := by
  rw [deployO_step, ENNReal.toReal_sum (fun x _ => ENNReal.mul_ne_top probOutput_ne_top
    (ENNReal.sum_ne_top.2 fun z _ => ENNReal.mul_ne_top probOutput_ne_top
      (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top probOutput_ne_top probOutput_ne_top,
        ENNReal.mul_ne_top probOutput_ne_top probOutput_ne_top⟩)))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_sum (fun z _ => ENNReal.mul_ne_top probOutput_ne_top
      (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top probOutput_ne_top probOutput_ne_top,
        ENNReal.mul_ne_top probOutput_ne_top probOutput_ne_top⟩))]
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (ENNReal.mul_ne_top probOutput_ne_top probOutput_ne_top)
    (ENNReal.mul_ne_top probOutput_ne_top probOutput_ne_top), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ControlStack.Refine.probOutput_false_toReal]

theorem deployO_rejected {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool) (b n : ℕ) :
    ∀ u h, Pr[= Outcome.rejected | deployO Bad π M D A b n u h] = 0 := by
  induction n with
  | zero => intro u h; simp [deployO]
  | succ n ih =>
    intro u h
    rw [deployO_step]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : Bad x <;> by_cases hu : u < b <;> simp [hx, hu, ih, probOutput_auditO]

theorem deployLaw : DeployLawClaim := by
  intro X Z _ _ Bad _ π M D A b n
  induction n with
  | zero =>
    intro u h
    simp [deployO, catG, caughtG, haltP, complG]
  | succ n ih =>
    intro u h
    dsimp only at ih ⊢
    refine ⟨?_, ?_, ?_, ?_, deployO_rejected _ _ _ _ _ _ _ _ _⟩
    · rw [marginal.1, ControlStack.Refine.deployG]
    · rw [deployO_step_real, caughtG]
      refine Finset.sum_congr rfl fun x _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun z _ => ?_
      congr 1
      by_cases hx : Bad x <;> by_cases hu : u < b <;> simp [hx, hu, ih, probOutput_auditO]
    · rw [deployO_step_real, haltP]
      refine Finset.sum_congr rfl fun x _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun z _ => ?_
      congr 1
      by_cases hx : Bad x <;> by_cases hu : u < b <;> simp [hx, hu, ih, probOutput_auditO]
    · rw [deployO_step_real, complG]
      refine Finset.sum_congr rfl fun x _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun z _ => ?_
      congr 1
      by_cases hx : Bad x <;> by_cases hu : u < b <;> simp [hx, hu, ih, probOutput_auditO]

theorem conservation : ConservationClaim := by
  intro X Z _ _ Bad _ M φ π R b hM hπ n
  induction n with
  | zero => intro u h; simp [catG, caughtG, haltP, complG]
  | succ n ih =>
    intro u h
    simp only [catG, caughtG, haltP, complG]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine (Finset.sum_congr rfl fun x _ => ?_).trans (hπ h)
    rw [← mul_add, ← mul_add, ← mul_add]
    conv_rhs => rw [← mul_one (π h x)]
    congr 1
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine (Finset.sum_congr rfl fun z _ => ?_).trans (hM x)
    rw [← mul_add, ← mul_add, ← mul_add]
    conv_rhs => rw [← mul_one (M x z)]
    congr 1
    have i1 := ih u (h ++ [(x, z, true)])
    have i2 := ih (u + 1) (h ++ [(x, z, false)])
    by_cases hx : Bad x <;> by_cases hu : u < b <;> simp only [hx, hu, if_true, if_false]
    · ring
    · ring
    · linear_combination φ z * i1 + (1 - φ z) * i2
    · linear_combination φ z * i1

theorem nonneg : NonnegClaim := by
  intro X Z _ _ Bad _ M φ π R b hM hπ hφ hR n
  induction n with
  | zero => intro u h; simp [catG, caughtG, haltP, complG]
  | succ n ih =>
    intro u h
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [catG, caughtG, haltP, complG] <;>
    refine Finset.sum_nonneg fun x _ => mul_nonneg (hπ h x)
      (Finset.sum_nonneg fun z _ => mul_nonneg (hM x z) ?_) <;>
    obtain ⟨φ0, φ1⟩ := hφ z <;>
    obtain ⟨R0, R1⟩ := hR h x z <;>
    obtain ⟨a1, a2, a3, a4⟩ := ih u (h ++ [(x, z, true)]) <;>
    obtain ⟨b1, b2, b3, b4⟩ := ih (u + 1) (h ++ [(x, z, false)]) <;>
    exact add_nonneg (mul_nonneg φ0 (by split_ifs <;> linarith))
      (mul_nonneg (by linarith) (by split_ifs <;> linarith))

theorem deployO_rejected' {X Z : Type} (Bad : X → Prop) [DecidablePred Bad]
    (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool) (b n : ℕ) :
    ∀ u h, Pr[= Outcome.rejected | deployO Bad π M D A b n u h] = 0 := by
  induction n with
  | zero => intro u h; simp [deployO]
  | succ n ih =>
    intro u h
    have key : ∀ x z (pass : Bool), Pr[= Outcome.rejected | (if pass = true then
        (if Bad x then pure .catastrophe else deployO Bad π M D A b n u (h ++ [(x, z, true)]))
      else if u < b then
        (if Bad x then (fun caught => if caught then Outcome.caught else Outcome.catastrophe) <$> A h x z
         else deployO Bad π M D A b n (u + 1) (h ++ [(x, z, false)]))
      else pure .halted : ProbComp Outcome)] = 0 := by
      intro x z pass
      split_ifs <;> simp [ih, probOutput_auditO]
    rw [deployO]
    simp only [probOutput_bind_eq_tsum, key, mul_zero, tsum_zero]

theorem probEvent_not_toReal {α : Type} (c : ProbComp α) (p : α → Prop) :
    (Pr[fun x => ¬ p x | c]).toReal = 1 - (Pr[p | c]).toReal := by
  have h := probEvent_compl c p
  simp only [probFailure_eq_zero, tsub_zero] at h
  have h2 := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_add probEvent_ne_top probEvent_ne_top] at h2
  simp at h2
  linarith

theorem gameLaw : GameLawClaim := by
  intro X Z Ω _ Bad _ ρ H M D π A nh ns b N
  refine ⟨?_, ?_⟩
  · intro o ho
    have key : ∀ ω, Pr[= o | honeypotPasses H M (D ω) nh >>= fun k =>
        if k ≤ ns then deployO Bad (π ω) M (D ω) A b N 0 [] else pure .rejected] =
        Pr[fun k => k ≤ ns | honeypotPasses H M (D ω) nh] *
          Pr[= o | deployO Bad (π ω) M (D ω) A b N 0 []] := by
      intro ω
      rw [probOutput_bind_eq_tsum, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      refine tsum_congr fun k => ?_
      by_cases hk : k ≤ ns <;> simp [hk, ho]
    unfold gameO
    rw [probOutput_bind_eq_tsum, tsum_fintype]
    simp only [key]
    rw [ENNReal.toReal_sum (fun ω _ => by finiteness)]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, Bridge.bridge, mul_assoc]
  · have key : ∀ ω, Pr[= Outcome.rejected | honeypotPasses H M (D ω) nh >>= fun k =>
        if k ≤ ns then deployO Bad (π ω) M (D ω) A b N 0 [] else pure .rejected] =
        Pr[fun k => ¬ k ≤ ns | honeypotPasses H M (D ω) nh] := by
      intro ω
      rw [probOutput_bind_eq_tsum, probEvent_eq_tsum_ite]
      refine tsum_congr fun k => ?_
      by_cases hk : k ≤ ns <;> simp [hk, deployO_rejected']
    unfold gameO
    rw [probOutput_bind_eq_tsum, tsum_fintype]
    simp only [key]
    rw [ENNReal.toReal_sum (fun ω _ => by finiteness)]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [ENNReal.toReal_mul, probEvent_not_toReal, Bridge.bridge]

theorem rateLink : RateLinkClaim := by
  intro X Z _ _ H μ M D₀
  have hz : ∀ (P : ProbComp X) z, (Pr[= z | P >>= M]).toReal =
      ∑ x, (Pr[= x | P]).toReal * (Pr[= z | M x]).toReal := by
    intro P z
    rw [probOutput_bind_eq_tsum, tsum_fintype, ENNReal.toReal_sum (fun x _ => by finiteness)]
    simp only [ENNReal.toReal_mul]
  refine ⟨?_, ?_⟩
  · rw [probOutput_bind_eq_tsum, tsum_fintype, ENNReal.toReal_sum (fun x _ => by finiteness)]
    unfold missRate push
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [ENNReal.toReal_mul, hz]
  · rw [probOutput_bind_eq_tsum, tsum_fintype, ENNReal.toReal_sum (fun x _ => by finiteness)]
    unfold flagRate
    simp only [ENNReal.toReal_mul, hz, ControlStack.Refine.probOutput_false_toReal, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    ring
theorem binCDF_succ_zero (n : ℕ) (f : ℝ) : binCDF (n + 1) 0 f = (1 - f) * binCDF n 0 f := by
  simp [binCDF, pow_succ]
  ring

theorem binCDF_succ_succ (n s : ℕ) (f : ℝ) :
    binCDF (n + 1) (s + 1) f = (1 - f) * binCDF n (s + 1) f + f * binCDF n s f := by
  unfold binCDF
  rw [Finset.sum_range_succ' _ (s + 1),
    Finset.sum_range_succ' (fun j => (n.choose j : ℝ) * f ^ j * (1 - f) ^ (n - j)) (s + 1)]
  have e : ∀ i ∈ Finset.range (s + 1),
      ((n + 1).choose (i + 1) : ℝ) * f ^ (i + 1) * (1 - f) ^ (n + 1 - (i + 1)) =
      (1 - f) * ((n.choose (i + 1) : ℝ) * f ^ (i + 1) * (1 - f) ^ (n - (i + 1))) +
      f * ((n.choose i : ℝ) * f ^ i * (1 - f) ^ (n - i)) := by
    intro i _
    rw [Nat.choose_succ_succ, Nat.cast_add, show n + 1 - (i + 1) = n - i by omega]
    rcases Nat.lt_or_ge i n with hi | hi
    · rw [show n - i = (n - (i + 1)) + 1 by omega]
      ring
    · rw [Nat.choose_eq_zero_of_lt (by omega : n < i + 1)]
      ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp [pow_succ]
  ring

theorem wsum_const {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (φ : Z → ℝ) (μ : X → ℝ)
    (hM1 : ∀ x, ∑ z, M x z = 1) (hμ1 : ∑ x, μ x = 1) (a c : ℝ) :
    ∑ x, μ x * ∑ z, M x z * (φ z * a + (1 - φ z) * c) =
      (1 - flagRate M μ φ) * a + flagRate M μ φ * c := by
  have hx : ∀ x, ∑ z, M x z * (φ z * a + (1 - φ z) * c) =
      a - (a - c) * ∑ z, M x z * (1 - φ z) := by
    intro x
    calc ∑ z, M x z * (φ z * a + (1 - φ z) * c)
        = ∑ z, (a * M x z - (a - c) * (M x z * (1 - φ z))) :=
          Finset.sum_congr rfl fun z _ => by ring
      _ = a * ∑ z, M x z - (a - c) * ∑ z, M x z * (1 - φ z) := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = a - (a - c) * ∑ z, M x z * (1 - φ z) := by rw [hM1 x, mul_one]
  simp only [hx]
  unfold flagRate
  calc ∑ x, μ x * (a - (a - c) * ∑ z, M x z * (1 - φ z))
      = ∑ x, (a * μ x - (a - c) * (μ x * ∑ z, M x z * (1 - φ z))) :=
        Finset.sum_congr rfl fun x _ => by ring
    _ = a * ∑ x, μ x - (a - c) * ∑ x, μ x * ∑ z, M x z * (1 - φ z) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = _ := by rw [hμ1]; ring

theorem catG_benign {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (R : Hist X Z → X → Z → ℝ) (b : ℕ)
    (hben : ∀ h x, π h x ≠ 0 → ¬ Bad x) :
    ∀ n u h, catG Bad M φ π R b n u h = 0 ∧ caughtG Bad M φ π R b n u h = 0 := by
  intro n
  induction n with
  | zero => intro u h; simp [catG, caughtG]
  | succ n ih =>
    intro u h
    simp only [catG, caughtG]
    constructor <;> refine Finset.sum_eq_zero fun x _ => ?_ <;>
    (by_cases h0 : π h x = 0
     · simp [h0]
     · simp [hben h x h0, ih])

theorem complG_benign {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ : Z → ℝ) (μ : X → ℝ) (b : ℕ)
    (hM1 : ∀ x, ∑ z, M x z = 1) (hμ1 : ∑ x, μ x = 1) (hben : ∀ x, μ x ≠ 0 → ¬ Bad x) :
    ∀ n u h, u ≤ b → complG Bad M φ (fun _ => μ) b n u h = binCDF n (b - u) (flagRate M μ φ) := by
  intro n
  induction n with
  | zero => intro u h _; simp [complG, binCDF, Finset.sum_range_succ']
  | succ n ih =>
    intro u h hub
    set f := flagRate M μ φ with hf
    have step : complG Bad M φ (fun _ => μ) b (n + 1) u h =
        ∑ x, μ x * ∑ z, M x z * (φ z * binCDF n (b - u) f +
          (1 - φ z) * (if u < b then binCDF n (b - (u + 1)) f else 0)) := by
      simp only [complG]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases h0 : μ x = 0
      · simp [h0]
      · have hx := hben x h0
        congr 1
        refine Finset.sum_congr rfl fun z _ => ?_
        by_cases hu : u < b
        · simp only [hx, hu, if_true, if_false, ih u _ hub, ih (u + 1) _ hu]
        · simp only [hx, hu, if_false, ih u _ hub]
    rw [step, wsum_const M φ μ hM1 hμ1, ← hf]
    by_cases hu : u < b
    · rw [if_pos hu, show b - u = (b - (u + 1)) + 1 by omega, binCDF_succ_succ]
    · rw [if_neg hu, show b - u = 0 by omega, binCDF_succ_zero]
      ring

theorem benignRecursion : BenignRecursionClaim := by
  intro X Z _ _ Bad _ M φ₀ μ b N hM hμ0 hμ1 hben hφ
  have hM1 : ∀ x, ∑ z, M x z = 1 := fun x => (hM x).2
  have hc := complG_benign Bad M φ₀ μ b hM1 hμ1 hben N 0 [] (Nat.zero_le _)
  rw [Nat.sub_zero] at hc
  have hz := catG_benign Bad M φ₀ (fun _ => μ) (fun _ _ _ => 0) b (fun _ x hx => hben x hx) N 0 []
  have hcons := conservation X Z Bad M φ₀ (fun _ => μ) (fun _ _ _ => 0) b hM1 (fun _ => hμ1) N 0 []
  refine ⟨?_, hc⟩
  rw [hz.1, hz.2, hc] at hcons
  linarith
theorem honest : HonestClaim := by
  intro X Z Ω _ _ _ Bad _ ρ H μ M D₀ A nh ns b N hben
  dsimp only
  have hGL := gameLaw X Z Ω Bad ρ H M (fun _ => D₀) (fun _ _ => μ) A nh ns b N
  have hDL := deployLaw X Z Bad (fun _ => μ) M D₀ A b N 0 []
  dsimp only at hGL hDL
  have hρ := ControlStack.Refine.sum_toReal_probOutput ρ
  have hfac : ∀ o, o ≠ Outcome.rejected →
      (Pr[= o | gameO Bad ρ H M (fun _ => D₀) (fun _ _ => μ) A nh ns b N]).toReal =
        binCDF nh ns (Pr[= true | H >>= M >>= D₀]).toReal *
          (Pr[= o | deployO Bad (fun _ => μ) M D₀ A b N 0 []]).toReal := by
    intro o ho
    rw [hGL.1 o ho, ← Finset.sum_mul, ← Finset.sum_mul, hρ, one_mul]
  have hben' : ∀ x, (Pr[= x | μ]).toReal ≠ 0 → ¬ Bad x :=
    fun x hx => hben x (fun h0 => hx (by simp [h0]))
  have hBR := benignRecursion X Z Bad (fun x z => (Pr[= z | M x]).toReal)
    (fun z => (Pr[= true | D₀ z]).toReal) (fun x => (Pr[= x | μ]).toReal) b N
    (fun x => ⟨fun z => ENNReal.toReal_nonneg, ControlStack.Refine.sum_toReal_probOutput _⟩)
    (fun x => ENNReal.toReal_nonneg) (ControlStack.Refine.sum_toReal_probOutput μ) hben'
    (fun z => ⟨ENNReal.toReal_nonneg, ControlStack.Refine.toReal_probOutput_le_one _ _⟩)
  rw [← (rateLink X Z H μ M D₀).2] at hBR
  have hCB := catG_benign Bad (fun x z => (Pr[= z | M x]).toReal) (fun z => (Pr[= true | D₀ z]).toReal)
    (fun _ x => (Pr[= x | μ]).toReal) (fun h x z => (Pr[= true | A h x z]).toReal) b
    (fun _ x hx => hben' x hx) N 0 []
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hfac _ (by decide), hDL.2.2.2.1, hBR.2]
  · rw [hfac _ (by decide), hDL.2.2.1, hBR.1]
  · have hc0 : (Pr[= Outcome.catastrophe |
        gameO Bad ρ H M (fun _ => D₀) (fun _ _ => μ) A nh ns b N]).toReal = 0 := by
      rw [hfac _ (by decide), hDL.1, hCB.1, mul_zero]
    exact ((ENNReal.toReal_eq_zero_iff _).1 hc0).resolve_right probOutput_ne_top
  · have hc0 : (Pr[= Outcome.caught |
        gameO Bad ρ H M (fun _ => D₀) (fun _ _ => μ) A nh ns b N]).toReal = 0 := by
      rw [hfac _ (by decide), hDL.2.1, hCB.2, mul_zero]
    exact ((ENNReal.toReal_eq_zero_iff _).1 hc0).resolve_right probOutput_ne_top
  · rw [hGL.2, ← Finset.sum_mul, hρ, one_mul]
theorem binCDF_nonneg (n s : ℕ) (f : ℝ) (h0 : 0 ≤ f) (h1 : f ≤ 1) : 0 ≤ binCDF n s f := by
  unfold binCDF
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg h0 _)) (pow_nonneg (by linarith) _)

theorem pareto : ParetoClaim := by
  intro X Z _ _ Bad _ H μ M D₀ A nh ns b N r x₀ hben hx₀ hN hA
  dsimp only
  have hα : (Pr[= true | H >>= M >>= fun _ => H >>= M >>= D₀]).toReal =
      (Pr[= true | H >>= M >>= D₀]).toReal := by
    rw [probOutput_bind_const]
    simp only [probFailure_eq_zero, tsub_zero, one_mul]
  have hdep : (Pr[= Outcome.catastrophe |
      deployO Bad (fun _ => pure x₀) M (fun _ => H >>= M >>= D₀) A b N 0 []]).toReal =
      (Pr[= true | H >>= M >>= D₀]).toReal +
        (if 0 < b then (1 - r) * (1 - (Pr[= true | H >>= M >>= D₀]).toReal) else 0) := by
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
    have h1 := (deployLaw X Z Bad (fun _ => pure x₀) M (fun _ => H >>= M >>= D₀) A b (m + 1) 0 []).1
    rw [h1, catG, Fintype.sum_eq_single x₀ (fun x hx => by classical simp [hx])]
    simp only [hx₀, if_true, hA]
    simp
    rw [← Finset.sum_mul, ControlStack.Refine.sum_toReal_probOutput, one_mul]
    split_ifs <;> ring
  have hrisk : (Pr[= Outcome.catastrophe | gameO Bad (pure ()) H M (fun _ _ => H >>= M >>= D₀)
      (fun _ _ => pure x₀) A nh ns b N]).toReal =
      binCDF nh ns (Pr[= true | H >>= M >>= D₀]).toReal * ((Pr[= true | H >>= M >>= D₀]).toReal +
        (if 0 < b then (1 - r) * (1 - (Pr[= true | H >>= M >>= D₀]).toReal) else 0)) := by
    rw [(gameLaw X Z Unit Bad (pure ()) H M (fun _ _ => H >>= M >>= D₀) (fun _ _ => pure x₀) A
      nh ns b N).1 _ (by decide), Fintype.sum_unique]
    rw [hα, hdep]
    simp
  have hH := honest X Z Unit Bad (pure ()) H μ M D₀ A nh ns b N hben
  dsimp only at hH
  refine ⟨hrisk, ?_, ?_⟩
  · rw [hrisk, hH.1]
    ring
  · intro Xc hX
    have hle := hX (fun _ _ => H >>= M >>= D₀) (fun _ _ => pure x₀)
    have hB0 := binCDF_nonneg N b (Pr[= false | μ >>= M >>= D₀]).toReal ENNReal.toReal_nonneg
      (ControlStack.Refine.toReal_probOutput_le_one _ _)
    rw [hrisk] at hle
    rw [hH.1]
    have := mul_le_mul_of_nonneg_left hle hB0
    linarith
theorem witness : Witness := by
  have hq : Pr[= true | ((fun k : Fin 4 => decide (k = 0)) <$> $[0..3] : ProbComp Bool)] = 4⁻¹ := by
    rw [probOutput_map_eq_sum_fintype_ite]
    simp
    norm_num
  have hq' : Pr[= false | ((fun k : Fin 4 => decide (k ≠ 0)) <$> $[0..3] : ProbComp Bool)] = 4⁻¹ := by
    rw [probOutput_map_eq_sum_fintype_ite]
    simp
    norm_num
  have h4 : ((4 : ENNReal)⁻¹).toReal = 1 / 4 := by
    rw [ENNReal.toReal_inv]
    norm_num
  unfold Witness
  intro G Dh Gh Gb
  have hα : (Pr[= true | (pure true : ProbComp Bool) >>= (fun x => pure x) >>= Dh]).toReal = 1 / 4 := by
    simp [Dh, hq, h4]
  have hf : (Pr[= false | (pure false : ProbComp Bool) >>= (fun x => pure x) >>= Dh]).toReal = 1 / 4 := by
    have hq'' : Pr[= false | ((fun k : Fin 4 => !decide (k = 0)) <$> $[0..3] : ProbComp Bool)] = 4⁻¹ := by
      simpa using hq'
    simp [Dh, hq'', h4]
  have hben : ∀ x : Bool, Pr[= x | (pure false : ProbComp Bool)] ≠ 0 → ¬ (x = true) := by
    intro x hx; cases x <;> simp_all
  have hH := honest Bool Bool Unit (fun x => x = true) (pure ()) (pure true) (pure false) (fun x => pure x) Dh
    (fun _ _ _ => pure true) 3 1 1 2 hben
  have hP := pareto Bool Bool (fun x => x = true) (pure true) (pure false) (fun x => pure x) Dh
    (fun _ _ _ => pure true) 3 1 1 2 1 true hben rfl (by norm_num) (fun z => by simp)
  dsimp only at hH hP
  rw [hα, hf] at hH hP
  have hB1 : binCDF 3 1 (1 / 4) = 27 / 32 := by norm_num [binCDF, Finset.sum_range_succ]
  have hB2 : binCDF 2 1 (1 / 4) = 15 / 16 := by norm_num [binCDF, Finset.sum_range_succ]
  have hB0 : binCDF 3 0 (1 / 4) = 27 / 64 := by norm_num [binCDF, Finset.sum_range_succ]
  rw [hB1, hB2] at hH
  rw [hB1] at hP
  have hD1 : (Pr[= true | ((fun k : Fin 4 => decide (k = 0)) <$> $[0..3] : ProbComp Bool)]).toReal =
      1 / 4 := by rw [hq, h4]
  have htest : (Pr[= true | (pure true : ProbComp Bool) >>= (fun x => pure x) >>=
      fun _ => (fun k : Fin 4 => decide (k = 0)) <$> $[0..3]]).toReal = 1 / 4 := by
    simp [hq, h4]
  have gG := gameLaw Bool Bool Unit (fun x => x = true) (pure ()) (pure true) (fun x => pure x)
    (fun _ _ => (fun k : Fin 4 => decide (k = 0)) <$> $[0..3]) (fun _ _ => pure true)
    (fun _ _ _ => pure true) 3 0 1 2
  have dG := deployLaw Bool Bool (fun x => x = true) (fun _ => pure true) (fun x => pure x)
    (fun _ => (fun k : Fin 4 => decide (k = 0)) <$> $[0..3]) (fun _ _ _ => pure true) 1 2 0 []
  dsimp only at dG
  have hne : ∀ c : ProbComp Outcome, ∀ o, (Pr[= o | c]).toReal = 0 → Pr[= o | c] = 0 :=
    fun c o h0 => ((ENNReal.toReal_eq_zero_iff _).1 h0).resolve_right probOutput_ne_top
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, hα, hf, ?_, ?_⟩
  · simp only [G]
    rw [gG.1 _ (by decide), Fintype.sum_unique, htest, hB0, dG.1]
    simp [catG, hq, h4]
    norm_num
  · simp only [G]
    rw [gG.1 _ (by decide), Fintype.sum_unique, htest, hB0, dG.2.1]
    simp [caughtG, hq, h4]
    norm_num
  · simp only [G]
    rw [gG.2, Fintype.sum_unique, htest, hB0]
    simp
    norm_num
  · apply hne
    simp only [G]
    rw [gG.1 _ (by decide), Fintype.sum_unique, htest, hB0, dG.2.2.1]
    simp [haltP, hq, h4]
  · apply hne
    simp only [G]
    rw [gG.1 _ (by decide), Fintype.sum_unique, htest, hB0, dG.2.2.2.1]
    simp [complG, hq, h4]
  · exact hH.2.2.1
  · exact hH.2.2.2.1
  · rw [show (5 / 32 : ℝ) = 1 - 27 / 32 by norm_num]
    exact hH.2.2.2.2
  · rw [show (27 / 512 : ℝ) = 27 / 32 * (1 - 15 / 16) by norm_num]
    exact hH.2.1
  · rw [show (405 / 512 : ℝ) = 27 / 32 * (15 / 16) by norm_num]
    exact hH.1
  · rw [show (27 / 128 : ℝ) = 27 / 32 * (1 / 4 + if 0 < 1 then (1 - 1) * (1 - 1 / 4) else 0) by norm_num]
    exact hP.1
  · rw [hB2]
    norm_num

end ControlStack.OutcomeGame

