/-
Monotone audit-then-defer bridge: lower bounds on audit recall, halt hazard and
service catch rate give an upper bound on the operational catastrophe
probability by the ledger recursion `catV`.
-/
import ControlStack.DeferGame

open OracleComp

namespace ControlStack.DeferGame
open ControlStack.Refine

theorem catVE_toReal_le_catV {X Z : Type} [Fintype X] [Fintype Z]
    (Bad : X → Prop) [DecidablePred Bad]
    (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool)
    (Halt : Hist X Z → X → Z → ProbComp Bool)
    (Svc : Hist X Z → X → Z → ProbComp Bool) (b : ℕ) (r η : ℝ)
    (a : Service X Z)
    (hA : ∀ h x z, Bad x → r ≤ (Pr[= true | A h x z]).toReal)
    (hH : ∀ h x z, η ≤ (Pr[= true | Halt h x z]).toReal)
    (hS : ∀ h x z, Bad x → a h x z ≤ (Pr[= true | Svc h x z]).toReal) :
    ∀ n u h, (catVE Bad π M D A Halt Svc b n u h).toReal ≤
      catV Bad (fun x z => (Pr[= z | M x]).toReal)
        (fun z => (Pr[= true | D z]).toReal)
        (fun h x => (Pr[= x | π h]).toReal) r η a b n u h := by
  intro n
  induction n with
  | zero => intro u h; simp [catVE, catV]
  | succ n ih =>
    intro u h
    simp only [catVE, catV]
    rw [ENNReal.toReal_sum (fun x _ => ENNReal.mul_ne_top probOutput_ne_top
      (catVE_inner_ne_top Bad π M D A Halt Svc b n u h x))]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_sum (fun z _ => ENNReal.mul_ne_top
      probOutput_ne_top (catVE_transition_ne_top Bad π M D A Halt Svc b n u h x z))]
    refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
    refine Finset.sum_le_sum fun z _ => ?_
    have htr := catVE_transition_ne_top Bad π M D A Halt Svc b n u h x z
    rcases ENNReal.add_ne_top.mp htr with ⟨hpass, hfail⟩
    rw [ENNReal.toReal_mul, ENNReal.toReal_add hpass hfail,
      ENNReal.toReal_mul, ENNReal.toReal_mul]
    refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
    have hnn : ∀ k v g, 0 ≤ (catVE Bad π M D A Halt Svc b k v g).toReal :=
      fun _ _ _ => ENNReal.toReal_nonneg
    have hle1 : ∀ c : ProbComp Bool, (Pr[= true | c]).toReal ≤ 1 := fun c => by
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top (probOutput_le_one (mx := c) (x := true))
    have hD1 := hle1 (D z)
    by_cases hx : Bad x <;> by_cases hu : u < b <;>
      simp only [hx, hu, if_true, if_false, ENNReal.toReal_one, ENNReal.toReal_mul,
        ControlStack.Refine.probOutput_false_toReal]
    · exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (by linarith [hA h x z hx]) (sub_nonneg.2 hD1))
    · refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (sub_nonneg.2 hD1))
      have h1 : 1 - (Pr[= true | Halt h x z]).toReal ≤ 1 - η := by linarith [hH h x z]
      have h2 : 1 - (Pr[= true | Svc h x z]).toReal ≤ 1 - a h x z := by linarith [hS h x z hx]
      have h1n : 0 ≤ 1 - (Pr[= true | Halt h x z]).toReal := sub_nonneg.2 (hle1 _)
      have h2n : 0 ≤ 1 - (Pr[= true | Svc h x z]).toReal := sub_nonneg.2 (hle1 _)
      exact mul_le_mul (mul_le_mul h1 h2 h2n (le_trans h1n h1)) (ih _ _) (hnn _ _ _)
        (mul_nonneg (le_trans h1n h1) (le_trans h2n h2))
    · exact add_le_add (mul_le_mul_of_nonneg_left (ih _ _) ENNReal.toReal_nonneg)
        (mul_le_mul_of_nonneg_left (ih _ _) (sub_nonneg.2 hD1))
    · have h1 : 1 - (Pr[= true | Halt h x z]).toReal ≤ 1 - η := by linarith [hH h x z]
      have h1n : 0 ≤ 1 - (Pr[= true | Halt h x z]).toReal := sub_nonneg.2 (hle1 _)
      refine add_le_add (mul_le_mul_of_nonneg_left (ih _ _) ENNReal.toReal_nonneg)
        (mul_le_mul_of_nonneg_left ?_ (sub_nonneg.2 hD1))
      simpa using mul_le_mul h1 (ih u (h ++ [(x, z, false)])) (hnn _ _ _) (le_trans h1n h1)

/-- **Monotone defer bridge.** If audit recall is at least `r` on bad submissions,
the halt hazard is at least `η`, and the trusted service catches each bad
submission with probability at least `a h x z`, then the operational
catastrophe probability is at most the ledger recursion `catV` with those
parameters. Unlike `defer_bridge`, this needs only lower bounds, so it is a
usable safety guarantee. -/
def DeferMonoClaim : Prop :=
  ∀ {X Z : Type} [Fintype X] [Fintype Z]
    (Bad : X → Prop) [DecidablePred Bad]
    (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool)
    (Halt : Hist X Z → X → Z → ProbComp Bool)
    (Svc : Hist X Z → X → Z → ProbComp Bool) (b : ℕ) (r η : ℝ)
    (a : Service X Z)
    (hA : ∀ h x z, Bad x → r ≤ (Pr[= true | A h x z]).toReal)
    (hH : ∀ h x z, η ≤ (Pr[= true | Halt h x z]).toReal)
    (hS : ∀ h x z, Bad x → a h x z ≤ (Pr[= true | Svc h x z]).toReal),
    ∀ n u h, (Pr[= true | deployV Bad π M D A Halt Svc b n u h]).toReal ≤
      catV Bad (fun x z => (Pr[= z | M x]).toReal)
        (fun z => (Pr[= true | D z]).toReal)
        (fun h x => (Pr[= x | π h]).toReal) r η a b n u h

theorem defer_mono : DeferMonoClaim := by
  intro X Z _ _ Bad _ π M D A Halt Svc b r η a hA hH hS n u h
  rw [deployV_eq_catVE]
  exact catVE_toReal_le_catV Bad π M D A Halt Svc b r η a hA hH hS n u h


#print axioms defer_mono

end ControlStack.DeferGame
