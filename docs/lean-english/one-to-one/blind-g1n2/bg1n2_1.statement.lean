open scoped BigOperators
open ControlStack.Covert ControlStack.SideChannel ControlStack.ScenarioARepair
  ControlStack.ScenarioAUsefulness ControlStack.LifetimeLedger ControlStack.GatewayCore
namespace PL_bg1n2_1

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

def FrozenBack : Prop :=
  (∀ (Ω S O : Type) [Fintype Ω] [Fintype S] [Fintype O]
      (rho : Ω → ℝ) (W : S → O → ℝ)
      (enc : Ω → Fin (2 ^ 32) → ControlStack.ScenarioARepair.Transcript × S → ℝ)
      (dec : Ω → ControlStack.ScenarioARepair.Transcript × O → Fin (2 ^ 32) → ℝ)
      (c : O → ℝ),
    ControlStack.Covert.IsDist rho →
    (∀ omega m, ControlStack.Covert.IsDist (enc omega m)) →
    (∀ omega y, ControlStack.Covert.IsDist (dec omega y)) →
    (∀ o, 0 ≤ c o) →
    (∀ s o, W s o ≤ c o) →
    (∑ o, c o) ≤ (65536 : ℝ) / 59049 →
    ControlStack.SideChannel.sideSuccess rho W enc dec ≤ (1 : ℝ) / 2 ^ 16) ∧
  (∀ p : ℝ, 0 ≤ p → p ≤ (9 : ℝ) / 10 →
    ControlStack.ScenarioAUsefulness.passProb p ≤ (1 : ℝ) / 80) ∧
  (ControlStack.ScenarioAUsefulness.tail 64 ((93382 : ℝ) / 100000) ≤ (1 : ℝ) / 80 ∧
    (9 : ℝ) / 10 ≤ (93382 : ℝ) / 100000) ∧
  (ControlStack.GatewayCore.viewSpace (C := 1) (fun _ => 1) (fun _ => 8) = 9 ∧
    Fintype.card ControlStack.ScenarioARepair.Transcript = 9 ^ 5) ∧
  (∀ (L : Type) [DecidableEq L] (tr : List (ControlStack.LifetimeLedger.Ev L)),
    (∀ e ∈ tr, ¬ ControlStack.LifetimeLedger.Ev.isRestore e) →
    (∀ ell k, ControlStack.LifetimeLedger.Ev.charge ell k ∈ tr → k = 9) →
    ∀ ell : L,
      (((ControlStack.LifetimeLedger.run (2 ^ 16)
        (some (fun _ : L => 1), []) tr).2).filter (fun a => a.1 = ell)).length ≤ 5)


def Original : Prop :=

    (∀ {Ω S O : Type} [Fintype Ω] [Fintype S] [Fintype O] (ρ : Ω → ℝ) (W : S → O → ℝ) (c : O → ℝ),
      (∀ s o, W s o ≤ c o) → (∀ o, 0 ≤ c o) → ∑ o, c o ≤ 65536 / 59049 →
      ∀ (enc : Ω → Fin (2 ^ 32) → Transcript × S → ℝ) (dec : Ω → Transcript × O → Fin (2 ^ 32) → ℝ),
      IsDist ρ → (∀ ω m, IsDist (enc ω m)) → (∀ ω y, IsDist (dec ω y)) →
      sideSuccess ρ W enc dec ≤ 1 / 2 ^ 16) ∧
    (∀ p : ℝ, 0 ≤ p → p ≤ 9 / 10 → passProb p ≤ 1 / 80) ∧
    (tail 64 (93382 / 100000) ≤ 1 / 80 ∧ (9 : ℝ) / 10 ≤ 93382 / 100000) ∧
    (viewSpace (C := 1) (fun _ => 1) (fun _ => 8) = 9 ∧ Fintype.card Transcript = 9 ^ 5) ∧
    (∀ {L : Type} [DecidableEq L] (es : List (Ev L)), (∀ e ∈ es, ¬ e.isRestore) →
      (∀ e ∈ es, ∀ ℓ k, e = .charge ℓ k → k = 9) →
      ∀ ℓ, ((run (2 ^ 16) (some (fun _ => 1), []) es).2.filter (fun a => a.1 = ℓ)).length ≤ 5)

noncomputable def delta {A : Type} [Fintype A] [DecidableEq A] (a : A) : A → ℝ :=
  fun x => if x = a then 1 else 0

def SideHyp (Ω S O : Type) [Fintype Ω] [Fintype S] [Fintype O]
    (rho : Ω → ℝ) (W : S → O → ℝ)
    (enc : Ω → Fin (2 ^ 32) → Transcript × S → ℝ)
    (dec : Ω → Transcript × O → Fin (2 ^ 32) → ℝ) (c : O → ℝ) : Prop :=
  IsDist rho ∧ (∀ omega m, IsDist (enc omega m)) ∧
  (∀ omega y, IsDist (dec omega y)) ∧ (∀ o, 0 ≤ c o) ∧
  (∀ s o, W s o ≤ c o) ∧ (∑ o, c o) ≤ (65536 : ℝ) / 59049

def OrigSideHyp (Ω S O : Type) [Fintype Ω] [Fintype S] [Fintype O]
    (rho : Ω → ℝ) (W : S → O → ℝ)
    (enc : Ω → Fin (2 ^ 32) → Transcript × S → ℝ)
    (dec : Ω → Transcript × O → Fin (2 ^ 32) → ℝ) (c : O → ℝ) : Prop :=
  (∀ s o, W s o ≤ c o) ∧ (∀ o, 0 ≤ c o) ∧ (∑ o, c o) ≤ (65536 : ℝ) / 59049 ∧
  IsDist rho ∧ (∀ omega m, IsDist (enc omega m)) ∧ (∀ omega y, IsDist (dec omega y))

def LedgerHyp (L : Type) [DecidableEq L] (tr : List (ControlStack.LifetimeLedger.Ev L)) : Prop :=
  (∀ e ∈ tr, ¬ e.isRestore) ∧ (∀ ell k, ControlStack.LifetimeLedger.Ev.charge ell k ∈ tr → k = 9)

def OrigLedgerHyp (L : Type) [DecidableEq L] (tr : List (ControlStack.LifetimeLedger.Ev L)) : Prop :=
  (∀ e ∈ tr, ¬ e.isRestore) ∧ (∀ e ∈ tr, ∀ ell k, e = .charge ell k → k = 9)

def Claim : Prop :=
  (∀ (Ω S O : Type) [Fintype Ω] [Fintype S] [Fintype O]
      (rho : Ω → ℝ) (W : S → O → ℝ)
      (enc : Ω → Fin (2 ^ 32) → Transcript × S → ℝ)
      (dec : Ω → Transcript × O → Fin (2 ^ 32) → ℝ) (c : O → ℝ),
    (SideHyp Ω S O rho W enc dec c ↔ OrigSideHyp Ω S O rho W enc dec c) ∧
    ((sideSuccess rho W enc dec ≤ (1 : ℝ) / 2 ^ 16) ↔
     (sideSuccess rho W enc dec ≤ (1 : ℝ) / 2 ^ 16))) ∧
  (∀ p : ℝ, ((0 ≤ p ∧ p ≤ (9 : ℝ) / 10) ↔ (0 ≤ p ∧ p ≤ (9 : ℝ) / 10)) ∧
    ((passProb p ≤ (1 : ℝ) / 80) ↔ (passProb p ≤ (1 : ℝ) / 80))) ∧
  (((tail 64 ((93382 : ℝ) / 100000) ≤ (1 : ℝ) / 80 ∧ (9 : ℝ) / 10 ≤ 93382 / 100000) ∧
      (viewSpace (C := 1) (fun _ => 1) (fun _ => 8) = 9 ∧ Fintype.card Transcript = 9 ^ 5)) ↔
   ((tail 64 ((93382 : ℝ) / 100000) ≤ (1 : ℝ) / 80 ∧ (9 : ℝ) / 10 ≤ 93382 / 100000) ∧
      (viewSpace (C := 1) (fun _ => 1) (fun _ => 8) = 9 ∧ Fintype.card Transcript = 9 ^ 5))) ∧
  (∀ (L : Type) [DecidableEq L] (tr : List (ControlStack.LifetimeLedger.Ev L)),
    (LedgerHyp L tr ↔ OrigLedgerHyp L tr) ∧
    (∀ ell : L,
      ((((run (2 ^ 16) (some (fun _ : L => 1), []) tr).2).filter (fun a => a.1 = ell)).length ≤ 5 ↔
       (((run (2 ^ 16) (some (fun _ : L => 1), []) tr).2).filter (fun a => a.1 = ell)).length ≤ 5))) ∧
  (FrozenBack ↔ Original)

def Witness : Prop :=
  (∃ (rho : Unit → ℝ) (enc : Unit → Fin (2 ^ 32) → Transcript × Unit → ℝ)
      (dec : Unit → Transcript × Unit → Fin (2 ^ 32) → ℝ),
    SideHyp Unit Unit Unit rho (fun _ _ => 1) enc dec (fun _ => 1)) ∧
  (0 ≤ (9 : ℝ) / 10 ∧ (9 : ℝ) / 10 ≤ (9 : ℝ) / 10) ∧
  LedgerHyp Unit (List.replicate 5 (.charge () 9)) ∧
  ((run (2 ^ 16) (some (fun _ : Unit => 1), []) (List.replicate 5 (.charge () 9))).2.filter (fun a => a.1 = ())).length = 5

end PL_bg1n2_1
