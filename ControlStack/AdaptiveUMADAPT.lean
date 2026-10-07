import ControlStack.AdaptiveGeneric
import Mathlib.Tactic

/-! Integration interface for the adaptive collusion theorem. The definitions
below have the same recursions as PL_UMADAPTF1.adSurv and classRule; this module
keeps the sharp combinatorial argument independently importable in this Lake project. -/

namespace ControlStack.AdaptiveUMADAPT

open ControlStack.AdaptiveGeneric

noncomputable def adSurv {X Z : Type} [Fintype X] [Fintype Z]
    (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (φ : Z → ℝ)
    (keep : Hist X Z → ℝ) : ℕ → Hist X Z → ℝ :=
  passSurv T M φ keep

def classRule {X C Z : Type} [DecidableEq C]
    (c : X → C) (g : Z → C) (t : ℝ) (x : X) (z : Z) : ℝ :=
  classPass c g t x z

theorem adSurv_reference_eq {X Z : Type} [Fintype X] [Fintype Z]
    (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (keep : Hist X Z → ℝ) :
    ∀ n h, refSurv T M keep n h = adSurv T M (fun _ => 0) keep n h := by
  intro n h
  exact refSurv_eq_passSurv_zero T M keep n h

theorem accepts_all_flag_reference {X Z : Type} [Fintype X] [Fintype Z]
    (T : Hist X Z → X → ℝ) (M : X → Z → ℝ) (keep : Hist X Z → ℝ) (n : ℕ)
    (hacc : adSurv T M (fun _ => 0) keep n [] = 1) :
    refSurv T M keep n [] = 1 := by
  rw [adSurv_reference_eq]
  exact hacc

/-- Uniform-seed sharp converse with the contract written in the same
all-FLAG survival form as AcceptsAllFlag. `cat i ≥ t` is the deployment lower
bound supplied by the protocol/colluder lemma. -/
theorem sharp_uniform_seed_risk {X C Z : Type} [DecidableEq C]
    [Fintype X] [Fintype Z] {k : ℕ}
    (S : Finset X) (e : Fin k ≃ {x // x ∈ S})
    (c : X → C) (g : Z → C)
    (hinjS : Set.InjOn c (S : Set X))
    (T : Hist X Z → X → ℝ) (M : X → Z → ℝ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (keep : Hist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h)
    (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z)
    (hkpos : 0 < k) (n : ℕ)
    (hacc : adSurv T M (fun _ => 0) keep n [] = 1)
    (cat : Fin k → ℝ) (hcat : ∀ i, t ≤ cat i) :
    (t / (k : ℝ)) * balancedTarget k n (1-t) ≤
      (1 / (k : ℝ)) * ∑ i : Fin k,
        adSurv T M (classRule c g t ((e i).val)) keep n [] * cat i := by
  have href : refSurv T M keep n [] = 1 :=
    accepts_all_flag_reference T M keep n hacc
  have h := sharp_seedset_catRisk S e c g hinjS T M t ht0 ht1 keep hk hT hM
    hkpos n href cat hcat
  change (t / (k : ℝ)) * balancedTarget k n (1-t) ≤
    (1 / (k : ℝ)) * ∑ i : Fin k,
      passSurv T M (classPass c g t ((e i).val)) keep n [] * cat i
  exact h

noncomputable def seedLawModel {X : Type} [DecidableEq X]
    (S : Finset X) (x : X) : ℝ := if x ∈ S then 1 / (S.card : ℝ) else 0

noncomputable def protocolCatModel {X : Type} [Fintype X] [DecidableEq X]
    (S : Finset X) (surv cat : X → ℝ) : ℝ :=
  ∑ x, seedLawModel S x * surv x * cat x

theorem protocolCatModel_eq {X : Type} [Fintype X] [DecidableEq X]
    (S : Finset X) (surv cat : X → ℝ) :
    protocolCatModel S surv cat =
      (1 / (S.card : ℝ)) * ∑ x : {x // x ∈ S}, surv x.val * cat x.val := by
  classical
  unfold protocolCatModel seedLawModel
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_mem_eq]
  calc
    (∑ x ∈ S, 1 / (S.card : ℝ) * surv x * cat x) =
        ∑ x ∈ S, (1 / (S.card : ℝ)) * (surv x * cat x) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = (1 / (S.card : ℝ)) * ∑ x ∈ S, surv x * cat x := by rw [Finset.mul_sum]
    _ = (1 / (S.card : ℝ)) * ∑ x : {x // x ∈ S}, surv x.val * cat x.val := by
      congr 1
      exact Finset.sum_subtype (s := S) (h := fun _ => Iff.rfl)
        (f := fun x => surv x * cat x)

theorem sum_finEquiv_eq_sum_seed {X : Type} {k : ℕ} (S : Finset X)
    (e : Fin k ≃ {x // x ∈ S}) (f : {x // x ∈ S} → ℝ) :
    (∑ i : Fin k, f (e i)) = ∑ x : {x // x ∈ S}, f x := e.sum_comp f

theorem sharp_uniform_adProtocolCatModel {X C Z : Type} [DecidableEq C]
    [Fintype X] [Fintype Z] [DecidableEq X] {k : ℕ}
    (S : Finset X) (e : Fin k ≃ {x // x ∈ S})
    (c : X → C) (g : Z → C)
    (hinjS : Set.InjOn c (S : Set X))
    (T : Hist X Z → X → ℝ) (M : X → Z → ℝ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (keep : Hist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h)
    (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z)
    (hkpos : 0 < k) (n : ℕ)
    (hacc : adSurv T M (fun _ => 0) keep n [] = 1)
    (cat : X → ℝ) (hcat : ∀ x ∈ S, t ≤ cat x) :
    (t / (k : ℝ)) * balancedTarget k n (1-t) ≤
      protocolCatModel S
        (fun x => adSurv T M (classRule c g t x) keep n []) cat := by
  let catI : Fin k → ℝ := fun i => cat (e i).val
  have hcatI : ∀ i, t ≤ catI i := fun i => hcat (e i).val (e i).property
  have hbound := sharp_uniform_seed_risk S e c g hinjS T M t ht0 ht1 keep hk hT hM
    hkpos n hacc catI hcatI
  have hreindex : (∑ i : Fin k,
      passSurv T M (classPass c g t ((e i).val)) keep n [] * catI i) =
      ∑ x : {x // x ∈ S},
        passSurv T M (classPass c g t x.val) keep n [] * cat x.val := by
    exact e.sum_comp (fun x : {x // x ∈ S} =>
      passSurv T M (classPass c g t x.val) keep n [] * cat x.val)
  have hmodel := protocolCatModel_eq S
    (fun x => passSurv T M (classPass c g t x) keep n []) cat
  have hkcard : S.card = k := by
    have hc := Fintype.card_congr e
    simpa using hc.symm
  have hkcast : (S.card : ℝ) = (k : ℝ) := by exact_mod_cast hkcard
  rw [hkcast] at hmodel
  change (t / (k : ℝ)) * balancedTarget k n (1-t) ≤
    (1 / (k : ℝ)) * ∑ i : Fin k,
      passSurv T M (classPass c g t ((e i).val)) keep n [] * catI i at hbound
  rw [hreindex] at hbound
  change (t / (k : ℝ)) * balancedTarget k n (1-t) ≤
    protocolCatModel S
      (fun x => passSurv T M (classPass c g t x) keep n []) cat
  calc
    (t / (k : ℝ)) * balancedTarget k n (1-t) ≤
        (1 / (k : ℝ)) * ∑ x : {x // x ∈ S},
          passSurv T M (classPass c g t x.val) keep n [] * cat x.val := hbound
    _ = protocolCatModel S
        (fun x => passSurv T M (classPass c g t x) keep n []) cat := hmodel.symm

end ControlStack.AdaptiveUMADAPT
