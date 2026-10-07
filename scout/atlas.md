# Scout report: Atlas repos (A: ai-safety-formalization-atlas, B: CapacityAtlas)

Scouted 2026-10-07, read-only (gh api tree + raw.githubusercontent.com; nothing cloned or built).
Target: Lean 4.35.0-rc3, Mathlib v4.35.0-rc3 (the ledger's Mathlib project; see `ledger-check/`).

## 0. Bottom line

* NEITHER repo contains total variation, hockey-stick / f-divergence, distinguishing advantage,
  statistical indistinguishability, TV data processing, or a security-game composition theorem.
  Code search and greps over all files fetched for: totalVariation, tvDist, hockey, hellinger, fDiv,
  advantage (A: only unrelated hits), distinguisher, Pinsker -> nothing relevant.
* Local Mathlib also has no TV / hockey-stick / f-divergence / Pinsker. It has KL (`klDiv`) with kernel DPI
  and a Bayes-risk DPI (details in section 3). So the target lemmas (delta_eta, E_P phi <= e^eta E_Q phi + delta,
  TV DPI for kernels) have to be proved by us (or taken from VCVio); these repos do not shortcut them.
* The only reusable pieces found:
  1. A's vendored `AISafetyAtlas/Upstream/Debate/Prob/*` (Reviewer C family-deepmind/debate, Apache-2.0): a
     finsupp-based `Prob` monad with `count f n` (binomial count of Bernoulli trials) and Hoeffding/Chernoff
     bounds. Mathlib-only deps, no sorry. Marginal value (Mathlib now has `ProbabilityTheory.binomial` and a
     sub-Gaussian Hoeffding already).
  2. B's `CapacityAtlasForMathlib` finite-distribution/finite-channel kernel (real-valued `FiniteDistribution`,
     `FiniteChannel`, `comp`, `deterministic`, `map`, `mixture`, PMF equiv). ~300 lines of elementary
     plumbing; useful as a pattern, not as a dependency. We can write the same in 30-60 lines.
* Recommendation: do NOT depend on or vendor either repo. At most crib the 3 small items in section 5.

---

## 1. Repo A: mbrcic/ai-safety-formalization-atlas

### 1.1 Toolchain / deps / licence
* lean-toolchain: `leanprover/lean4:v4.33.0`. lakefile.toml: `warningAsError = true`; `[[require]] mathlib rev = "v4.33.0"`
  (resolved db584cd6d46c92f209a44c0f1c829460d327499d).
* Other requires (lake-manifest): Foundation (FormalizedFormalLogic @30a16ff), PFR (teorth/pfr @7d6404b),
  Causalean (Jiyuan-Tan/CausalSmith @e298f64, brings optlib, FoML/lean-rademacher), add-combi, plus vendored
  `vendor/TauCeti`, `vendor/SocialChoiceLean`. Very heavy dependency closure.
* All source uses the Lean module system: first line `module`, `public import ...`, `@[expose] public def`.
* Licence: Apache-2.0. Root `LICENSE` is the standard Apache text (11357 bytes, confirmed "Apache License Version 2.0").
  No per-file `Copyright` headers in AISafetyAtlas/* (grep for "Copyright": none). Vendored subtrees keep upstream
  attribution; `AISafetyAtlas/Upstream/LICENSE-NOTICE` lists them: Debate (Reviewer C family-deepmind/debate via LukaHobor/debate
  port-lean-4.31, Apache-2.0), KolmogorovMathlib (Apache-2.0), Attribution (Apache-2.0), GibbardSatterthwaite (MIT),
  LinearSystems and Analysis/Blackwell (Apache-2.0, adapted, per-file headers).
* sorry/axiom/native_decide: none in any file I fetched (counted: DataProcessing, ChannelCapacity, Determinism,
  OversightBudget, ChannelRate, InformationLimits, PolicyKernel, Check, Audit, JointObservation*, VarietyBound,
  all Upstream/Debate/Prob/*). (A grep hit in Knowledge/Ambiguity.lean line 56 is a docstring mentioning "axioms".)

### 1.2 Declarations relevant (or nearly relevant) to our targets

A. InformationTheory (path: AISafetyAtlas/InformationTheory/)
* `DataProcessing.lean` (imports only `PFR.ForMathlib.Entropy.Basic`). MUTUAL-INFORMATION data processing, not TV.
  ```
  @[expose] public def IsMarkovChain (X : Ω → S) (Y : Ω → T) (Z : Ω → U)
      (μ : Measure Ω) : Prop :=
    CondIndepFun X Z Y μ

  public theorem mutualInfo_le_of_isMarkovChain (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
      (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
      [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
      (h : IsMarkovChain X Y Z μ) :
      I[X : Z ; μ] ≤ I[X : Y ; μ]

  public theorem mutualInfo_comp_le (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
      (hX : Measurable X) (hY : Measurable Y) {g : T → U} (hg : Measurable g)
      [FiniteRange X] [FiniteRange Y] :
      I[X : g ∘ Y ; μ] ≤ I[X : Y ; μ]
  ```
  Other: `mutualInfo_chain_rule`, `mutualInfo_chain_rule'`, `mutualInfo_chain_rule_fin`, `mutualInfo_sub_eq`,
  `isMarkovChain_iff_measure_factorizes(_singleton)`, `isMarkovChain_comp`, `condMutualInfo_le_mutualInfo`.
  Note: header says PFR already has the functional DPIs; the module adds chain rules + Markov form.
* `ChannelCapacity.lean` (imports Mathlib only; trivial):
  ```
  @[expose] public noncomputable def channelCapacity (O : Type*) [Fintype O] : ℝ :=
    Real.log (Fintype.card O)
  public theorem channelCapacity_prod (O₁ O₂ : Type*) [Fintype O₁] [Fintype O₂]
      [Nonempty O₁] [Nonempty O₂] :
      channelCapacity (O₁ × O₂) = channelCapacity O₁ + channelCapacity O₂
  ```
  "Capacity" here is just log of alphabet size (noiseless ceiling). Plus `channelCapacity_fun`,
  `channelCapacity_le_of_card_le`, `channelCapacity_eq_of_card_eq_pow`.
* `Determinism.lean`: `condEntropy_comp_self_left : H[g ∘ X | X ; μ] = 0`. Entropy, PFR-based.
* `Fano.lean`, `PrefixCode.lean` also present (not fetched in detail).

B. Control (path: AISafetyAtlas/Control/)
* `OversightBudget.lean` (215 lines, imports Control.InformationLimits, Control.OpenLoop). Three theorems, each a
  1-4 line corollary of `entropyReduction_le_openLoopMax` (Touchette-Lloyd):
  ```
  public structure Oversight (Ω : Type uΩ) (S : Type uS) (K : Type uK) (T : Type uT) where
    hazard : Ω → S
    reading : Ω → K
    outcome : Ω → T

  public theorem oversight_reduction_le_budget [IsProbabilityMeasure μ] [Fintype S]
      {F : S → K → N → T} {Z : Ω → N}
      (hhaz : Measurable O.hazard) (hread : Measurable O.reading) (hZ : Measurable Z)
      [FiniteRange O.hazard] [FiniteRange O.reading] [FiniteRange O.outcome]
      (hplant : IsPlant F O.hazard O.reading Z O.outcome)
      (hindep : IndepFun (⟨O.hazard, O.reading⟩ : Ω → S × K) Z μ) :
      entropyReduction μ O.hazard O.outcome
        ≤ openLoopMax F (μ.map Z) + I[O.hazard : O.reading ; μ]
  ```
  plus `blind_channel_buys_nothing` (I = 0 => bound collapses to openLoopMax) and
  `budget_is_the_channel_not_the_volume`. This is "reduction in entropy of a physical control loop <= open-loop term +
  I(hazard;reading)". It is an entropy statement about a plant `F : S → K → N → T` with independent noise; it says nothing
  about adversarial policies, mediators, honeypots, TV or pass rules. The docstring itself says "The atlas has no
  monitoring stack, no telemetry and no incident."
* `InformationLimits.lean` (735 lines, imports DataProcessing): the substantive math.
  ```
  @[expose] public noncomputable def controlLoss (μ : Measure Ω) (X : Ω → S) (C : Ω → K) (X' : Ω → T) : ℝ :=
    H[X' | ⟨X, C⟩ ; μ]
  @[expose] public noncomputable def entropyReduction (μ : Measure Ω) (X : Ω → S) (X' : Ω → T) : ℝ :=
    H[X ; μ] - H[X' ; μ]
  ```
  `entropy_noise_sub_controlLoss`, `controlLoss_le_entropy_noise`, `controlLoss_eq_condMutualInfo`,
  `condEntropy_ge_of_openLoopBound`, `entropyReduction_le_of_openLoopBound`, `minControlLoss_*`. Touchette-Lloyd "information
  limits of control", entropy only.
* `ChannelRate.lean` (339 lines, imports RequisiteVariety, DataProcessing): `chainRate`, `traj`, `entropy_traj`,
  `ashbyCapacity` (rate * stepDuration), `chainRate_eq_condEntropy`, `entropy_outcome_ge_sub_chainEntropy`. Entropy rates
  of Markov-chain trajectories; Ashby requisite-variety flavour.
* `RequisiteVariety.lean`, `VarietyCounting.lean`, `PolicyKernel.lean` (720 lines: policy kernels, imports
  Mathlib.Probability.Kernel.Composition.MeasureCompProd), `Purification.lean`, `OpenLoop.lean`: all entropy/variety.

C. Knowledge / indistinguishability (path: AISafetyAtlas/Knowledge.lean)
  DETERMINISTIC notion only (observation function collisions), not statistical:
  ```
  @[expose] public def Knowable {Ω : Sort u} {I : Sort v} {Y : Sort w}
      (observation : Ω → I) (property : Ω → Y) : Prop :=
    ∃ decoder : I → Y, ∀ ω, property ω = decoder (observation ω)
  public structure IndistinguishabilityWitness ... (observation : Ω → I) (property : Ω → Y) where
    left : Ω; right : Ω; ...
  public theorem knowable_iff_no_collision {Ω : Sort u} {I : Sort v} {Y : Sort w}
      [Nonempty Y] (observation : Ω → I) (property : Ω → Y) :
      Knowable observation property ↔
        ∀ ω τ, observation ω = observation τ → property ω = property τ
  ```
  = `Function.FactorsThrough` repackaged. Also `Determines`, `Knowable.mono`, `not_knowable_comp`, `knowable_id_iff_injective`.
  `Knowledge/Check.lean` (`findCollision`, decidable instances) = executable finite checker for the same.

D. Oversight/JointObservation (path: AISafetyAtlas/Oversight/JointObservation/*): `Covers q h` is
  definitionally `Knowledge.Knowable q.observe h`; `covers_iff_no_collision`; finite `CollisionWitness`; Portfolio / Residual /
  Registry / RepairBoundary. Combinatorial, deterministic, no probability.

E. Compositional (AISafetyAtlas/Compositional/*): hyperproperties, trace systems, network traces, rectangularity,
  symmetry, local contract boundary. Trace-set/topological, non-probabilistic. No composition theorem for advantage/TV.

F. Binomial / tails: the vendored Debate `Prob` library (section 1.3). Also `Combinatorics/Cascade*.lean` and
  `Learning/Sharp.lean` mention "binomial" (combinatorial/learning-theory contexts, not fetched).

### 1.3 Best candidate slices (A)

SLICE A1: `AISafetyAtlas/Upstream/Debate/Prob/{Defs,Basics,Arith,Bernoulli,Estimate,Chernoff}.lean`
(+ `Misc/{Finset,If}.lean`; `Cond.lean`, `Pmf.lean` optional bridge).
* Import closure inside repo: Chernoff -> Bernoulli, Estimate; Bernoulli, Estimate -> Arith -> Basics, Misc.If;
  Basics -> Defs -> Misc.Finset. Pmf.lean additionally -> Mathlib PMF modules. Nothing outside `Upstream/Debate/{Prob,Misc}`.
* Mathlib imports (all confirmed present in local Mathlib 4.35.0-rc3): Mathlib.Algebra.BigOperators.Finsupp.Basic,
  Tactic.Cases, Data.Finsupp.{SMul,Basic,Notation}, Analysis.Calculus.{Taylor,Deriv.Inv}, Analysis.SpecialFunctions.{Log.Deriv,Pow.Real},
  (Pmf.lean: Probability.ProbabilityMassFunction.{Basic,Integrals,Monad}, MeasureTheory.Integral.IntegrableOn).
* Representation: OWN finite-support type, not Mathlib PMF/Measure:
  ```
  structure Prob (α : Type) where
    prob : α →₀ ℝ
    prob_nonneg : ∀ {x}, 0 ≤ prob x
    total : prob.sum (λ _ p ↦ p) = 1
  def Prob.exp (f : Prob α) (g : α → ℝ) : ℝ := f.prob.sum (λ x p ↦ p * g x)
  def Prob.pr (f : Prob α) (p : α → Prop) := f.exp (λ x ↦ if p x then 1 else 0)
  ```
  with `Monad`/`LawfulMonad Prob`, `bernoulli`, `bit`; `Prob.toPmf`/`PMF.toProb` (Pmf.lean) bridge. Note `α : Type` (not `Type*`).
* Key binomial/concentration results (Estimate.lean, Chernoff.lean):
  ```
  def count (f : m Bool) : ℕ → m ℕ          -- distribution of #true in n iid samples (arbitrary Monad m)
  lemma exp_count (f : Prob Bool) (n : ℕ) (t : ℝ) :
      (count f n).exp (λ x ↦ (t*x).exp) = (f.exp (λ x ↦ (t * bif x then 1 else 0).exp)) ^ n
  lemma chernoff_count_le (f : Prob Bool) (n : ℕ) {t : ℝ} (t0 : 0 ≤ t) :
      (count f n).pr (λ x ↦ n * f.prob true + t ≤ x) ≤ (-2 * t^2 / n).exp
  lemma chernoff_le_count (f : Prob Bool) (n : ℕ) {t : ℝ} (t0 : 0 ≤ t) :
      (count f n).pr (λ x ↦ x ≤ n * f.prob true - t) ≤ (-2 * t^2 / n).exp
  lemma chernoff_count_abs_le ... : ... ≤ (2:ℝ) * ((-2:ℝ) * t^2 / n).exp
  lemma hoeffdings_lemma {p : ℝ} (m : p ∈ Icc 0 1) {t : ℝ} (t0 : 0 ≤ t) : ...
  ```
  These are one-sided Hoeffding tail UPPER BOUNDS for Bin(n,p), not exact binomial tail identities. No pmf formula
  `P(count = k) = C(n,k) p^k (1-p)^(n-k)` found in the fetched files.
* sorry/axiom/native_decide: none in Prob/*. Headers say linters are switched off for the vendored files
  (`set_option linter.* false`).
* Port to 4.35.0-rc3 with small edits? Plausible but unverified. Spot-checks against local Mathlib (all OK):
  `Finsupp.notMem_support_iff` (Data/Finsupp/Defs.lean:165), `Real.log_pow` (Log/Basic.lean:288),
  `Fintype.card_prod` (Data/Fintype/Prod.lean:56), `Finset.prod_fiberwise` (to_additive `sum_fiberwise`;
  Algebra/BigOperators/Group/Finset/Basic.lean:282), `induction'` tactic still in Mathlib/Tactic/Cases.lean:75, core
  `Nat.zero_eq` still exists in 4.35.0-rc3 (Init/Data/Nat/Basic.lean:109). Risk: `hoeffdings_lemma` uses `taylor_*`
  / `iteratedDerivWithin` Taylor machinery (Mathlib renames likely); the file already survived 4.8 -> 4.31 -> 4.33
  migrations (Atlas records two proof-script rewrites only in Cost.lean and Details.lean, not Prob).
  Our alternative: Mathlib already has `ProbabilityTheory.binomial (n : ℕ) (p : I) : Measure ℕ`
  (Probability/Distributions/Binomial.lean:57) and Hoeffding `measure_sum_range_ge_le_of_iIndepFun`
  (Probability/Moments/SubGaussian.lean:785), which is the better foundation.
* Verdict: low value. Copy only if we want a Mathlib-light Bernoulli Hoeffding on a custom finite type.

SLICE A2: `Knowledge.lean` + `Knowledge/Check.lean` (deterministic indistinguishability + finite checker).
* Trivial (factorization through observation). Useful only as naming inspiration for a zero-error / content-only notion
  ("content-only kernel" = decoder factoring through the mediated text). Imports Mathlib.Data.Fintype.{Prod,Pi}, and
  Knowledge depends on the Atlas module graph (Sovereignty/Devices for Check). Not worth porting; reprove in 5 lines.

SLICE A3: `InformationTheory/DataProcessing.lean` + `Control/InformationLimits.lean` + `OversightBudget.lean`.
* Hard-depends on PFR (`PFR.ForMathlib.Entropy.Basic`, pinned to mathlib v4.33.0) -> NOT portable by small edits to
  4.35.0-rc3 unless PFR is also bumped. Entropy/MI only; wrong divergence for our hockey-stick bound.
  Not recommended.

### 1.4 Honest assessment of A's control/oversight content
* Real theorems exist, but in their own domains: MI chain rules/DPI, Fano, Touchette-Lloyd control limits, requisite variety,
  singular-learning (Watanabe) chart machinery (hundreds of KB), MAIS conjectures O7/O70/O77, vendored Debate/GS/Arrow.
  The registry/"witness" discipline (Examples/* files) is careful: statements are non-vacuous and audited.
* The control/oversight bridges (OversightBudget, JointObservation, Compositional, Knowledge) are mostly thin:
  3 two-line corollaries of an entropy inequality; deterministic factorization (`Knowable`) repackaged; capacity = log|O|.
  They explicitly decline any "monitoring stack" claim. The Atlas is a catalogue/registry of formal facts with excellent
  provenance hygiene, not a toolbox for probabilistic security games.
* Would it save real work for us? NO for TV/hockey-stick/DPI-for-kernels/content-only kernels/sequential bound.
  Possibly 0.5 day at most for Bernoulli Hoeffding (but Mathlib has it now).

---

## 2. Repo B: TomasOrtega/CapacityAtlas

### 2.1 Toolchain / deps / licence
* `lean/lean-toolchain`: `leanprover/lean4:v4.32.0`; `lean/lakefile.toml`: mathlib `rev = "v4.32.0"` (81a5d257c8e4...), only Mathlib
  (+ its transitive plausible, aesop, batteries, Qq, importGraph, proofwidgets, LeanSearchClient, Cli). Lean options:
  `autoImplicit = false`. `CapacityAtlas` lib has `warn.sorry = false` (registry of open claims); the shared-API lib
  `CapacityAtlasForMathlib` does not.
* Licence: Apache-2.0 for `src/`, `lean/`, etc.; data/docs CC-BY-4.0 (`LICENSES/README.md`). `NOTICE`: "Copyright 2026 The
  Capacity Atlas Authors". Root `LICENSE` (11328 bytes) begins with the standard Apache 2.0 text. `COPYRIGHT`: "Copyright 2026 The
  Capacity Atlas Authors." Per-file header (89 of 98 files in CapacityAtlasForMathlib+Util):
  ```
  /-
  Copyright 2026 The Capacity Atlas Authors
  Licensed under the Apache License, Version 2.0 (the "License").
  See the License for the specific language governing permissions and limitations.
  -/
  ```
  9 files lack it (e.g. Probability/FiniteRange.lean, FunctionProduct.lean, MeasureTheory/Measure/Real.lean, Util/Metadata.lean,
  ArbitrarilyVarying.lean, BinaryEntropyOptimization.lean, BinarySymmetric.lean, BinaryWords.lean, BlockInputInformation.lean).
* CapacityAtlasForMathlib: 98 files, 653 KB (fetched all). sorry / axiom / native_decide: ZERO in all 98 files.
  No hits for total variation, tvDist, hockey, advantage, indistinguish, binomial, Chernoff, Hoeffding.
  Only tail-type content: Chebyshev lower tail (`FiniteProductProbability.lowerTail_mass_le_secondMoment_div_sq`,
  `InformationDensity` Chebyshev estimate, `InputCost/CostTail`).
* Repo content: channel-capacity coding theorems (channel coding converse/direct for DMC, MAC, relay, broadcast, wiretap, feedback,
  Gelfand-Pinsker, index coding, Gaussian), all via mutual information / entropy. Nothing about TV or adversaries.

### 2.2 Declarations (all under lean/CapacityAtlasForMathlib/, namespace `CapacityAtlas`)
All tagged `@[capacity_shared_api]` (an attribute from `CapacityAtlasUtil.Metadata`, which does `import Lean` + `initialize`
attribute registration; must be stripped or vendored to reuse).

* `InformationTheory/FiniteDistribution.lean` (157 lines; imports Util.Metadata, Mathlib BinaryEntropy, Log.Base, Fintype.Order, Tactic):
  ```
  structure FiniteDistribution (X : Type*) [Fintype X] where
    probability : X → ℝ
    nonnegative : ∀ x, 0 ≤ probability x
    sum_probability : ∑ x, probability x = 1
  noncomputable def map [DecidableEq Y] (distribution : FiniteDistribution X) (f : X → Y) : FiniteDistribution Y where
    probability y := ∑ x with f x = y, distribution x   -- pushforward by a deterministic map
  noncomputable def uniform (X : Type*) [Fintype X] [Nonempty X] : FiniteDistribution X
  def bernoulli (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : FiniteDistribution Bool
  ```
  with `FunLike` instance, `ext`, `entropy`, `entropyBits`, `entropy_bernoulli`, `eq_bernoulli`.
* `InformationTheory/FiniteDistribution/PMF.lean` (85 lines; + Mathlib PMF.Constructions): bridge
  `toPMF`, `ofPMF`, `noncomputable def equivPMF (X : Type*) [Fintype X] : FiniteDistribution X ≃ PMF X`,
  `toPMF_map : (distribution.map f).toPMF = distribution.toPMF.map f`.
* `InformationTheory/FiniteChannel.lean` (117 lines; Mathlib BigOperators/Fintype/Real only):
  ```
  structure FiniteChannel (X Y : Type*) [Fintype X] [Fintype Y] where
    transition : X → Y → ℝ
    nonnegative : ∀ x y, 0 ≤ transition x y
    row_sum : ∀ x, ∑ y, transition x y = 1
  def deterministic [DecidableEq Y] (output : X → Y) : FiniteChannel X Y
  def identity (X : Type*) [Fintype X] [DecidableEq X] : FiniteChannel X X
  def comp (V : FiniteChannel Y Z) (W : FiniteChannel X Y) : FiniteChannel X Z where
    transition x z := ∑ y, W.transition x y * V.transition y z
  ```
  This is exactly a Markov kernel on finite types (our mediator M). `FiniteChannel/PMF.lean`: `toPMF`, `toPMF_comp`
  (but that file imports `FiniteChannelCapacity`, heavier).
* `InformationTheory/FiniteMixture.lean` (179 lines; imports FiniteEntropy 27 KB):
  `mixture (weights : FiniteDistribution I) (inputs : I → FiniteDistribution X)`, `mixture_apply`, `atom`, `binaryMixture`
  (t-mixture of two laws: relevant to mixing honeypot law with real law), entropy-concavity lemmas (not needed).
* `InformationTheory/FiniteProductDistribution.lean`, `FiniteProductProbability.lean` (196 lines, self-contained: Metadata + BigOperators
  + Tactic): iid/product mass on `ι → α`, sums of products, and
  ```
  theorem lowerTail_mass_le_secondMoment_div_sq (w f : α → ℝ)
      (hw : ∀ a, 0 ≤ w a) (center δ : ℝ) (hδ : 0 < δ) :
      (∑ a, if f a ≤ center - δ then w a else 0) ≤
        (∑ a, w a * (f a - center) ^ 2) / δ ^ 2
  ```
  (finite Chebyshev). `FiniteProductDistribution.productFamily`, `productFamily_const_eq_iid`, `map_productFamily_eval`.
* `InformationTheory/OutputRelabeling.lean`, `SequentialInformation.lean` (`relabelOutput_mutualInformation`,
  `sequentialExtension_mutualInformation_le_add_capacity`), `FiniteEntropy.lean` (`mutualInformation_le_log_card_output`,
  block MI bounds): MI only. Deterministic-relabeling invariance is for MI/coding error, not TV.
* No `data processing` lemma for any divergence beyond MI/coding; no TV.

### 2.3 Best candidate slices (B)
SLICE B1: `FiniteDistribution.lean` + `FiniteDistribution/PMF.lean` + `FiniteChannel.lean` (about 360 lines).
* Imports inside repo: Util.Metadata (attribute only). Mathlib: BinaryEntropy, Log.Base, Fintype.Order, Tactic, PMF.Constructions,
  BigOperators.
* Representation: own real-valued Fintype structures with explicit PMF equivalence (`equivPMF`); not Mathlib PMF/Measure natively.
* Port to 4.35.0-rc3: very likely trivial (toolchain 4.32 -> 4.35). Spot-check in local Mathlib: all imported modules present
  (BinaryEntropy, Log/Base, Data/Fintype/Order, Tactic, PMF/Constructions); `Real.negMulLog` (Log/NegMulLog.lean:164),
  `PMF.map` (PMF/Constructions.lean:45), `Finset.sum_fiberwise`, `Finset.sum_comm`, `Finset.sum_nonneg` all exist.
  Remaining work: delete `@[capacity_shared_api]` / drop `CapacityAtlasUtil.Metadata` import (or vendor the 4 KB Metadata.lean).
* sorry/axiom/native_decide: none.
* Value: it is the finite Markov-kernel plumbing (pushforward `map`, composition `comp`, `deterministic`) we need for
  "data processing under kernels and deterministic maps"; but the real content (TV / hockey-stick DPI) is NOT there. We would write
  `hockey`/`tv` ourselves either way. Writing our own `structure`/`def` takes <1 hour; the `row_sum` proof for `comp` is ~15 lines.

SLICE B2: `FiniteProductProbability.lean` (self-contained, 196 lines): iid product mass, `mean`, Chebyshev lower tail.
  Marginal; could inform our binomial/iid honeypot-product statement but there are no binomial tail identities.

SLICE B3: `FiniteMixture.lean` `binaryMixture`/`mixture`: depends on FiniteEntropy; skip (reprove mixture in 10 lines).

### 2.4 Honest assessment of B
Clean, well-organised, sorry-free Apache-2.0 Mathlib-only library, but for Shannon-capacity coding theorems. Zero overlap with TV/hockey-stick/
distinguishing advantage. Its finite-distribution kernel is a nice template (and the per-file Apache header + split LICENSES/ is easy to
comply with) but gives no theorem we need. Savings: under half a day of plumbing, none of the hard content.

---

## 3. Local Mathlib (v4.35.0-rc3) survey: what exists

Path prefix: Mathlib/ = the Mathlib v4.35.0-rc3 source tree (`.lake/packages/mathlib/Mathlib/` of the ledger's Mathlib project)

* `InformationTheory/` contains only: Hamming.lean, Coding/{Kraft,KraftMcMillan,PrefixFree,UniquelyDecodable}.lean,
  KullbackLeibler/{Basic,ChainRule,DataProcessing,KLFun}.lean. NO TV, NO hockey-stick, NO f-divergence (`fDiv`), NO Hellinger,
  NO Renyi/chi-squared, NO Pinsker (grep across all of Mathlib: no `tvDist`, `totalVariation` (only signed-measure `Variation/`
  vector-measure total variation in `MeasureTheory/VectorMeasure/Variation/{Defs,Basic,SignedMeasure,Semivariation}.lean`), `Measure.tv`, `fDiv`,
  `hellinger`, `Pinsker`).
* KL with data processing (InformationTheory/KullbackLeibler/DataProcessing.lean):
  ```
  theorem klDiv_map_le (hg : Measurable g) : klDiv (μ.map g) (ν.map g) ≤ klDiv μ ν
  theorem klDiv_trim_le (hm : m ≤ m𝓧) : klDiv (μ.trim hm) (ν.trim hm) ≤ klDiv μ ν
  theorem klDiv_comp_right_le (κ : Kernel 𝓧 𝓨) [IsMarkovKernel κ] :
      klDiv (κ ∘ₘ μ) (κ ∘ₘ ν) ≤ klDiv μ ν
  ```
  plus `klDiv`, `klDiv_self`, `klDiv_eq_lintegral_klFun`, `toReal_klDiv` in KullbackLeibler/Basic.lean; `KLFun.lean` has `klFun`
  (convex generator; the general f-divergence generator pattern but no `fDiv` yet).
* Bayesian risk with DPI (Probability/Decision/Risk/RiskIncrease.lean, authors Degenne, Luccioli; Defs, Basic, Countable):
  `riskIncrease (ℓ : Θ → 𝓨 → ℝ≥0∞) (P : Kernel Θ 𝓧) (π : Measure Θ) : ℝ≥0∞`, `riskIncrease_comp_le`, `riskIncrease_map_le`
  (statistical-information DPI under Markov kernels / measurable maps). With 0-1 loss and two hypotheses this is the TV/Bayes-risk
  link, but it is not packaged as TV or hockey-stick; our own finite proof of the pointwise bound is easier than adapting it.
* Binomial and concentration: `ProbabilityTheory.binomial (n : ℕ) (p : I) : Measure ℕ` (Probability/Distributions/Binomial.lean:57;
  `binomial_singleton`, `binomial_eq_sum_dirac`, `integral_binomial`, `ae_le_of_hasLaw_binomial`);
  Hoeffding in Probability/Moments/SubGaussian.lean:785
  `measure_sum_range_ge_le_of_iIndepFun {X : ℕ → Ω → ℝ} (h_indep : iIndepFun X μ) {c : ℝ≥0} {n : ℕ}
   (h_subG : ∀ i < n, HasSubgaussianMGF (X i) c μ) {ε : ℝ} (hε : 0 ≤ ε) :
   μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, X i ω} ≤ exp (-ε ^ 2 / (2 * n * c))`
  (and `measure_sum_ge_le_of_iIndepFun` at line 778).
* PMF API: Probability/ProbabilityMassFunction/{Basic,Constructions (PMF.map),Monad,Integrals}.lean.

---

## 4. Summary table

| Target | A (Atlas) | B (CapacityAtlas) | Mathlib 4.35.0-rc3 |
|---|---|---|---|
| hockey-stick / f-div | none | none | none (only KL, `klFun`) |
| TV distance | none | none | none (only vector-measure variation) |
| E_P phi <= e^eta E_Q phi + delta | none | none | none |
| DPI under kernels | MI only (PFR-based) | MI only | `klDiv_comp_right_le`, `riskIncrease_comp_le` |
| DPI deterministic map | MI (`mutualInfo_comp_le`) | `FiniteDistribution.map` only (no DPI) | `klDiv_map_le` |
| content-only kernel | `Knowable` (deterministic factorization) | `FiniteChannel.deterministic` | n/a |
| distinguishing advantage | none | none | none |
| binomial tails | Hoeffding on `count` (Debate/Prob) | Chebyshev only | `binomial` measure, sub-Gaussian Hoeffding |
| composition / sequential bound | `channelCapacity_prod` (log card); trace compositions (non-prob.) | `FiniteChannel.comp`, MI sequential bound | `Kernel.comp` |
| toolchain | 4.33.0, PFR/Foundation/Causalean | 4.32.0, Mathlib only | 4.35.0-rc3 |

## 5. What to reuse (if anything)
1. Nothing as a dependency.
2. Optional crib (all Apache-2.0, keep header + attribution if copied): B `FiniteChannel.comp` row_sum proof and `FiniteDistribution.map`
   (`Finset.sum_fiberwise`) as a template for the finite-kernel DPI plumbing.
3. Optional: A `Prob/Chernoff.lean` `chernoff_count_le` pattern if we want a Bernoulli-count Hoeffding on a finsupp type; prefer Mathlib
   `binomial` + sub-Gaussian Hoeffding instead.
4. Real prior art for the missing pieces is outside these repos: VCVio's TV/distinguisher bounds (already in hand), and the in-progress
   Mathlib/TestingLowerBounds f-divergence work (Degenne; `riskIncrease`/`klFun` here are its precursors). Re-check before writing
   `hockeyStick` ourselves.
