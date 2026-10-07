# VCVio source scout (read-only; nothing built or cloned)

Pin: `Verified-zkEVM/VCVio@9146f78c4f1bc2c9d8d92da686e9e375315ae5e7` (committed 2026-10-03, "feat(VCVio): expected charged-query count of a stateful simulation (#817)").
`lean-toolchain` = `leanprover/lean4:v4.34.0`; Mathlib `v4.34.0` (rev 5ed2965256430c3649e86755f9576b54eca72435). Same as ours.
Other pinned deps: PolyFun@3710d71b28404a151b8d1f0ce080ea448778dec0 (-> cslib@990e65a685bed413f43b139db900a36ad5322a10, Mathlib), plus batteries, aesop, Qq, etc.
Everything below is read from source at that commit. "VERIFIED" = statement copied from source; "GUESSED" = not in source, never compiled.

## 0. Bottom line

1. **Two parallel TV stacks.**
   * (a) Legacy SPMF/sum-based `tvDist` on any monad lifting to `SPMF`: `VCVio/EvalDist/TVDist.lean`.
   * (b) Measure-native `Measure.etvDist` = sup over measurable events of `ENNReal.absDiff`: `ToMathlib/MeasureTheory/Measure/TotalVariation.lean`, with bind/kernel lemmas.
   * VCVio's own AGENTS.md (gotcha 10) says PMF/SPMF is a "retiring surface". `evalSPMF`, `probOutput`, `probEvent`, `probFailure`, `EvalDistCompatible` are `@[deprecated]` (since 2026-09-13/17). New code is meant to use `Measure`/`Kernel`/`𝒟[·]`.
   * The two TV notions are bridged only for zero distance (`SPMF.toMeasure_tvDist_eq_zero_iff`) and `PUnit` (`SPMF.toMeasure_tvDist_punit`). There is no general equality theorem.
2. **T1 and data processing already exist, measure-native, with no VCVio-proper dependency.** Import `ToMathlib.Probability.Kernel.TotalVariation` (+ `ToMathlib.MeasureTheory.Measure.Bool`). That is 8 modules, 1039 lines, closure = Mathlib only (no PolyFun, no cslib).
   * T1 for randomised decision rules: `Measure.absDiff_lintegral_le_etvDist`. A decision rule is `D : α → ℝ≥0∞`, measurable, `≤ 1`. It is stated for any measures, no probability hypothesis.
   * Data processing: `Measure.etvDist_map_le` (deterministic map), `Measure.etvDist_bind_le` (subprobability kernel), `Kernel.etvDist_comp_le` (kernel composition).
   * Hybrid-step bad-event lemmas: `etvDist_bind_bind_le_of_bad`, `etvDist_bind_bind_le_add_lintegral`.
3. **Plain Mathlib v4.34.0 has no TV-distance API for `PMF`/`Measure`.** The only "variation" files are `Mathlib/MeasureTheory/VectorMeasure/Variation/*`, which is the signed-measure notion. If we go "plain Mathlib" we must write TV ourselves, or vendor VCVio's `ToMathlib` TV files. They are Apache-2.0, headered, and Mathlib-only: `ToMathlib/Data/ENNReal/AbsDiff.lean` (175 lines), `Measure/TotalVariation.lean` (164), `Measure/TotalVariation/Bind.lean`, `Probability/Kernel/TotalVariation.lean`, and for PMF `Probability/ProbabilityMassFunction/TotalVariation.lean` (220).
4. **`ProbComp` is the wrong carrier for "arbitrary randomised policy".** `OracleComp spec α` is a *finite* free-monad tree (`PFunctor.FreeM`; cslib's "finite free program"). `ProbComp = OracleComp unifSpec` only draws uniform `Fin (n+1)` values, so it has finite support and rational probabilities. "∀ A : α → ProbComp β" quantifies over that class only. A real-valued Bernoulli, or a countable-support policy, is not expressible. For arbitrary adversaries use `Kernel α β` / `α → Measure β` (measure world) or `α → PMF β`. The VCVio payoffs are `do`-notation, `simulateQ`/handler machinery, query bounds, and program logic.
5. **No ready-made N-round "swap real attacks for honeypots one at a time" theorem.** Available building blocks:
   * generic n-term triangle hybrids (`QueryImpl.Stateful.advantage_hybrid`, `IndistAt.hybrid`);
   * the IND-CPA q-query hybrid (`IND_CPA_Advantage_le_mul_of_oneTime_bound`);
   * ε-perturbed identical-until-bad with a query bound (`tvDist_simulateQ_le_queryBound_mul_slack_plus_probEvent_bad`);
   * measure-level bad-event bind lemmas.
   * T3 would be our own induction on top of `Measure.etvDist_triangle` and `etvDist_bind_bind_le_add_lintegral`.
6. **Dependency cost (items below):**
   * measure TV stack: 8 modules;
   * `VCVio.EvalDist.MeasureTVDist.Bind`: 11 modules, no PolyFun;
   * SPMF `tvDist` + `ProbComp`: 69 VCVio/ToMathlib + 19 PolyFun/ToCslib + 3 Cslib modules, about 19.6k lines;
   * `VCVio.Native`: 138 + 36;
   * `VCVio.StateSeparating.Hybrid`: 126 + 28;
   * whole `VCVio` umbrella: 502 + 149 (about 178k lines).

## 1. Core types (VERIFIED)

`VCVio/OracleComp/OracleSpec.lean`
```lean
def OracleSpec (ι : Type u) : Type (max u (v + 1)) :=
  ι → Type v
@[reducible, always_inline] def ofFn {ι : Type u} (F : ι → Type v) : OracleSpec ι := F
notation:25 (name := singletonSpec) A:25 " →ₒ " B:26 => OracleSpec.ofFn (ι := A) (fun _ => B)
abbrev Domain (_spec : OracleSpec ι) : Type _ := ι
abbrev Range (spec : OracleSpec ι) (t : ι) : Type _ := spec t
@[reducible] def coinSpec : OracleSpec.{0, 0} Unit := Unit →ₒ Bool
@[inline, reducible] def unifSpec : OracleSpec ℕ := OracleSpec.ofFn fun n => Fin (n + 1)
```
`spec₁ + spec₂` combines specs (`++ₒ` is dead).

`VCVio/OracleComp/OracleComp.lean`
```lean
@[reducible]
def OracleComp {ι : Type u} (spec : OracleSpec.{u, v} ι) :
    Type w → Type (max u v w) :=
  PFunctor.FreeM spec.toPFunctor
```
`VCVio/OracleComp/ProbComp/Basic.lean`
```lean
abbrev ProbComp : Type → Type := OracleComp unifSpec
```
Uniform sampling: `uniformFin (n : ℕ) : ProbComp (Fin (n + 1))` with notation `$[0..n]`. Also `uniformRange`, and `$ᵗ α` for `SampleableType`.

**Distribution type is a layered bundle, not one thing.**
* `ToMathlib/ProbabilityTheory/SPMF.lean`: `def SPMF : Type u → Type u := OptionT PMF`. `SPMF.toPMF : SPMF α → PMF (Option α)` (`none` = missing mass), `SPMF.mk (p : PMF (Option α)) : SPMF α`. `instance : FunLike (SPMF α) α ENNReal` with `p x = p.toPMF (some x)` (`SPMF.apply_eq_toPMF_some`).
* `VCVio/EvalDist/PFunctor.lean`: `noncomputable instance instMonadLiftTPMF [P.IsProbabilitySpec] : MonadLiftT (FreeM P) PMF`. This is the lossless PMF of a program. `OracleSpec.IsProbabilitySpec spec := PFunctor.IsProbabilitySpec spec.toPFunctor`. `IsUniformSpec` instances exist for `unifSpec`, `coinSpec`, and `spec + spec'`.
* Legacy API, all `@[deprecated]` (`VCVio/EvalDist/Defs/Basic.lean`):
```lean
def evalSPMF [MonadLiftT m SPMF] {α : Type u} (mx : m α) : SPMF α := liftM mx
notation "𝒮[" mx "]" => evalSPMF mx
def probOutput [MonadLiftT m SPMF] (mx : m α) (x : α) : ℝ≥0∞ := evalSPMF mx x
noncomputable def probEvent [MonadLiftT m SPMF] (mx : m α) (p : α → Prop) : ℝ≥0∞ :=
  (evalSPMF mx).run.toOuterMeasure (some '' {x | p x})
def probFailure [MonadLiftT m SPMF] (mx : m α) : ℝ≥0∞ := (evalSPMF mx).run none
notation "Pr[= " x " | " mx "]" => probOutput mx x
macro (name := probEventNotation) "Pr[ " p:term " | " mx:term "]" : term => `(probEvent $mx $p)
notation "Pr[⊥" " | " mx "]" => probFailure mx
lemma evalSPMF_eq_simulateQ [IsProbabilitySpec spec] (mx : OracleComp spec α) :
    𝒮[mx] = simulateQ IsProbabilitySpec.toPMF mx := rfl      -- VCVio/OracleComp/EvalDist.lean
```
* **ProbComp -> Mathlib PMF/SPMF:**
  * `(liftM p : PMF α)` for `p : ProbComp α` (lossless);
  * `𝒮[p] : SPMF α`, then `.toPMF : PMF (Option α)`;
  * `Pr[= x | p] = 𝒮[p] x` (`probOutput_def`).
* Primary, measure-native semantics (`VCVio/EvalDist/Defs/Measure/Core.lean`):
```lean
class EvalDistSemantics (m : Type u → Type v) where
  denote : {α : Type u} → [MeasurableSpace α] → m α → Measure α
  apply_univ_le_one : ∀ {α : Type u} [MeasurableSpace α] (mx : m α), denote mx Set.univ ≤ 1
noncomputable def evalDist {m} [EvalDistSemantics m] {α : Type u} [MeasurableSpace α] (mx : m α) : Measure α
notation "𝒟[" mx "]" => evalDist mx
class LawfulPureEvalDistSemantics (m) [Monad m] [EvalDistSemantics m] : Prop where
  denote_pure {α} [MeasurableSpace α] (x : α) : 𝒟[(pure x : m α)] = Measure.dirac x
class LawfulEvalDistSemantics (m) [Monad m] [EvalDistSemantics m] : Prop extends LawfulPureEvalDistSemantics m where
  denote_bind {α β} [MeasurableSpace α] [MeasurableSpace β] (mx : m α) (f : α → m β)
      (hf : Measurable fun x => 𝒟[f x]) : 𝒟[mx >>= f] = Measure.bind 𝒟[mx] fun x => 𝒟[f x]
theorem evalDist_bind_of_discrete ...   -- no measurability proof needed when source type is DiscreteMeasurableSpace
theorem evalDist_map {m} [Monad m] [LawfulMonad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m] ... (hf : Measurable f) : 𝒟[f <$> mx] = 𝒟[mx].map f
```
  * Instances: `instEvalDistSemanticsOfMonadLiftTSPMF` (priority 10, via the SPMF lift) and `instEvalDistSemanticsFreeM` (priority 20, needs `[P.IsMeasureSpec]`, in `VCVio/EvalDist/PFunctorMeasure/Core.lean`).
  * `OracleSpec.IsMeasureSpec`, `IsUniformMeasureSpec`: native instances exist for `unifSpec`/`coinSpec`.
  * Bridges (`Defs/Basic.lean`): `evalDist_apply_singleton : 𝒟[mx] {x} = Pr[= x | mx]`, `evalDist_apply_setOf : 𝒟[mx] {x | p x} = Pr[p | mx]` (discrete α), `evalDist_apply_univ : 𝒟[mx] Set.univ = 1 - Pr[⊥ | mx]`, and `OracleComp.evalDist_apply_univ_eq_one` (total for lossless specs).
  * Measure-world event notation (`ProbabilityNotation.lean`): `Pr{ do-seq }[ p ]` = `𝒟[do ...; return p] {True}`.
* Kernel view (`VCVio/EvalDist/Kernel.lean`): `evalDistKernel (f : ρ → m α) (hf : Measurable fun r => 𝒟[f r]) : Kernel ρ α`; `evalDistKernelOfDiscrete`.

## 2. Total variation (VERIFIED, every declaration)

### 2a. `ToMathlib/Probability/ProbabilityMassFunction/TotalVariation.lean` (imports only Mathlib + `ToMathlib.Data.ENNReal.AbsDiff`)
```lean
protected def PMF.etvDist (p q : PMF α) : ℝ≥0∞ := (∑' x, ENNReal.absDiff (p x) (q x)) / 2
protected def PMF.tvDist (p q : PMF α) : ℝ := (p.etvDist q).toReal
lemma etvDist_self/comm/triangle/le_one/ne_top/eq_zero_iff ; tvDist_self/comm/nonneg/triangle/le_one/eq_zero_iff
lemma etvDist_map_le (f : α' → β) (p q : PMF α') : (f <$> p).etvDist (f <$> q) ≤ p.etvDist q     -- α' β : Type u₀ (SAME universe)
lemma tvDist_map_le  (f : α' → β) (p q : PMF α') : (f <$> p).tvDist (f <$> q) ≤ p.tvDist q
lemma etvDist_bind_right_le (f : α' → PMF β) (p q : PMF α') : (p.bind f).etvDist (q.bind f) ≤ p.etvDist q
lemma tvDist_bind_right_le  (f : α' → PMF β) (p q : PMF α') : (p.bind f).tvDist (q.bind f) ≤ p.tvDist q
noncomputable instance instMetricSpace : MetricSpace (PMF α)     -- dist = tvDist
lemma etvDist_option_punit / tvDist_option_punit :
    p.tvDist q = |(p (some ())).toReal - (q (some ())).toReal|          -- p q : PMF (Option PUnit)
```
Not present: sup-over-events characterisation for PMF (only the sum definition), and "advantage ≤ TV" for general events.

### 2b. `VCVio/EvalDist/TVDist.lean` (SPMF/monadic; uses deprecated `𝒮[·]`)
```lean
protected def SPMF.tvDist (p q : SPMF α) : ℝ := p.toPMF.tvDist q.toPMF
SPMF.tvDist_self/comm/nonneg/triangle/le_one/eq_zero_iff
lemma SPMF.tvDist_map_le {α' : Type w} {β : Type w} (f : α' → β) (p q : SPMF α') : SPMF.tvDist (f <$> p) (f <$> q) ≤ SPMF.tvDist p q
lemma SPMF.tvDist_bind_right_le {α' β : Type w} (f : α' → SPMF β) (p q : SPMF α') : SPMF.tvDist (p >>= f) (q >>= f) ≤ SPMF.tvDist p q

variable {m : Type u → Type v} [MonadLiftT m SPMF] {α : Type u}
noncomputable def tvDist (mx my : m α) : ℝ := SPMF.tvDist (𝒮[mx]) (𝒮[my])
tvDist_self / tvDist_eq_zero_iff (mx my) : tvDist mx my = 0 ↔ 𝒮[mx] = 𝒮[my] / tvDist_comm / tvDist_nonneg / tvDist_le_one
lemma tvDist_triangle (mx my mz : m α) : tvDist mx mz ≤ tvDist mx my + tvDist my mz
lemma tvDist_map_le [Monad m] [LawfulMonadLiftT m SPMF] [LawfulMonad m] {β : Type u} (f : α → β) (mx my : m α) :
    tvDist (f <$> mx) (f <$> my) ≤ tvDist mx my
lemma tvDist_bind_right_le [Monad m] [LawfulMonadLiftT m SPMF] [LawfulMonad m] {β : Type u} (f : α → m β) (mx my : m α) :
    tvDist (mx >>= f) (my >>= f) ≤ tvDist mx my                      -- data processing, randomised kernel f
lemma tvDist_bind_left_le {m} [Monad m] [LawfulMonad m] [MonadLiftT m PMF] [LawfulMonadLiftT m PMF] {α β : Type u}
    (mx : m α) (f g : α → m β) : tvDist (mx >>= f) (mx >>= g) ≤ ∑' a, Pr[= a | mx].toReal * tvDist (f a) (g a)
theorem tvDist_bind_left_le_const' ... (hfg : ∀ a, tvDist (f a) (g a) ≤ c) : tvDist (mx >>= f) (mx >>= g) ≤ c
   -- (also tvDist_bind_left_le_const with `a ∈ support mx`, and ofReal_ ℝ≥0∞ companions; need [MonadAttach m] [EvalDistCompatible m])
lemma tvDist_bind_left_event_le ... (bad : α → Prop) (h_eq : ∀ a, ¬ bad a → 𝒮[f a] = 𝒮[g a]) :
    tvDist (mx >>= f) (mx >>= g) ≤ Pr[bad | mx].toReal
lemma tvDist_bind_event_le ... (mx my : m α) (f g : α → m β) (bad : α → Prop) (h_eq : ∀ a, ¬ bad a → 𝒮[f a] = 𝒮[g a]) :
    tvDist (mx >>= f) (my >>= g) ≤ Pr[bad | mx].toReal + tvDist mx my      -- + tvDist_bind_event_right_le, ofReal_ versions
lemma tvDist_le_probEvent_of_probOutput_eq_of_not [Monad m] {mx my : m α} [NeverFail mx] [NeverFail my]
    (p : α → Prop) (h_eq : ∀ x, ¬p x → Pr[= x | mx] = Pr[= x | my]) (h_event_eq : Pr[ p | mx] = Pr[ p | my]) :
    tvDist mx my ≤ Pr[ p | mx].toReal
-- advantage ≤ TV, Boolean outputs only:
lemma abs_probOutput_toReal_sub_le_tvDist {m : Type → Type v} [MonadLiftT m SPMF] (game₁ game₂ : m Bool) :
    |Pr[= true | game₁].toReal - Pr[= true | game₂].toReal| ≤ tvDist game₁ game₂
```
`TVDist/Positivity.lean`: only a `@[positivity tvDist _ _]` extension (`Mathlib.Meta.Positivity.evalTVDist`, nonnegativity). No other math.
Not present in the SPMF stack: a sup-over-events characterisation and a general-event "Pr[E|a] − Pr[E|b] ≤ TV". Only the Bool-output lemma above.

### 2c. Measure-native: `ToMathlib/MeasureTheory/Measure/TotalVariation.lean` (namespace `MeasureTheory.Measure`; imports Mathlib + AbsDiff)
```lean
protected noncomputable def Measure.etvDist (μ ν : Measure α) : ℝ≥0∞ :=
  ⨆ s : {s : Set α // MeasurableSet s}, ENNReal.absDiff (μ s.1) (ν s.1)      -- sup over events BY DEFINITION
protected noncomputable def Measure.tvDist (μ ν : Measure α) : ℝ := (μ.etvDist ν).toReal
theorem absDiff_apply_le_etvDist (μ ν : Measure α) {s : Set α} (hs : MeasurableSet s) : ENNReal.absDiff (μ s) (ν s) ≤ μ.etvDist ν
etvDist_self / etvDist_comm / etvDist_nonneg
theorem etvDist_triangle (μ ν κ : Measure α) : μ.etvDist κ ≤ μ.etvDist ν + ν.etvDist κ        -- no mass hypotheses
theorem etvDist_eq_zero_iff {μ ν : Measure α} : μ.etvDist ν = 0 ↔ μ = ν
theorem etvDist_le_one (μ ν : Measure α) (hμ : μ Set.univ ≤ 1) (hν : ν Set.univ ≤ 1) : μ.etvDist ν ≤ 1
theorem etvDist_map_le (μ ν : Measure α) (f : α → β) (hf : Measurable f) : (μ.map f).etvDist (ν.map f) ≤ μ.etvDist ν
tvDist_self/comm/nonneg ; tvDist_triangle (needs 3 mass ≤ 1 hyps) ; tvDist_le_one ; tvDist_eq_zero_iff ; tvDist_map_le
theorem tvDist_punit (μ ν : Measure PUnit) [IsFiniteMeasure μ] [IsFiniteMeasure ν] : μ.tvDist ν = |(μ {PUnit.unit}).toReal - (ν {PUnit.unit}).toReal|
```
`ToMathlib/MeasureTheory/Measure/TotalVariation/Bind.lean`:
```lean
theorem absDiff_lintegral_le_etvDist (μ ν : Measure α) (f : α → ENNReal) (hf : Measurable f) (hbound : ∀ a, f a ≤ 1) :
    ENNReal.absDiff (∫⁻ a, f a ∂μ) (∫⁻ a, f a ∂ν) ≤ μ.etvDist ν            -- **T1** (f = acceptance prob of randomised D)
theorem lintegral_le_add_etvDist (μ ν) (f) (hf : Measurable f) (hbound : ∀ a, f a ≤ 1) : ∫⁻ a, f a ∂μ ≤ (∫⁻ a, f a ∂ν) + μ.etvDist ν
theorem etvDist_bind_le (μ ν : Measure α) (k : α → Measure β) (hk : Measurable k) [∀ a, IsSubprobabilityMeasure (k a)] :
    (μ.bind k).etvDist (ν.bind k) ≤ μ.etvDist ν                                -- DPI for mediator kernel
theorem etvDist_bind_bind_le_lintegral (μ : Measure α) (k l : α → Measure β) (hk : AEMeasurable k μ) (hl : AEMeasurable l μ)
    (bound : α → ENNReal) (hbound : ∀ᵐ a ∂μ, (k a).etvDist (l a) ≤ bound a) : (μ.bind k).etvDist (μ.bind l) ≤ ∫⁻ a, bound a ∂μ
theorem etvDist_bind_bind_le_add_lintegral (μ ν : Measure α) (k l : α → Measure β) (hk : Measurable k) (hl : AEMeasurable l ν)
    [∀ a, IsSubprobabilityMeasure (k a)] (bound : α → ENNReal) (hbound : ∀ᵐ a ∂ν, (k a).etvDist (l a) ≤ bound a) :
    (μ.bind k).etvDist (ν.bind l) ≤ μ.etvDist ν + ∫⁻ a, bound a ∂ν            -- hybrid step: prefix TV + conditional TV
theorem etvDist_bind_bind_le_add_lintegral_of_bad (μ) (k l) (hk hl : AEMeasurable ...) [subprob k, l] {bad : Set α} (hbad : MeasurableSet bad)
    (bound) (hgood : ∀ᵐ a ∂μ, a ∉ bad → (k a).etvDist (l a) ≤ bound a) : (μ.bind k).etvDist (μ.bind l) ≤ μ bad + ∫⁻ a in badᶜ, bound a ∂μ
theorem etvDist_bind_bind_le_of_bad (μ) (k l) (hk hl : AEMeasurable ...) [subprob] {bad : Set α} (hbad : MeasurableSet bad) (ε : ENNReal)
    (hgood : ∀ᵐ a ∂μ, a ∉ bad → (k a).etvDist (l a) ≤ ε) : (μ.bind k).etvDist (μ.bind l) ≤ μ bad + ε * μ badᶜ
theorem tvDist_bind_le (μ ν) [IsSubprobabilityMeasure μ] [IsSubprobabilityMeasure ν] (k) (hk : Measurable k) [∀ a, IsSubprobabilityMeasure (k a)] :
    (μ.bind k).tvDist (ν.bind k) ≤ μ.tvDist ν
theorem tvDist_bind_bind_le_lintegral ... (hfinite : (∫⁻ a, bound a ∂μ) ≠ ⊤) : ... ≤ (∫⁻ a, bound a ∂μ).toReal
```
`ToMathlib/Probability/Kernel/TotalVariation.lean` (namespace `ProbabilityTheory.Kernel`):
```lean
theorem etvDist_comp_le (κ η : Kernel ρ α) (τ : Kernel α β) [IsSubprobabilityKernel τ] (r : ρ) :
    ((τ ∘ₖ κ) r).etvDist ((τ ∘ₖ η) r) ≤ (κ r).etvDist (η r)
theorem etvDist_comp_comp_le_lintegral / etvDist_comp_comp_le_add_lintegral / etvDist_comp_comp_le_of_bad  -- kernel forms of the three bind lemmas
```
`ToMathlib/Probability/Kernel/Subprobability.lean` (VERIFIED): `class IsSubprobabilityKernel`; `instance IsMarkovKernel.toIsSubprobabilityKernel`; instances for `comp`, `prod`, `map`, `comap`, `pow` (`Kernel.pow.instIsSubprobabilityKernel` is useful for N-round iteration `κ ^ n`).
`ToMathlib/MeasureTheory/Measure/Subprobability.lean`: `class IsSubprobabilityMeasure`; `IsProbabilityMeasure.toIsSubprobabilityMeasure`; `isSubprobabilityMeasure_bind`.
`ToMathlib/MeasureTheory/Measure/Bool.lean`:
```lean
noncomputable def Measure.boolDist (μ ν : Measure Bool) : ℝ≥0∞ := ENNReal.absDiff (μ {true}) (ν {true})
noncomputable def Measure.boolBias (μ : Measure Bool) : ℝ≥0∞ := ENNReal.absDiff (μ {true}) (μ {false})
lemma boolDist_triangle / boolDist_self / toReal_boolDist [IsFiniteMeasure μ] [IsFiniteMeasure ν] : (μ.boolDist ν).toReal = |(μ {true}).toReal - (ν {true}).toReal|
```
`ToMathlib/Data/ENNReal/AbsDiff.lean`: `protected def ENNReal.absDiff (a b : ℝ≥0∞) := (a - b) + (b - a)`; `absDiff_eq_edist`, `absDiff_toReal`, `absDiff_triangle`, `absDiff_le_iff`, `absDiff_tsum_le`, ...

### 2d. `VCVio/EvalDist/MeasureTVDist/{Basic,Bind}.lean` (monadic wrappers on `𝒟[·]`; any `[EvalDistSemantics m]`)
```lean
noncomputable def measureETVDist [EvalDistSemantics m] [MeasurableSpace α] (mx my : m α) : ℝ≥0∞ := Measure.etvDist (𝒟[mx]) (𝒟[my])
noncomputable def measureTVDist  [EvalDistSemantics m] [MeasurableSpace α] (mx my : m α) : ℝ  := Measure.tvDist  (𝒟[mx]) (𝒟[my])
measureETVDist_self/comm/triangle/eq_zero_iff/le_one ; measureTVDist_self/comm/nonneg/triangle/le_one/eq_zero_iff
theorem measure_absDiff_apply_le_measureETVDist [EvalDistSemantics m] [MeasurableSpace α] (mx my : m α) {s : Set α} (hs : MeasurableSet s) :
    ENNReal.absDiff (𝒟[mx] s) (𝒟[my] s) ≤ measureETVDist mx my                     -- event-level advantage ≤ TV
theorem measureETVDist_bind_le (mx my : m α) (f : α → m β) (hf : Measurable fun a ↦ 𝒟[f a]) : measureETVDist (mx >>= f) (my >>= f) ≤ measureETVDist mx my
theorem measureETVDist_bind_bind_le_add_lintegral (mx my : m α) (f g : α → m β) (hf : Measurable fun a ↦ 𝒟[f a]) (hg : Measurable fun a ↦ 𝒟[g a])
    (bound : α → ENNReal) (hbound : ∀ᵐ a ∂𝒟[my], measureETVDist (f a) (g a) ≤ bound a) : measureETVDist (mx >>= f) (my >>= g) ≤ measureETVDist mx my + ∫⁻ a, bound a ∂𝒟[my]
theorem measureETVDist_bind_bind_le_of_bad (mx : m α) (f g) (hf) (hg) {bad : Set α} (hbad : MeasurableSet bad) (ε : ENNReal)
    (hgood : ∀ᵐ a ∂𝒟[mx], a ∉ bad → measureETVDist (f a) (g a) ≤ ε) : measureETVDist (mx >>= f) (mx >>= g) ≤ 𝒟[mx] bad + ε * 𝒟[mx] badᶜ
-- + measureETVDist_bind_bind_le_lintegral, measureTVDist_bind_le, measureTVDist_bind_bind_le_lintegral
```
(In `Bind.lean`: `variable {m} [Monad m] [EvalDistSemantics m] [LawfulEvalDistSemantics m] {α β : Type u} [MeasurableSpace α] [MeasurableSpace β]`.)
Bridges (`MeasureTVDist.lean`): `SPMF.toMeasure_tvDist_eq_zero_iff` (discrete α) and `SPMF.toMeasure_tvDist_punit` only.

### 2e. Related TV <-> coupling (SPMF world only), `ProgramLogic/Relational/Quantitative.lean`
```lean
theorem tvDist_eq_one_sub_eRelWP_eqRel {oa ob : OracleComp spec₁ α} :
    tvDist oa ob = (1 - eRelWP (spec₂ := spec₁) oa ob (RelPost.indicator (EqRel α))).toReal
theorem approxRelTriple_eqRel_of_ofReal_tvDist_le {oa ob : OracleComp spec₁ α} {ε : ℝ≥0∞} (h : ENNReal.ofReal (tvDist oa ob) ≤ ε) : ApproxRelTriple ε oa ob (EqRel α)
```
No measure-level "TV ≤ P[x≠y] under a coupling" lemma found (grep of tvDist/etvDist ∩ Coupling is empty); `ToMathlib/MeasureTheory/Measure/Coupling.lean` has only the `Coupling`/`IsCoupling` structures and bind composition.

## 3. Game-hop / hybrid infrastructure (VERIFIED)

* **Distinguishing advantage, measure-valued** (`VCVio/StateSeparating/Advantage/Measure.lean`): `advantage (h₀) (s₀) (h₁) (s₁) (A : OracleComp E Bool) : ℝ≥0∞ := 𝒟[h₀.runProb s₀ A].boolDist 𝒟[h₁.runProb s₁ A]` (for `QueryImpl.Stateful unifSpec E σ` handlers).
  * `advantage_self`, `advantage_symm`, `advantage_triangle`.
  * Quantifies over `A : OracleComp E Bool` with NO query bound.
* **Hybrid over n handlers** (`StateSeparating/Hybrid.lean`):
```lean
theorem advantage_hybrid {σ : ℕ → Type} (h : (i : ℕ) → QueryImpl.Stateful unifSpec E (σ i)) (s : (i : ℕ) → σ i) (A : OracleComp E Bool) (n : ℕ) :
    (h 0).advantage (s 0) (h n) (s n) A ≤ ∑ i ∈ Finset.range n, (h i).advantage (s i) (h (i + 1)) (s (i + 1)) A
```
  Proof is induction + `advantage_triangle`. `IndistAt.hybrid` (`StateSeparating/IndistAt.lean`) is the ε-indexed form `(h 0, s 0) ≈ᵈ[∑ i ∈ Finset.range n, ε i] (h n, s n)`.
* **Generic game-hop algebra** (`CryptoFoundations/Asymptotics/Security.lean`): `SecurityGame.secureAgainst_of_hybrid` (negligible chain), `secureAgainst_of_close_poly_reduction`. `ProgramLogic/NotationCore.lean`: `GameEquiv g₁ g₂ := 𝒮[g₁] = 𝒮[g₂]`, `AdvBound game ε := |Pr[= true | game].toReal - 1/2| ≤ ε`, `AdvBound.of_tvDist`, `AdvBound.of_gameEquiv`.
* **N-step hybrid with query-bounded adversary** (closest to honeypot swapping), `CryptoFoundations/AsymmEncAlg/INDCPA/GenericLift.lean`:
```lean
theorem IND_CPA_OneTime_Advantage_stepAdversary [Inhabited M] (adversary : encAlg'.IND_CPA_Adversary) (k : ℕ) :
    IND_CPA_OneTime_Advantage encAlg' ProbCompRuntime.probComp (IND_CPA_stepAdversary (encAlg' := encAlg') adversary k) =
      𝒟[encAlg'.IND_CPA_LR_hybrid adversary (k + 1)].boolDist 𝒟[encAlg'.IND_CPA_LR_hybrid adversary k]
theorem IND_CPA_Advantage_le_sum_oneTime_stepAdversary ... (hq : adversary.MakesAtMostQueries q) :
    IND_CPA_Advantage (encAlg := encAlg') adversary ≤ ∑ k ∈ Finset.range q, IND_CPA_OneTime_Advantage encAlg' ProbCompRuntime.probComp (IND_CPA_stepAdversary (encAlg' := encAlg') adversary k)
theorem IND_CPA_Advantage_le_mul_of_oneTime_bound ... (hstep : ∀ adv : IND_CPA_OneTime_Adversary encAlg', IND_CPA_OneTime_Advantage ... adv ≤ ε) : IND_CPA_Advantage (encAlg := encAlg') adversary ≤ q * ε
```
  The step adversary runs the original up to query k, embeds the one-time challenge at query k, and answers later queries with the other branch. This is the pattern for "replace the k-th real attack by a honeypot".
* **Identical-until-bad / fundamental lemma** (`ProgramLogic/Relational/SimulateQ/{Basic,Epsilon,StateDependent}.lean`, SPMF `tvDist`):
```lean
theorem tvDist_simulateQ_le_probEvent_bad {σ : Type} (impl₁ impl₂ : QueryImpl spec (StateT σ (OracleComp spec))) (bad : σ → Prop)
    (oa : OracleComp spec α) (s₀ : σ) (h_init : ¬bad s₀)
    (h_agree : ∀ (t : spec.Domain) (s : σ), ¬bad s → (impl₁ t).run s = (impl₂ t).run s)
    (h_mono₁ : ∀ t s, bad s → ∀ x ∈ support ((impl₁ t).run s), bad x.2) (h_mono₂ : ... same for impl₂) :
    tvDist ((simulateQ impl₁ oa).run' s₀) ((simulateQ impl₂ oa).run' s₀) ≤ Pr[ bad ∘ Prod.snd | (simulateQ impl₁ oa).run s₀].toReal
theorem identical_until_bad_with_flag ...                       -- same with flag σ × Bool
theorem tvDist_simulateQ_le_queryBound_mul_slack_plus_probEvent_bad (impl₁ impl₂ : QueryImpl spec (StateT (σ × Bool) (OracleComp spec')))
    {ε : ℝ} (hε : 0 ≤ ε) (S : ι → Prop) [DecidablePred S]
    (h_step_tv_S : ∀ (t : ι), S t → ∀ (s : σ), tvDist ((impl₁ t).run (s, false)) ((impl₂ t).run (s, false)) ≤ ε)
    (h_step_eq_nS : ∀ (t : ι), ¬ S t → ∀ (p : σ × Bool), (impl₁ t).run p = (impl₂ t).run p)
    (h_mono₁ : ∀ (t : ι) (p : σ × Bool), p.2 = true → ∀ z ∈ support ((impl₁ t).run p), z.2.2 = true)
    (oa : OracleComp spec α) {qS : ℕ} (h_qb : OracleComp.IsQueryBoundP oa S qS) (s₀ : σ) :
    tvDist ((simulateQ impl₁ oa).run' (s₀, false)) ((simulateQ impl₂ oa).run' (s₀, false)) ≤ qS * ε + Pr[fun z : α × σ × Bool => z.2.2 = true | (simulateQ impl₁ oa).run (s₀, false)].toReal
```
  This is "q charged queries each costing ε TV, plus P[bad]", directly shaped like T3 if the protocol is modelled as an oracle program against a stateful handler. `QueryImpl.Stateful.advantage_le_queryBound_mul_slack_plus_probEvent_bad` (`StateSeparating/IdenticalUntilBad.lean`) is the `advantage` form (ℝ≥0∞). `ProgrammingOracle.lean` has `tvDist_simulateQ_randomOracle_withProgramming_le_probEvent_bad`.
* Union-bound-like (SPMF): `probEvent_bind_le_add {mx : m α} {my : α → m β} {p q} {ε₁ ε₂ : ℝ≥0∞} (h₁ : Pr[fun x => ¬p x | mx] ≤ ε₁) (h₂ : ∀ x ∈ support mx, p x → Pr[fun y => ¬q y | my x] ≤ ε₂) : Pr[fun y => ¬q y | mx >>= my] ≤ ε₁ + ε₂` (`EvalDist/Monad/Basic.lean`); `Monad/Disagreement*.lean` (`probEvent_bind_le_add_of_disagree`, ...); measure forms in `Monad/Disagreement/Measure.lean` (`prEvent_bind_le_sum_add_lintegral_ae`).
* UC layer: `VCVio/Interaction/UC/Computational.lean` `distAdvantage S p q := (S.evalDist p).etvDist (S.evalDist q)` with `_triangle`, `_le_one`; `ReactiveSecurity.lean` `advantage real ideal context := (law real context).etvDist (law ideal context)`.

## 4. Adversaries, query bounds (VERIFIED)

```lean
@[reducible] def QueryImpl {ι} (spec : OracleSpec ι) (m : Type u → Type v) := (x : spec.Domain) → m (spec.Range x)   -- OracleComp/SimSemantics/QueryImpl/Basic.lean
def simulateQ {ι} {spec : OracleSpec ι} {r : Type u → Type _} [Monad r] (impl : QueryImpl spec r) {α : Type u} (mx : OracleComp spec α) : r α := PFunctor.FreeM.liftM impl mx
@[reducible] def QueryImpl.Stateful (I : OracleSpec ιᵢ) (E : OracleSpec ιₑ) (σ : Type v) := QueryImpl E (StateT σ (OracleComp I))
def QueryImpl.Stateful.run (h : QueryImpl.Stateful I E σ) (s₀ : σ) (A : OracleComp E α) : OracleComp I α := (simulateQ h A).run' s₀
-- OracleComp/QueryTracking/QueryBound/Basic.lean
def IsQueryBound (oa : OracleComp spec α) (budget : B) (canQuery : ι → B → Prop) (cost : ι → B → B) : Prop
def IsQueryBoundP (oa : OracleComp spec α) (p : ι → Prop) [DecidablePred p] (n : ℕ) : Prop   -- ≤ n queries at indices satisfying p
abbrev IsPerIndexQueryBound (oa : OracleComp spec α) (qb : ι → ℕ) : Prop     -- [DecidableEq ι]
def IsTotalQueryBound (oa : OracleComp spec α) (n : ℕ) : Prop
-- CryptoFoundations/SecExp.lean
structure BoundedAdversary {ι : Type u} [DecidableEq ι] (spec : OracleSpec ι) (α β : Type u) where
  run : α → OracleComp spec β
  qb : ι → ℕ
  qb_isQueryBound (x : α) : IsPerIndexQueryBound (run x) (qb)
  activeOracles : List ι
  mem_activeOracles_iff (i : ι) : i ∈ activeOracles ↔ qb i ≠ 0
-- QueryTracking/CountingOracle/Core.lean
@[expose] def OracleSpec.countingOracle [DecidableEq ι] : QueryImpl spec (AddWriterT (QueryCount ι) (OracleComp spec))
```
Also `IsQueryBound.simulateQ_run_of_step` (transfers a bound through a stateful `simulateQ`), `isQueryBound_bind`, `Iter.lean` (`replicate` bounds).

How to phrase quantification:
* **"for every adversary A : α → ProbComp β":** `∀ A : α → ProbComp β, ...`. It is unbounded (AGENTS gotcha 11 and 14: such types carry no resource bound; write bounds for NAMED reductions, never `∃ B, ...`). The class is finite-tree programs only.
* **"for every oracle adversary":** `A : OracleComp E γ` run against a handler `h : QueryImpl.Stateful unifSpec E σ`, as `h.run s₀ A` / `(simulateQ h A).run' s₀`.
  * With resource bound: `(hA : OracleComp.IsQueryBoundP A S q)`, or `IsTotalQueryBound A n`, or `BoundedAdversary`.
  * `IndistAt h₀ s₀ h₁ s₁ ε := ∀ (A : OracleComp E Bool), h₀.advantage s₀ h₁ s₁ A ≤ ε` is the template for "for every distinguisher".
* **Arbitrary randomised policy beyond ProbComp:** `A : Kernel α β` (+ `IsMarkovKernel`) or `A : α → Measure β` with `Measurable A`. Everything in 2c applies directly and needs no `OracleComp`.

## 5. Program logic (`VCVio/ProgramLogic/*`) (VERIFIED)

* **Qualitative pRHL**, coupling-based, SPMF-world (`Relational/Basic.lean`): `abbrev RelPost`, `EqRel`, `abbrev RelTriple (oa : OracleComp spec₁ α) (ob : OracleComp spec₂ β) (R : RelPost α β) : Prop`.
  * Notation: `⟪c₁ ~ c₂ | R⟫`.
  * Rules: `relTriple_bind`, `relTriple_pure_pure`, `relTriple_map`, `relTriple_replicate`, `relTriple_list_foldlM`, `relTriple_uniformSample_bij`, `relTriple_trans_eqRel`, `evalSPMF_eq_of_relTriple_eqRel`.
  * Requires `[IsUniformSpec spec]`.
* **Quantitative (eRHL)** (`Relational/QuantitativeDefs.lean`): `eRelWP oa ob g := ⨆ (c : SPMF.Coupling 𝒮[oa] 𝒮[ob]), ∑' z, Pr[= z | c.1] * g z.1 z.2`, `RelTriple'`, `ApproxRelTriple ε oa ob R := 1 - ε ≤ eRelWP oa ob (RelPost.indicator R)` (R holds except w.p. ≤ ε). Notation `⟪c₁ ≈[ε] c₂ | R⟫`. TV bridge: section 2e.
* **Measure-native relational logic** (`Relational/Measure.lean`, `Measure/Bind.lean`; closure = 5 modules / 980 lines, Mathlib only):
```lean
def MeasureProgramLogic.CouplingPost (μ : Measure α) (ν : Measure β) (R : α → β → Prop) : Prop := ∃ c : Measure.Coupling μ ν, ∀ᵐ z ∂c.joint, R z.1 z.2
def RelWP [EvalDistSemantics m₁] [EvalDistSemantics m₂] (mx : m₁ α) (my : m₂ β) (R) : Prop := CouplingPost 𝒟[mx] 𝒟[my] R
noncomputable def eRelWP (mx : m₁ α) (my : m₂ β) (g : α → β → ℝ≥0∞) : ℝ≥0∞ := ⨆ c : Measure.Coupling 𝒟[mx] 𝒟[my], ∫⁻ z, g z.1 z.2 ∂c.joint
theorem relWP_bind ... (hinit : RelWP mx my R) (f) (g) (hf : Measurable fun a => 𝒟[f a]) (hg : ...) {j : α × β → Measure (γ × δ)} (hj : Measurable j) (hS : MeasurableSet {z | S z.1 z.2})
    (hstep : ∀ z, R z.1 z.2 → Measure.IsCoupling (j z) 𝒟[f z.1] 𝒟[g z.2] ∧ ∀ᵐ out ∂j z, S out.1 out.2) : RelWP (mx >>= f) (my >>= g) S
```
  No TV lemma attached to it.
* **Unary** (`Unary/*`): quantitative `wp`, `Triple`, `⦃P⦄ c ⦃Q⦄`. Measure versions in `Unary/WP/Measure.lean`, `Unary/WP/Probabilistic/Measure.lean`.
* **Tactics** (`import VCVio.ProgramLogic.Tactics`, closure 167 + 35 modules, 45k lines): `by_equiv`, `game_trans`, `by_dist`, `by_upto bad`, `by_hoare`, `rvcstep`, `rvcgen`, `vcstep`, `vcgen`, `rel_conseq`. Walkthroughs in `Examples/ProgramLogic/`. Docs: `docs/agents/program-logic.md`.
* Expect real friction: heavy, deprecation-laden, SPMF-based relational logic, mid-migration to measures.

## 6. Import closure (computed by following `import` / `public import` lines; VCVio = VCVio.* + ToMathlib.*)

| root module | VCVio+ToMathlib | PolyFun+ToCslib | lines (VCVio+ToMathlib) | notes |
|---|---|---|---|---|
| `ToMathlib.Data.ENNReal.AbsDiff` | 1 | 0 | 175 | |
| `ToMathlib.Probability.ProbabilityMassFunction.TotalVariation` | 2 | 0 | 395 | PMF TV only |
| `ToMathlib.MeasureTheory.Measure.TotalVariation` | 2 | 0 | 339 | Measure.etvDist only |
| **`ToMathlib.Probability.Kernel.TotalVariation`** (+ `.Measure.Bool`) | **7 (8)** | **0** | 860 (1039) | **recommended for T1/DPI** |
| `VCVio.EvalDist.Defs.Measure.Core` | 3 | 0 | 549 | `EvalDistSemantics`, `𝒟[·]` |
| `ToMathlib.MeasureTheory.Measure.Coupling` | 2 | 0 | 332 | |
| `VCVio.ProgramLogic.Relational.Measure` | 5 | 0 | 980 | measure pRHL |
| `VCVio.EvalDist.MeasureTVDist.Bind` | 11 | 0 | 1470 | monadic measureTVDist |
| `VCVio.EvalDist.Kernel` | 14 | 1 | 2280 | |
| `VCVio.EvalDist.TVDist` | 54 | 4 | 8358 | SPMF tvDist, no OracleComp |
| `VCVio.OracleComp.ProbComp` | 66 | 19 | 10900 | |
| `ProbComp` + `TVDist` | 69 | 19 | 11740 | needed for `tvDist (p : ProbComp Bool)` |
| `ProbComp` + `TVDist` + `MeasureTVDist.Bind` | 76 | 19 | 12486 | |
| `VCVio.OracleComp.QueryTracking.QueryBound.Basic` | 40 | 25 | 8058 | |
| `VCVio.StateSeparating.Hybrid` | 126 | 28 | 24434 | |
| `VCVio.ProgramLogic.Relational.SimulateQ.Epsilon` | 117 | 26 | 25952 | ε-until-bad |
| `VCVio.ProgramLogic.Relational.Quantitative` | 106 | 25 | 20828 | |
| `VCVio.Native` (public native entry) | 138 | 36 | 26797 | |
| `VCVio.ProgramLogic.Tactics` | 167 | 35 | 45065 | |
| `VCVio` umbrella | 502 | 149 | 124550 | |

PolyFun/ToCslib modules in the `ProbComp` closure (19 + 3 Cslib; the Cslib modules are `Cslib.Foundations.Control.Monad.IsMonadHom`, `...IsMonadHom.List`, `Cslib.Foundations.Data.PFunctor.Free`):
PolyFun.Control.Monad.{Algebra, Hom, Hom.IsMonadHom, Hom.Loops, Support, Support.Instances}, PolyFun.PFunctor.{Basic, Equiv.Basic, Free.Basic, Free.Displayed, Free.Path, Free.Support, Free.WP, Handler, Handler.Instrumentation, Lens.Basic, Obj}, ToCslib.Control.Monad.HomTransport, ToCslib.Data.PFunctor.Free.Basic.

**Recommended minimal list A (measure-native TV stack, 8 modules, Mathlib only)**
ToMathlib.Data.ENNReal.AbsDiff, ToMathlib.MeasureTheory.Integral.AbsDiff, ToMathlib.MeasureTheory.Measure.Bool, ToMathlib.MeasureTheory.Measure.Subprobability, ToMathlib.MeasureTheory.Measure.TotalVariation, ToMathlib.MeasureTheory.Measure.TotalVariation.Bind, ToMathlib.Probability.Kernel.Subprobability, ToMathlib.Probability.Kernel.TotalVariation.
Mathlib direct imports of that set: Data.FunLike.IsApply, MeasureTheory.Integral.{Layercake, Lebesgue.Sub}, MeasureTheory.Measure.{GiryMonad, Map, Prod, Typeclasses.Finite, Typeclasses.Probability}, Probability.Kernel.Composition.{Comp, MapComp, Prod}, Topology.Algebra.InfiniteSum.ENNReal, Topology.EMetricSpace.Weak (and Lebesgue.Countable via `Measure.Bool`).

**List B (`VCVio.EvalDist.MeasureTVDist.Bind`, 11 modules, no PolyFun)**
ToMathlib.Data.ENNReal.AbsDiff, ToMathlib.MeasureTheory.Integral.AbsDiff, ToMathlib.MeasureTheory.Measure.Prop, ToMathlib.MeasureTheory.Measure.Subprobability, ToMathlib.MeasureTheory.Measure.TotalVariation, ToMathlib.MeasureTheory.Measure.TotalVariation.Bind, ToMathlib.Probability.Kernel.Subprobability, ToMathlib.Probability.Kernel.TotalVariation, VCVio.EvalDist.Defs.Measure.Core, VCVio.EvalDist.MeasureTVDist.Basic, VCVio.EvalDist.MeasureTVDist.Bind.

**List C (`VCVio.OracleComp.ProbComp` + `VCVio.EvalDist.TVDist`: 69 VCVio/ToMathlib modules)**
ToMathlib.{Algebra.BigOperators.Finset, Algebra.BigOperators.List, Control.Except, Control.Functor.Prod, Control.Monad.Fold, Control.Option, Control.OptionT, Data.BitVec, Data.ENNReal.AbsDiff, Data.ENNReal.Gauss, Data.Fin.Basic, Data.List.Count, Data.Set.Functor, Data.Vector.Count, Data.Vector.Induction, Data.Vector.ListVector, Lint.LegacyProbability, Logic.Basic, MeasureTheory.Integral.Bounds, MeasureTheory.MeasurableSpace.Except, MeasureTheory.MeasurableSpace.Option, MeasureTheory.Measure.Bounds, MeasureTheory.Measure.Except, MeasureTheory.Measure.GiryMonad, MeasureTheory.Measure.IndependentDraws, MeasureTheory.Measure.Option, MeasureTheory.Measure.Prop, MeasureTheory.Measure.Subprobability, Probability.ProbabilityMassFunction.Lemmas, Probability.ProbabilityMassFunction.Measure, Probability.ProbabilityMassFunction.TotalVariation, Probability.UniformOn, ProbabilityTheory.SPMF, Topology.Algebra.InfiniteSum.Option}
VCVio.{EvalDist.Defs.AlternativeMonad, EvalDist.Defs.Basic, EvalDist.Defs.Measure, EvalDist.Defs.Measure.Core, EvalDist.Defs.Measure.Deterministic, EvalDist.Defs.Measure.ExceptT, EvalDist.Defs.Measure.Failure, EvalDist.Defs.Measure.OptionT, EvalDist.Defs.NeverFails, EvalDist.Defs.Support, EvalDist.Defs.Support.Failure, EvalDist.Instances.OptionT, EvalDist.Monad.Basic, EvalDist.Monad.Map, EvalDist.Monad.Measure, EvalDist.Monad.Seq, EvalDist.Monad.Seq.Measure, EvalDist.Monad.Support, EvalDist.Option, EvalDist.PFunctor, EvalDist.ProbabilityNotation, EvalDist.TVDist, OracleComp.EvalDist, OracleComp.HasQuery.Basic, OracleComp.OracleComp, OracleComp.OracleQuery, OracleComp.OracleSpec, OracleComp.ProbComp, OracleComp.ProbComp.Basic, OracleComp.ReachableWhen, OracleComp.SimSemantics.QueryImpl.Basic, OracleComp.SimSemantics.SimulateQ, OracleComp.Support, Prelude, Prelude.Core}
plus the 19 PolyFun/ToCslib modules and 3 Cslib modules above, and about 50 direct Mathlib imports.

Lake note (from `lakefile.lean`/README): `require VCVio from git ...` works as a dependency (native `extern_lib`s fall back to empty stubs). Resolving the manifest clones PolyFun, cslib and the other pinned packages even if unused. Lake compiles only the modules actually imported, so list A costs about 8 small modules on top of the Mathlib cache.
VCVio files use Lean's `module` system (`module`, `public import`); a plain downstream file can import them.

## 7. Worked examples close to ours

* Hybrid / q-query / distinguisher advantage:
  * `VCVio/CryptoFoundations/AsymmEncAlg/INDCPA/GenericLift.lean`: `IND_CPA_Advantage_le_sum_oneTime_stepAdversary`, `IND_CPA_Advantage_le_mul_of_oneTime_bound`, `IND_CPA_OneTime_Advantage_stepAdversary`.
  * `.../INDCPA/Oracle.lean`: `IND_CPA_LR_hybrid_zero_evalSPMF_eq_right`, `IND_CPA_LR_hybrid_q_evalSPMF_eq_left_of_MakesAtMostQueries`.
  * `VCVio/CryptoFoundations/KEMDEM/Measure.lean`: `KEMDEM.bias_compose_le`.
  * `VCVio/CryptoFoundations/DataEncapMech/RealOrRandom.lean`: `realOrRandomAdvantage_eq_IND_CPA_Advantage`, `IND_CPA_Advantage_le_realOrRandomAdvantage_add`.
  * `VCVio/StateSeparating/{Advantage/Measure,Hybrid,IndistAt,DistEquiv,IdenticalUntilBad}.lean`.
  * `Examples/ElGamal/Hash.lean` (sum of `boolDist`s), `Examples/ElGamal/SSP.lean`.
* Identical-until-bad with TV:
  * `Examples/PRGfromPRF.lean`.
  * `Examples/CommitmentScheme/Hiding/{Main,LoggingBounds/Average}.lean`: `tvDist_hidingReal_hidingSim_le_probBad`, plus averaging via `tvDist_bind_left_le`. Its docstring warns that a per-salt bound is FALSE and averaging is essential.
* Perfect-secrecy / measure-native OTP: `Examples/OneTimePad/Basic.lean`, the canonical compact example (AGENTS.md).
* Docs for writing examples (`docs/agents/`): `crypto.md` (naming: `<notion>Experiment`, `<notion>Game`, `<notion>Advantage : ℝ≥0∞`; advantage of a distinguisher = `Measure.boolDist`; `BoundedAdversary`; "Name the reduction in the theorem statement"), `end-to-end-examples.md` (Schnorr, commitments), `probability.md`, `program-logic.md`, `gotchas.md` (esp. 1, 3, 7, 9, 13), `notation.md`. CONTRIBUTING.md: header + module docstring on every new file.

## 8. Draft example files (not compiled)

### 8a. Measure-native, minimal (imports list A). Names VERIFIED from source; the elaboration details marked GUESSED are unchecked.
```lean
import ToMathlib.Probability.Kernel.TotalVariation
import ToMathlib.MeasureTheory.Measure.Bool

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Mini
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- T1: a randomised decision rule (acceptance probability `D`) cannot separate `P` and `Q`
by more than their total variation. [name VERIFIED: Measure.absDiff_lintegral_le_etvDist] -/
theorem t1 (P Q : Measure α) (D : α → ℝ≥0∞) (hD : Measurable D) (h1 : ∀ a, D a ≤ 1) :
    ENNReal.absDiff (∫⁻ a, D a ∂P) (∫⁻ a, D a ∂Q) ≤ P.etvDist Q :=
  Measure.absDiff_lintegral_le_etvDist P Q D hD h1

/-- Deterministic post-processing. [VERIFIED: Measure.etvDist_map_le] -/
theorem dpi_map (P Q : Measure α) (f : α → β) (hf : Measurable f) :
    (P.map f).etvDist (Q.map f) ≤ P.etvDist Q :=
  Measure.etvDist_map_le P Q f hf

/-- Data processing through a Markov mediator kernel `M`.
[VERIFIED: Measure.etvDist_bind_le; GUESSED: the `Kernel` -> function coercion and the
`IsMarkovKernel -> IsSubprobabilityMeasure (M a)` instance chain elaborate as written] -/
theorem dpi_kernel (P Q : Measure α) (M : Kernel α β) [IsMarkovKernel M] :
    (P.bind M).etvDist (Q.bind M) ≤ P.etvDist Q :=
  Measure.etvDist_bind_le P Q M M.measurable

/-- Mediator then randomised decision: T1 composed with data processing. [GUESSED glue, VERIFIED parts] -/
theorem t1_mediated (P Q : Measure α) (M : Kernel α β) [IsMarkovKernel M]
    (D : β → ℝ≥0∞) (hD : Measurable D) (h1 : ∀ b, D b ≤ 1) :
    ENNReal.absDiff (∫⁻ b, D b ∂(P.bind M)) (∫⁻ b, D b ∂(Q.bind M)) ≤ P.etvDist Q :=
  (Measure.absDiff_lintegral_le_etvDist _ _ D hD h1).trans (dpi_kernel P Q M)
end Mini
```
Possible fixes if `dpi_kernel` fails to elaborate: write `(P.bind ⇑M)`, or use `Kernel.etvDist_comp_le` on `Kernel.const Unit P`. The latter is VERIFIED to exist: `etvDist_comp_le (κ η : Kernel ρ α) (τ : Kernel α β) [IsSubprobabilityKernel τ] (r : ρ)`.

### 8b. ProbComp / SPMF version (imports list C: 69 + 19 modules). Both lemma names VERIFIED. The use of `abs_probOutput_toReal_sub_le_tvDist` and `tvDist_map_le` at `ProbComp` is exercised in `StateSeparating/IdenticalUntilBad.lean` and `SimulateQ/Basic.lean`, but this exact file was never compiled.
```lean
import VCVio.EvalDist.TVDist
import VCVio.OracleComp.ProbComp

open OracleComp

/-- |Pr[=true|p] - Pr[=true|q]| ≤ tvDist p q.  [VERIFIED: TVDist.lean, `abs_probOutput_toReal_sub_le_tvDist`] -/
example (p q : ProbComp Bool) :
    |Pr[= true | p].toReal - Pr[= true | q].toReal| ≤ tvDist p q :=
  abs_probOutput_toReal_sub_le_tvDist p q

/-- T1 for a randomised decision rule `D : α → ProbComp Bool`, with data processing.
[VERIFIED names: abs_probOutput_toReal_sub_le_tvDist, tvDist_bind_right_le.
 GUESSED: `LawfulMonadLiftT ProbComp SPMF` is found by instance search] -/
theorem t1_probcomp {α : Type} (P Q : ProbComp α) (D : α → ProbComp Bool) :
    |Pr[= true | P >>= D].toReal - Pr[= true | Q >>= D].toReal| ≤ tvDist P Q :=
  (abs_probOutput_toReal_sub_le_tvDist (P >>= D) (Q >>= D)).trans (tvDist_bind_right_le D P Q)
```
Expect deprecation warnings (`probOutput`, `evalSPMF` are `@[deprecated]`); they are warnings only.

## 9. Licence

* `LICENSE`: the Apache License 2.0 text (verified; ends with the unfilled `Copyright {yyyy} {name of copyright owner}` appendix boilerplate). `lakefile.lean`: `license := "Apache-2.0"`.
* All 604 `.lean` files under `VCVio/`, `ToMathlib/`, `Examples/` carry a header `Copyright (c) 20xx <author>. All rights reserved. / Released under Apache 2.0 license as described in the file LICENSE. / Authors: ...` (0 missing, checked by script).
* CONTRIBUTING.md: copied or ported material must preserve upstream attribution. Vendoring `ToMathlib` files means keeping their headers.
* Only 3 files contain `sorry`: `ToMathlib/Control/AlternativeMonad.lean`, `FiatShamir/WithAbort/Security.lean`, `GPVHashAndSign.lean`. None is in any recommended closure.

## 10. Gaps and risks for our use

* Mid-migration API: SPMF/`Pr[...]`/`probOutput` deprecated. The measure-native API is the stable direction but less ergonomic (measurability side conditions; `Measurable fun a => 𝒟[f a]` auto-discharged only for discrete source types via `Measurable.of_discrete`).
* TV is defined twice and bridged only for zero distance and `PUnit`. Pick one stack per development. The Measure stack gives the sup-over-events definition, so T1 is immediate; the PMF stack gives sum-form with DPI for maps and kernels.
* `Measure.tvDist_triangle` needs subprobability hypotheses; `Measure.etvDist_triangle` does not.
* `ProbComp` expresses only finite-tree, rational-probability programs, and `ProbComp : Type → Type` (value universe 0). Do not use it for "arbitrary" policies.
* `PMF.tvDist_map_le` / `tvDist_bind_right_le` force source and target value types into the same universe (`α' β : Type u₀`). The measure versions have independent universes.
* No packaged N-round honeypot-interleaving / audit-budget / shutdown protocol, no `Kernel.traj`-style sequential-protocol TV lemma. The `Kernel.pow` subprobability instance and the `etvDist_bind_bind_*` lemmas are the nearest tools. T3 needs a bespoke induction.
* Mathlib v4.34.0 has no TV for PMF/Measure (checked file tree). Proof-engineering gotchas: `autoImplicit=false` globally, `do`-bind simp lemmas need the `LawfulMonad.do_*` restatements (gotcha 13), no ASCII-banner comments, strict header rules if contributing upstream.
