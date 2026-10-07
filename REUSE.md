# REUSE: what the control stack builds on, and why

Phase 0, 2026-10-07. Sources were read via `gh api` / raw GitHub (scout reports; `scout/atlas.md` and `scout/vcvio.md`
are included in this export, the action-layer and ControlArena scouts are not). Only VCVio was built.

## Decisions

| resource | licence | toolchain (checked) | decision | why |
|---|---|---|---|---|
| **VCVio** `Verified-zkEVM/VCVio` @ `9146f78c` | Apache-2.0 (per-file headers) | v4.34.0, Mathlib v4.34.0, PolyFun `3710d71` | **dependency of the root Lake project** (interface level) | builds cleanly; has the TV / distinguisher API we need for the crypto-style statement form. Its `probOutput`/`probEvent` notation is deprecated at this commit ("retiring probability API: use `𝒟[mx] {…}`"), so the quantitative core does not sit on it yet |
| Mathlib (shared 4.35 project) | Apache-2.0 | v4.35.0-rc3 | **core level** (all ledger-gated theorems) | `Finset.sum` real arithmetic; `PMF.binomial` (`Mathlib/Probability/ProbabilityMassFunction/Binomial.lean`) and `ProbabilityTheory.binomial` exist. Mathlib has **no** TV, hockey-stick or f-divergence (only `klDiv` with DPI), so we prove our own finite versions |
| AI Safety Formalization Atlas `mbrcic/…` | Apache-2.0 (no per-file headers) | v4.33.0 + PFR, Foundation, Causalean | **not used, nothing vendored** | no TV, hockey-stick, advantage or indistinguishability. Its DPI is mutual information on PFR (does not port to 4.35 without bumping PFR). OversightBudget is three thin corollaries of an entropy bound. `Knowable` is deterministic factorisation |
| CapacityAtlas `TomasOrtega/CapacityAtlas` | Apache-2.0 (headers on 89/98 files) | v4.32.0, Mathlib only | **not used** | Shannon capacity via mutual information; no TV, advantage or binomial tails. Its real-valued `FiniteDistribution`/`FiniteChannel` plumbing is a pattern we follow in about 40 lines rather than vendor |
| TestingLowerBounds `RemyDegenne/testing-lower-bounds` | Apache-2.0 (headers) | v4.35.0-rc2 | **correspondence target, not a dependency** | has measure-theoretic `eGamma` (hockey-stick) with kernel DPI `eGamma_comp_le` and `tv` with `tv_comp_le`, but on general measures with a heavy StatInfo/DeGroot closure. Our finite `hs η` is `eGamma` with γ = e^η on counting measures. A bridge is a later option |
| StatLean `statopia/statlean4` | **none: read only, never copy** | v4.28.0-rc1 | names only | has `neyman_pearson_optimality`, `typeII_add_power`, `totalVariationDist`, `scheffe`, Hoeffding/McDiarmid/DKW. It has no binomial tails, no TV-as-test-advantage, no Pinsker, no optional stopping, so nothing we need is missing because of the licence |
| Cedar `cedar-policy/cedar-spec` `cedar-lean/` | Apache-2.0 | HEAD v4.34.1; last v4.34.0 commit `3f51c8f7` | **Phase 3 dependency (action layer)**, pinned to `3f51c8f7` in control-stack | Batteries only (same rev as our lock), no Mathlib. `Cedar.Spec` (`isAuthorized`, `evaluate`) is 25 files / 3.2k lines. Theorems: `forbid_trumps_permit`, `default_deny`, `allowed_only_if_explicitly_permitted`, `order_and_dup_independent`. Pitfalls: `inₑ` is a one-step ancestor lookup, and an erroring `forbid` fails open |
| Veil `verse-lab/veil` | Apache-2.0 | v4.32.0 + lean-smt/cvc5/Loom | **rejected** | toolchain clash; default `veil.smt.trust=true` closes goals with `sorry`, and lean-smt has literal `sorry`s. `Reachable` (about 60 lines) is re-derived in plain Lean |
| Aeneas / hax | Apache-2.0 / Apache-2.0 | Lean backend v4.31 | later | VCVio's own lakefile keeps both disabled at 4.34 |
| ControlArena | MIT | Python | correspondence only (CORRESPONDENCE.md) | no honeypots, untrusted monitoring or shutdown in code |

## VCVio API used (exact names, `.lake/packages/VCVio`)
- `ProbComp := OracleComp unifSpec` (`VCVio/OracleComp/ProbComp/Basic.lean:31`).
- `tvDist (mx my : m α) : ℝ := SPMF.tvDist 𝒮[mx] 𝒮[my]` (`VCVio/EvalDist/TVDist.lean:73`).
- `tvDist_bind_right_le (f : α → m β) (mx my : m α) : tvDist (mx >>= f) (my >>= f) ≤ tvDist mx my`
  (kernel data processing).
- `tvDist_map_le` (deterministic data processing); `tvDist_triangle`, `tvDist_le_one`.
- `abs_probOutput_toReal_sub_le_tvDist (game₁ game₂ : m Bool) :
   |Pr[= true | game₁].toReal - Pr[= true | game₂].toReal| ≤ tvDist game₁ game₂` (distinguisher bound).
- `PMF.tvDist`, `PMF.etvDist` (`ToMathlib/Probability/ProbabilityMassFunction/TotalVariation.lean`: `ℝ≥0∞`, `tsum`).
- Not yet used, but available for T3's bridge: `tvDist_bind_left_le`, `tsum_probOutput_toReal_mul_tvDist_le_probEvent`
  (identical-until-bad), `simulateQ`, `QueryImpl`.

Spike: `ControlStack/Spike.lean` proves `distinguish_le_tv` (T1 for arbitrary `ProbComp` distinguishers through a
`ProbComp` mediator) and `mediated_tv_le`. It compiles with `lake env lean` in 26 s, 3.1 GB RSS, no errors.

## Costs (measured)
| step | wall time | disk |
|---|---|---|
| `lake update` (clone VCVio, Mathlib v4.34.0, PolyFun, …) + automatic Mathlib cache (8906 files) | 5.4 min | — |
| explicit `lake exe cache get` (already complete) | 23 s | — |
| build `VCVio.EvalDist.TVDist` + `VCVio.OracleComp.ProbComp` (69 VCVio + 19 PolyFun modules; 3103 jobs incl. Mathlib replay) | about 4 min of compilation on 2 cores | VCVio build 76 MB, PolyFun 22 MB |
| totals | | `control-stack/.lake` 8.5 GB + toolchain v4.34.0 3.0 GB = **11.5 GB**; free space 45.9 GB → **32.7 GB** (≥ 15 GB rule holds) |

No third Lake project. No Mathlib built from source.

## Vendored slices
None. Neither Atlas repo has a slice that our theorems need, and TestingLowerBounds' slice is measure-theoretic and
heavy. The shared 4.35 project is unchanged.

## Gate integration
- The ledger gate compiles `import Mathlib` in the shared 4.35 project. Core stack theorems use it unchanged.
  `ledger-check/check.py` reproduces the assembly the gate performs.
- A statement may reference definitions of its declared (transitive) dependencies.
  - Statement checks compile the dependency statements first.
  - The gate includes only *verified* dependencies (statement and gated proof, each proof in its own namespace).
  - The red-team prompt shows the dependency statements.
- VCVio-level bridge lemmas are checked with `lake env lean` + `#print axioms` in the root Lake project, outside the
  ledger. Extending the gate to a per-campaign Lean environment is possible; it is deferred.

## Sandbox lesson (the action-layer target)
A bubblewrap policy for untrusted provers that starts from a **writable host root** (`bwrap --dev-bind / /`) and only
tmpfs-masks a list of hidden directories confines reads (for the listed directories) but not writes: an untrusted
process can modify toolchain directories that a later, unsandboxed checker executes. Other boundary questions (no PID
namespace, so possible reads through `/proc/<pid>/root`; no network isolation; readable credential files) are outside
the mount-table model. This was the concrete target for the first action-layer step: model a mount table, then prove
the intended property for a fixed policy (SANDBOXF1, SANDBOX2F1).
