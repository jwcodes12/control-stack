# Hostile review (Reviewer B): `ControlStack/Refinement.lean` (operational refinement of UM(n_h, hard slack n_s, b, N))

Reviewer: independent, read-only on all existing files. Scratch work: `<scratch>/` (python3, exact `Fraction`).
Lean/lake were NOT run (per instructions). All "true/false" verdicts below for the Lean statements are therefore
(a) by hand-proof sketch against the pinned VCVio sources, and (b) by exact brute force of a literal translation of the
game (see "Evidence").

## 0. Verdict

**MINOR (accept the statements as the thing to prove, after the five fixes below). No FATAL issue, no false claim found.**

- All four claims (`DeployClaim`, `DeployExactClaim`, `ProtocolClaim`, `EndToEndClaim`) are TRUE as stated, including
  the edge cases the brief lists (N = 0, b = 0, r < 0, r > 1, Bad empty, L = 0, n_h = 0, n_s >= n_h, empty X/Z/Ω).
- `deploy` / `protocolGame` are faithful to the protocol in PL_UMPROTF1's docstring and DESIGN §2.2 (order of draws,
  history entries, what the monitor sees, budget/halt rule, absorbing shutdown, benign audits, test-then-deploy, seed sharing).
- The weaknesses are not about truth. They are: (i) the headline equality is stated under an over-rigid hypothesis when a
  hypothesis-free, strictly stronger equality is available and makes both the claims and their proofs simpler; (ii) there is
  no Witness / non-vacuity statement and no operational attainment (both nearly free here); (iii) several load-bearing
  modelling assumptions are only implicit in the `ProbComp` interface and are not listed in the docstring; (iv) duplicated
  `honeypotPasses`/`binCDF`; (v) minor statement hygiene.

## 1. Evidence (what I actually ran)

`<scratch>/refine_check.py`: `ProbComp` = finite distribution monad (dict value -> Fraction; never fails).
`deploy`, `honeypotPasses`, `protocolGame` are LITERAL monadic translations of the Lean text (no use of `cat`); `cat` and
`binCDF` are literal translations of the ledger (including truncated `n - j`).

| check | instances | result |
|---|---|---|
| `Pr[deploy] = cat` (exact recall r, history-dependent generator, kernels random rational, several (n,u,h)) | 800 | 0 mismatches |
| `Pr[deploy] <= cat` (history-dependent audit with recall >= r) | 800 | 0 violations |
| `ProtocolClaim` equality (also `Pr[= k | honeypotPasses] = C(n,k) h^k (1-h)^(n-k)`) | 800 | exact |
| `EndToEndClaim` (L = exact max domination ratio of the instance, non-trivial Bad) | ~545 | 0 violations |
| adversarial: DP-optimal adaptive deterministic generator (max over x at every history) realised as a policy in the literal game; game value = DP value; random monitors | 150 x 20 | equal; `EndToEnd` bound holds, ratio game/bound reaches **1.0** (bound is tight) |
| edge grid: r in {-1,-1/2,0,1,3/2,5} (r > 1 only with Bad empty, otherwise hypothesis unsatisfiable), Bad in {empty, all, some}, (b,N,n_h,n_s) in {(0,0,0,0),(0,3,0,0),(0,3,2,5),(1,3,3,3),(2,3,4,1),(0,2,1,0),(3,2,2,0)} | 1528 | all claims hold |
| hypothesis-free general-recall recursion `catG` (proposed in §2, I-2) vs literal game with history-dependent audit | 300 | exact equality |
| operational attainment formula (I-1) vs literal game | 200 | exact |
| concrete witness of I-1: X=Z=Bool, id mediator, H = pure true, n_h=3, n_s=0, b=N=1, monitor passes w.p. 1/4, r=1 | 1 | game value 27/256 (= core `Witness`), bound 1/4 |

VCVio facts checked in the pinned sources (commit 9146f78c):
- `ProbComp = OracleComp unifSpec = PFunctor.FreeM ...`: constructors are only `pure` and uniform-query `bind`; there is no
  failure constructor, and `NeverFail` / `probFailure_eq_zero` holds. Hence `Pr[= true | c] + Pr[= false | c] = 1`,
  `sum_probOutput_eq_one` for every `Fintype` codomain (the Bridge already uses `sum_probOutput_eq_sub`).
- `ProbComp X` is *empty* when `X` is empty (an inductive tree needs a `pure a` leaf). So the "empty X / Z / Ω" cases are
  vacuous (`π []`, `M x`, `ρ` cannot exist), not problematic.
- `Pr[...]` / `probOutput` carry `@[deprecated ... (since := "2026-09-13")]` in this commit: every statement will emit
  deprecation warnings (harmless at the pin; see I-9).
- Useful lemmas for the proofs exist: `probOutput_bind_eq_sum_fintype` (Fintype.lean:26), `probOutput_ite`,
  `probOutput_map_injective`, `sum_probOutput_eq_one`, `probEvent_eq_tsum_ite`.
- The `cat` and `binCDF` bodies in Refinement.lean are byte-identical to the ledger's (checked by script; `binCDF` differs only
  by `Finset.range` vs `open Finset`'s `range`; `Hist` identical).

## 2. Issues (severity-tagged)

### I-1 [MAJOR, cheap] No Witness / non-vacuity, and no operational attainment
Every ledger file carries a `Witness`. This file has none, although its hypotheses are stranger than the core's:
`(∀ h x z, Bad x → r ≤ (Pr[= true | A h x z]).toReal)` ranges over *all* histories, `Fintype X/Z/Ω` over `ProbComp`
types, and `L`-domination of `Pr[= z | M x]` by `Pr[= z | H >>= M]`. Nothing in the file shows the hypotheses of
`EndToEndClaim` are jointly inhabited and the bound is non-trivial. (They are: I checked numerically; but the statement file
should say so in Lean, and it is the only thing that rules out a silent vacuity from instance/universe mismatches.)

Fix A (statement; one line of proof each from `ProtocolClaim` + a single unfolding of `deploy`, no induction):
```lean
/-- operational attainment (T3*): a generator that submits a fixed bad `x` at once, exact recall `r` at the root
    history, N ≥ 1, b ≥ 1. Operational twin of the core's T3*; with a monitor tuned to h ≈ 1/(n_h+1) it shows
    `EndToEndClaim`'s bound is essentially attained -/
def AttainClaim : Prop :=
  ∀ (X Z Ω : Type) [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
    (ρ : ProbComp Ω) (H : ProbComp X) (M : X → ProbComp Z) (D : Ω → Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool) (nh ns b N : ℕ) (r : ℝ) (x : X),
    Bad x → 1 ≤ N → 1 ≤ b → (∀ z, (Pr[= true | A [] x z]).toReal = r) →
    (Pr[= true | protocolGame Bad ρ H M D (fun _ _ => pure x) A nh ns b N]).toReal =
      ∑ ω, (Pr[= ω | ρ]).toReal * binCDF nh ns (Pr[= true | H >>= M >>= D ω]).toReal *
        (1 - r + r * (Pr[= true | M x >>= D ω]).toReal)

/-- Non-vacuity (mirrors PL_UMPROTF1.Witness; sketch, not compiled): X = Z = Bool, Bad = {true}, identity mediator,
    H = pure true (L = 1), r = 1, n_h = 3, n_s = 0, b = N = 1, monitor passes w.p. 1/4, generator always attacks. -/
def Witness : Prop :=
  (Pr[= true | protocolGame (fun x : Bool => x = true) (pure ()) (pure true)
      (fun x => pure x) (fun _ _ => (fun k : Fin 4 => decide (k = 0)) <$> $[0..3])
      (fun _ _ => pure true) (fun _ _ _ => pure true) 3 0 1 1]).toReal = 27/256 ∧
  (∀ z : Bool, (Pr[= z | (pure true : ProbComp Bool)]).toReal ≤ 1 * (Pr[= z | (pure true : ProbComp Bool) >>= (fun x => pure x)]).toReal) ∧
  (27/256 : ℝ) < (1 - 1) + 1 * (1 * (((0:ℝ) + 1) / ((3:ℝ) + 1)))
```
(`AttainClaim` needs no `Fintype X/Z`; the RHS is exactly the core's T3* `surv * (1 - r + r E_{M x} φ)` with the Bridge.)

### I-2 [MAJOR (strength and proof economy), not a correctness problem] State the hypothesis-free equality; derive the rest
`DeployExactClaim` requires `Pr[A h x z] = r` for *every* `(h, x, z)` with `Bad x`, including unreachable histories
(wrong budget count, entries that end the game) and `z` outside the support of `M x`. Consequences:
- It cannot be applied to any realistic audit whose recall varies with history/budget/view (the exact thing the Reviewer A #16
  "conditional recall" remark is about). The truthful operational statement for such an audit is an equality with the
  recall *function*, with no hypothesis at all.
- It forces rational `r` (see I-8) and a second, near-duplicate induction next to `DeployClaim`.

The right primary theorem (I checked it exactly on 300 random instances with history-dependent audit):
```lean
/-- `cat` with a history/view-dependent recall function `R` (textual copy of `cat` with `r` replaced by `R h x z`). -/
noncomputable def catG {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (R : Hist X Z → X → Z → ℝ) (b : ℕ) :
    ℕ → ℕ → Hist X Z → ℝ
  | 0, _, _ => 0
  | n + 1, u, h => ∑ x, π h x * ∑ z, M x z *
      (φ z * (if Bad x then 1 else catG Bad M φ π R b n u (h ++ [(x, z, true)])) +
       (1 - φ z) * (if u < b then
                      (if Bad x then 1 - R h x z else catG Bad M φ π R b n (u + 1) (h ++ [(x, z, false)]))
                    else 0))

def DeployGClaim : Prop :=            -- NO hypotheses besides finiteness of X, Z
  ∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool) (b : ℕ) (n u : ℕ) (h : Hist X Z),
    (Pr[= true | deploy Bad π M D A b n u h]).toReal =
      catG Bad (fun x z => (Pr[= z | M x]).toReal) (fun z => (Pr[= true | D z]).toReal)
        (fun h x => (Pr[= x | π h]).toReal) (fun h x z => (Pr[= true | A h x z]).toReal) b n u h
```
Then `DeployExactClaim` = `DeployGClaim` + `catG (fun _ _ _ => r) = cat` (induction, `simp`), and `DeployClaim` =
`DeployGClaim` + a monotonicity lemma `R ≥ r on Bad → catG R ≤ cat r` (induction; needs only `0 ≤ π, M, φ ≤ 1`, all
automatic from `ProbComp`). One real induction over `deploy`, two small ones over real recursions. Keep `DeployClaim` /
`DeployExactClaim` as the *published* statements if the programme wants them in the ledger-style list; just prove them
via `DeployGClaim`.

### I-3 [MINOR] `honeypotPasses` and `binCDF` are copied, not imported
The docstring says "It is the same game as `ControlStack.Bridge.honeypotPasses`", but the file re-defines both in
`ControlStack.Refine`. Then `Bridge.bridge` does not apply to `Refine.honeypotPasses` without an extra
`honeypotPasses = Bridge.honeypotPasses` induction, and nothing machine-checks the "same game" claim. The Refine and Bridge
copies of `binCDF` also double the textual-identity surface to audit against the core.

Fix: `import ControlStack.HoneypotBridgeProof` and `open ControlStack.Bridge (honeypotPasses binCDF)`; delete the two
definitions here. (Both files are in the same `lean_lib`.) `cat` stays a textual copy (it is the only object linked to the
core by text; record its CID/hash next to the ledger's).

### I-4 [MINOR] `ProtocolClaim` carries unused `[Fintype X] [Fintype Z]`; prove the factorisation generically
Nothing in `ProtocolClaim`'s statement uses `Fintype X`/`Fintype Z` (no `cat`); they only weaken it. Only `Fintype Ω`
(for `∑ ω`) is needed. Drop the other two.
Proof hint: prove once the generic gate lemma (reusable verbatim for the soft-slack test and the class-aware tests of
UMSTRAT, whose survival is not `binCDF`):
```lean
lemma gate {Ω K : Type} [Fintype Ω] (ρ : ProbComp Ω) (T : Ω → ProbComp K) (P : K → Prop) [DecidablePred P]
    (G : Ω → ProbComp Bool) :
    Pr[= true | do let ω ← ρ; let k ← T ω; if P k then G ω else pure false] =
      ∑ ω, Pr[= ω | ρ] * Pr[ P | T ω] * Pr[= true | G ω]
```
(`probOutput_bind_eq_sum_fintype`, `probEvent_eq_tsum_ite`, pull `Pr[= true | G ω]` out of the `k`-sum; independence of the
test and deployment coins given `ω` is exactly that `G ω` does not mention `k`). Then `Pr[ (· ≤ ns) | honeypotPasses .. ]`
is the Bridge. The independence "both call `D ω` with fresh coins" is correct: each `←` is a fresh run, and the only shared
object is the *value* `ω`.

### I-5 [MINOR] Load-bearing modelling assumptions are implicit in the interface and not listed in the docstring
List them (they are the content of "no hidden assumption"):
1. **A1/A2 (stateless monitor, fresh coins).** `D : Ω → Z → ProbComp Bool` cannot see the call index, the audit counter
   `u`, the history, or whether the call is a honeypot; each `←` is a fresh run. This is the single most load-bearing
   restriction (see I-10 for a one-line necessity argument). The docstring says "stateless" but never ties it to A1/A2/CLKF.
2. **Audit independence.** `A h x z` takes no `ω` and has fresh coins, so A6 is read as: Pr[catch | flag, h, x, z] >= r
   with the audit's coins independent of `ω`, the generator's coins and the monitor's coins *given (h, x, z)*. The monitor
   cannot steer recall except through `z` (good: that is the selection effect Reviewer A #16 asked about, and `∀ z` covers it).
   If the human's behaviour could depend on `ω` beyond what `(h,x,z)` reveal, the model does not cover it. State this.
3. **Generator does not see the test.** `π ω h` is not given `k` or the honeypot transcript. This is WLOG for the *bound*:
   given `ω`, the test coins are independent of every deployment coin, so
   `Pr[true] = Σ_ω ρ(ω) Σ_{k≤ns} Pr[k|ω]·Pr[deploy(π_{ω,k})]`, and `Pr[deploy(π_{ω,k})] ≤ (1-r)+r·A_ω` for every `k` (T3a is
   pointwise in the policy); so the sup is unchanged. It matters only if the test and deployment are interleaved or the
   monitor is stateful (A4). The docstring should say "WLOG, by independence" instead of leaving it silent (DESIGN F6 says it
   was only checked numerically). If one wants it in Lean: `π : Ω → ℕ → Hist X Z → ProbComp X` with `k`; `EndToEnd` goes
   through unchanged pointwise in `(ω,k)`.
4. **Generator information is maximal.** It sees `(x, z, pass)` for every past round, hence `u`; the game gives the
   generator everything the protocol reveals (not less adversarial than the real protocol on this axis).
5. **Everything is finite-support and rational** (I-8), and `X, Z, Ω` are `Fintype` only so that `cat` can use `∑`.

### I-6 [MINOR] `EndToEndClaim` is mislabelled as "the operational form of PL_UMPROTF1's domination bound"
It is strictly **more** general than the core in one axis and strictly **less** general in another:
- more: the audit may depend on `(h, x, z)` with recall >= r (the core's `cat` has constant r; STACK.md says the
  "conditional-recall refinement is open"). Closing that is a real gain, but its scope is "conditional on (h,x,z) with
  audit coins independent of everything else" (I-5.2), not conditional on the adversary's private state.
- less: hard slack and the L-domination form only (no hockey-stick, no soft slack). So it is not "the" operational form of
  T3, and `STACK.md` should not read as if all three T3 forms were refined.
No overclaim in the Lean text itself. Fix the docstring wording and the later STACK.md row accordingly.

Derivability check (the question "is EndToEnd derivable from DeployClaim + ProtocolClaim + T3a + T3c?"): YES, but T3a and
T3c are *not* available in this project (separate Lake project, Lean 4.34 vs 4.35, linked only by text), so they must be
re-proved here (statement says so). Derivation per ω with `h_ω = Pr[= true | H>>=M>>=D ω].toReal ∈ [0,1]`:
`A_ω := min 1 (L·h_ω)` satisfies `E_{M x} φ_ω ≤ A_ω` for bad x (domination, ∑_z); `IsKernel M`, `IsRule φ_ω`, `IsDist (π ω h)`
all hold automatically (no failure). T3a gives `cat ≤ (if u<b then 1-r+rA else A) ≤ 1-r+rA` (the `u≥b` branch needs
`A ≤ 1-r+rA`, i.e. `(1-r)(1-A) ≥ 0`, true since `A ≤ 1`, `r ≤ 1`). Then
`Σ_ω ρ_ω binCDF·(1-r+rLh_ω) ≤ (1-r)·1 + rL·sup_h h·binCDF(n_h,n_s,h) ≤ (1-r) + rL(n_s+1)/(n_h+1)` using `binCDF ≤ 1` (it is
a probability, via the Bridge), `Σ ρ = 1`, and T3c. Size estimate for the in-project re-proofs: T3a ~40 lines (induction on
`n`, three cases: bad/PASS, bad/FLAG, benign), T3c ~50 lines via `Nat.add_one_mul_choose_eq` and `∑_{j≤n+1} P_{n+1}(j) = 1`.
Alternative with less glue: prove the T3a bound *directly on the game* in `ℝ≥0∞` by induction on `deploy` (hypothesis
`Pr[ pass | M x >>= D ] ≤ A` for bad `x`), skipping `cat` entirely for `EndToEnd` (keep `DeployClaim` for the fidelity link).

### I-7 [MINOR] Recall hypothesis quantifies over unreachable `(h, z)`
`∀ h x z, Bad x → r ≤ …` forces recall >= r also for `z` with `Pr[= z | M x] = 0` and for impossible histories. Sound
(only strengthens the hypothesis) but needlessly narrows the class of audits. Cheap improvement for `z`: add
`Pr[= z | M x] ≠ 0 →` (the term is multiplied by `M x z`, so the proof is unchanged). For `h`, restricting to reachable
states costs a reachability predicate; not worth it once I-2 is adopted (the hypothesis-free equality makes the question
moot: the audit's recall function is whatever it is, and `catG` is the exact value).

### I-8 [INFO] ProbComp probabilities are rational; `DeployExactClaim` is vacuous for irrational r
Every `ProbComp` is a finite-depth tree of uniform `Fin (n+1)` draws, so every `Pr[= x | c]` is a rational number. Hence
`Pr[A]=r` forces `r ∈ ℚ`, and the core's irrational values (e.g. T3* attainment with irrational `φ`) have no operational
twin. Harmless (rationals are dense; all inequalities are for arbitrary real `r`, `L`), but it is one more reason to prefer
the hypothesis-free `DeployGClaim`, and the docstring's "no finite real-valued kernel is assumed" should add "but the
probabilities are rational and `X, Z, Ω` are `Fintype`". (Also: every `ProbComp` has finite support, so `Fintype X/Z/Ω`
is w.l.o.g. mathematically, only a notational price for `cat`.)

### I-9 [INFO] Deprecation of the `Pr[...]` API at the pin
`probOutput`/`probEvent`/`probFailure` are marked deprecated since 2026-09-13 ("use `𝒟[mx] {x}`"). The Bridge already
depends on them; keep the pin (9146f78c) and note that a VCVio bump will force a statement-level rewrite (and therefore
new CIDs).

### I-10 [INFO] Facts the brief asked about, answered
- `DeployClaim` without `r ≤ 1` / `0 ≤ r`: true for every real `r` (r < 0: the hypothesis is vacuous-true and the bound
  `1-r > 1` is only larger; r > 1 with a bad submission and at least one view: hypothesis unsatisfiable since a
  probability is ≤ 1; with Bad empty `r` never occurs in `cat`). Adding `0 ≤ r ≤ 1` would only weaken it.
- `DeployExactClaim`: true; for `r ∉ [0,1]` and Bad nonempty it is vacuous (correct); with Bad empty `r` is absent.
- `N = 0, b = 0` (first flag halts), `nh = 0` (`binCDF 0 s h = 1`), `ns ≥ nh` (`binCDF = 1`, game always deploys): all
  consistent between game and recursion (checked in the edge grid).
- Stateless-monitor necessity (why I-5.1 matters): with a call-counter monitor `D' ω (i, z)` that flags every call with
  `i ≤ n_h` and passes call `n_h + 1`, the test is survived with probability 1 and a first-round bad submission passes
  with probability 1: catastrophe probability 1, versus the stateless bound `(1-r) + rL(n_s+1)/(n_h+1)`, e.g. 1/4 at
  `r = 1, L = 1, n_h = 3, n_s = 0`. So A1/A2 are not a convenience; they are the theorem.
- Induced kernels: `toReal ∘ probOutput` is the right bridge object. Every `IsKernel`, `IsRule`, `IsDist` the core's T3
  needs (`M`, `φ_ω`, `π ω h`, `ρ`, `PH`) holds *automatically*: `Pr[⊥ | c] = 0` (`NeverFail`) gives
  `∑ z, Pr[= z | c] = 1` (`sum_probOutput_eq_one`), each term is ≤ 1 hence finite, so `ENNReal.toReal_sum`/`toReal_mul` apply.
  `DeployClaim`/`DeployExactClaim` themselves need none of `IsKernel`/`IsDist` (only `0 ≤ weights`, `φ ≤ 1`,
  and `Pr[= false | D z] = 1 - Pr[= true | D z]`, the same `key` lemma as in the Bridge).

## 3. Fidelity audit of `deploy` / `protocolGame` (item 1 of the brief)

Line by line against `PL_UMPROTF1.cat` / `protocolCat` and DESIGN §2.2:
- order of draws `x ← π h`, `z ← M x`, `pass ← D z`: matches `cat`'s `∑ x π h x ∑ z M x z (φ z …)`;
- PASS & bad: `pure true` (catastrophe, absorbing); PASS & benign: continue with `h ++ [(x,z,true)]`, `u` unchanged: matches;
- FLAG & `u < b` & bad: `!caught <$> A h x z` (caught = absorbing shutdown, A11; escape = catastrophe): `1 - r` in `cat`; FLAG & `u < b` &
  benign: continue with `u+1`, `(x,z,false)`: matches; FLAG & `u ≥ b`: `pure false` (halt, safe): matches (incl. flagged bad);
- test: `k ≤ ns` after `nh` fresh honeypots, then `deploy … N 0 []`, with `D ω` and `π ω` sharing `ω` and `H`, `M`, `A`
  independent of `ω`: matches `hardKill ns` (the (ns+1)-th miss kills) and `surv … nh 0`; `binCDF` is `P(Bin ≤ ns)`.
- Nothing in the game is less adversarial than the real protocol *given A1–A4, A6, A11*: generator has full perfect recall
  and sees `ω`; audit kernel is chosen last, after `(ρ, D, π)`, so it is worst-case over all kernels with recall >= r;
  `A` may be history-dependent; test result invisibility is WLOG (I-5.3).
- The one place the game is *narrower* than the real world is the audit's independence from `ω` (I-5.2) and the stateless
  monitor (I-5.1); both are assumptions, now to be written down.

## 4. Proof-difficulty notes (item 5)

- `if Bad x then pure true else deploy …`, `if u < b`, `if pass`: all plain `ite` on decidable props; use
  `by_cases hb : Bad x` then `simp [hb]` (do not let `simp` split inside the tsum). `probOutput_ite` is a `@[simp]` lemma.
- `h ++ [(x,z,·)]`: harmless, because the induction is `induction n generalizing u h` and `h` is universally quantified in
  the IH. (A cons-list history would shorten `cat`, but it would break textual identity with the core; keep as is.)
- Use `probOutput_bind_eq_sum_fintype` (not `tsum` then `tsum_fintype`) three times, then `Fintype.sum_bool` for `pass`;
  `Pr[= true | (fun c => !c) <$> A …] = Pr[= false | A …]` is `probOutput_map_injective` with `Bool.not` injective.
- toReal of ENNReal sums: do the step lemma once in `ℝ≥0∞`, then convert once with `ENNReal.toReal_sum` (every summand is
  `≠ ⊤` since `≤ 1`); do not convert inside the induction.
- Recommended order: (1) step lemma `deploy_succ` (ENNReal), (2) `DeployGClaim` by induction, (3) `catG_const`, `catG_mono`,
  (4) `gate` + Bridge ⇒ `ProtocolClaim`, (5) T3a, T3c in-project ⇒ `EndToEndClaim`, (6) `AttainClaim`, `Witness`.

## 5. Is this the most valuable operational statement at this cost? (item 6; at most two additions)

Yes: `ProtocolClaim` + `DeployG/Exact` is exactly what the final review said was missing (fidelity of the recursion to the
operational protocol rested on simulation), and `EndToEndClaim` is a cheap corollary once T3a and T3c are in the project.
Two additions, in priority order:
1. **I-1 `AttainClaim` + `Witness`.** Operational tightness and non-vacuity at the cost of one unfolding; it also turns
   `EndToEndClaim` into a two-sided statement ("the bound is attained by an explicit colluding pair") and discharges the
   missing non-vacuity convention.
2. **Stateless-monitor necessity (I-10).** Extend `deploy`/`honeypotPasses` with the call index (`D : Ω → ℕ → Z → ProbComp Bool`)
   and prove the counting-monitor pair gets catastrophe probability 1 against the same parameters. It is ~40 lines and
   machine-checks that A1/A2 (not any other modelling detail) carry the guarantee; this is the honest "out of model"
   entry the programme currently states only in prose (CLKF/LUREF are informal). I would NOT spend on the hockey-stick form
   here: its core proof depends on the testing lemma T2 (the `max 0` sums), which would have to be re-proved in this project
   for a bound that adds no new operational content over the `catG` equality; and the "generator sees the test" variant
   is WLOG (I-5.3) and not worth a separate statement.

## 6. Fixes in priority order

1. **I-2**: add `catG` and `DeployGClaim` (hypothesis-free equality); derive `DeployClaim`/`DeployExactClaim` from it.
2. **I-1**: add `AttainClaim` and `Witness`.
3. **I-3** + **I-4**: import `Bridge.honeypotPasses`/`binCDF`; drop unused `Fintype X/Z` from `ProtocolClaim`; prove a generic `gate` lemma.
4. **I-5** + **I-6**: put the five modelling assumptions in the docstring (A1/A2 statelessness and fresh coins; audit independence of `ω` and coins;
   generator not shown the test, WLOG by independence; generator information maximal; rational/finite-support) and re-label `EndToEndClaim`
   ("hard slack, domination form, audit with conditional recall >= r on (h,x,z)"; not "the" operational form of T3).
5. **I-7** (optional): add `Pr[= z | M x] ≠ 0 →` to the recall hypotheses.

Overall: **MINOR / accept** — prove it after fixes 1-4; none of the issues changes a truth value, and the brute-force evidence
(exact `Fraction`, ~4000 instances, adaptive adversarial generators, edge grid) agrees with every claim.
