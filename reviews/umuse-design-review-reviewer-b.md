# UMUSE design review (hostile): Reviewer B, 2026-10-07

Scope: the draft statement `PL_UMUSEF1` in `reviews/umuse-design-review-prompt.md` against the frozen dependencies
(UMHSF1, UMSURVF1, UMPROTF1; UMSTRATF1/UMLOWERF1 read from `ledger/`). I did not run Lean. Every numeric claim
below was recomputed in exact `Fraction` arithmetic (small instances) or independent float code (large `n`).
Scratch scripts: `<scratch>/` (`lib.py`, `check_ab.py`, `check_cde.py`, `check_e.py`, `check_more.py`,
`check_partition.py`, `final_forms.py`, `dwit.py`, `table.py`). Nothing in the repository was modified.

## 0. Verdict: MAJOR (revise before freezing)

- **One conjunct is false as typed**: (c), second part, when `κ` is not constrained to `[0,1]` (section 1, F1). One-line fix.
- **(a) and (b) are true, faithful, and worth freezing** (472 and 282 exact random instances, edge cases included).
- **(d) is true** (0 violations on 10,261 grid points; ratio up to 0.975, so it is tight). It is the weaker of two
  available lemmas (Cantelli is stronger at the same cost) and it points in the necessary-slack direction only.
- **The mimicry floor (c)/(e) is not degenerate but it is dominated and mislabelled.**
  - It equals the value of a *view-blind* monitor, so "mimicry", "fresh honeypot draws" and the hypothesis
    "P_H supported on Bad" are all unnecessary (F2).
  - Its hypothesis contradicts the design (A9: `P_H` lives on a superset `B̄ ⊋ Bad`).
  - The honest rates `α₀, f₀` are free parameters, so the "Pareto statement" has no trusted-only content (F3).
  - (e) restates (b), the frozen T3 verbatim, and (c) (F4).
- **The best small frontier statement** is the product inequality `α₀ · honestUse ≤ risk(view-blind pair) ≤ UMPROT bound`,
  plus the honest-ROC constraint `α₀ + f₀ ≥ 1 − TV(M·μ, M·P_H)` from UMHS T1/T2. Both are one-page proofs from frozen
  results (section 6).
- Overall: freeze (a), (b), a corrected (c'), the product inequality (P), (d) in Cantelli form, and the honest-ROC
  constraint (f). Drop (e) as a separate conjunct. Details in section 9.

## 1. Findings (severity-tagged)

### F1. FATAL as typed (trivially fixable): (c) second conjunct is false for `κ` outside `[0,1]`
Where: `Claim (c)`, `survH (missRate M PH φ₀) κ nh 0 * missRate M PH φ₀ ≤ protocolCat ...`.
There is no hypothesis on `κ`. The identity (first conjunct) is algebraic and survives, but the inequality needs
`survH ≥ 0`.

Counterexample (exact; reproduced by `check_cde.py`):
- `X = Z = Bool`, `Bad = {true}`, `M = id`, `PH = δ_true`, `φ₀ ≡ 9/10`, `κ ≡ 2`, `nh = 1`, `r = 1/2`, `b = 1`, `N = 1`.
- `S = survH (9/10) κ 1 0 = (1/10) + (9/10)(1 − 2) = −4/5`.
- floor `S·α₀ = −18/25`; `protocolCat = S·(9/10 + (1/2)(1/10)) = −19/25`.
- `−18/25 ≤ −19/25` is false.

In 800 random exact instances: 0 violations of the identity; 33 inequality violations, all with `κ ∉ [0,1]`; 0 with
`κ ∈ [0,1]` (rerun on 600 more: 0 / 16).

Fix (either):
```lean
-- add to (c):  (∀ i, 0 ≤ κ i ∧ κ i ≤ 1) →
```
or state the inequality only for `hardKill ns` (as (e) does, where it is fine), or replace (c) by (c') and (P) below.

Not affected: (a), (b) (identities, hold for arbitrary real `κ`, checked), (d), (e).

### F2. MAJOR: the mimicry floor is dominated by a view-blind pair, and its hypothesis does not match the design
(c) pairs the honest `φ₀` with a generator drawing fresh `x ~ P_H`. But `survH` depends on the monitor only through
`h = E_q φ` (frozen T3b). So **a monitor that ignores its view and PASSes with probability `h := α₀`**, paired with a
generator submitting *any one fixed* `x ∈ Bad`, has the same survival `survH α₀ κ n_h 0` and passes the attack with
probability exactly `α₀` (since `∑_z M x z = 1`). Exact value (checked on 316 random instances with `P_H` *not*
supported on Bad, `b ∈ 0..3`, `r ∈ {0,1/2,1}`):

`protocolCat (view-blind h, fixed bad x) = survH h κ nh 0 · (h + [0<b](1−r)(1−h))`.

For `b ≥ 1` this is the frozen T3* attainment with `φ = const h`; only `b = 0` is new.

Consequences:
1. "Mimicry", "fresh honeypot draws" and the hypothesis `∀ x, PH x ≠ 0 → Bad x` are unnecessary. The floor needs only
   `∃ x, Bad x`. The hypothesis is also *inapplicable to the intended design*: STACK/DESIGN A9 puts `P_H` on a
   Blue-enumerable superset `B̄ ⊋ Bad`, so (c)/(e) cover only the idealised `B̄ = Bad` case. With `P_H` having benign mass
   the identity is false (instance: `nh = 0, b = 1, N = 2, r = 1`, half the honeypot mass benign: `protocolCat = 3/40`,
   formula `α₀ = 1/10`).
2. The honest rule enters only through the number `α₀`. The "honest monitor" has no role beyond calibrating `h`.
3. Under the draft's hypotheses `max_{x∈Bad} E_{Mx}φ₀ ≥ ∑ PH x E_{Mx}φ₀ = α₀`, so (c) is the frozen T3*
   attainment averaged over `P_H` (plus a `b = 0` case). Triviality is acceptable per the owner; the point is the
   hypotheses and the name.
4. **The view-blind family gives a floor that is at least as large as the mimic floor at every row of the DESIGN
   table** (recomputed): `R(n,s) := sup_h h·binCDF(n,s,h)`.

   | n_h | α₀ | n_s | mimic `surv·α₀` | view-blind sup R | counting UB `(n_s+1)/(n_h+1)` (L=1) |
   |---|---|---|---|---|---|
   | 30 | 0.05 | 3 | 0.0470 | 0.0649 | 0.1290 |
   | 100 | 0.05 | 8 | 0.0468 | 0.0519 | 0.0891 |
   | 1000 | 0.05 | 59 | 0.0457 | 0.0458 | 0.0599 |
   | 10000 | 0.05 | 528 | 0.0452 | 0.0474 | 0.0529 |

   At `L = 1` (every bad view equals the honeypot view) T3a plus `S(h)` give `protocolCat ≤ sup_h S(h)(1−r+rh)`, and
   the view-blind pair attains it. So at `L = 1` the game value is exactly `sup_h binCDF(n_h,n_s,h)(1−r+rh)` (b ≥ 1)
   and the mimic floor is the value of that same family at the single point `h = α₀` (within 1.4x of the sup in the
   table: 0.047 vs 0.065 at `n_h = 30`; 1.00x at `n_h = 1000`).

Fix: replace (c) by the view-blind statement (c') (section 9). Keep the docstring sentence about the honest monitor
only as the *motivation* for choosing `h = α₀`.

### F3. MAJOR: the Pareto statement has no trusted-only content because `α₀` and `f₀` are unconstrained; "no capability" is wrong
- `α₀ = E_{M·P_H} φ₀` and `f₀ = E_{M·μ}(1−φ₀)` are rates of an *arbitrary* rule. They are measurements of the honest
  monitor's ability, i.e. capability statistics, not trusted components. The docstring's "This needs no collusion, no
  seed and no capability" is false for the *floor value* (it is `α₀`-valued); at most it means "no assumption on the
  adversary". The usefulness half is conditional on a measured honest profile and on `μ`; say so, and say that this
  half is *not* capability-free.
- Worse, the draft lets the honest monitor have `α₀ = f₀ = 0` for every `(M, P_H, μ)`. That is only possible if the
  mediated honeypot and benign laws are disjointly supported. UMHS already constrains it, for free:

  `1 − f₀ − α₀ = E_{M·μ}φ₀ − E_{M·P_H}φ₀ ≤ hs 0 (M·μ) (M·P_H)` (T1), and more generally
  `1 − f₀ ≤ e^η α₀ + hs η (M·μ) (M·P_H)` for every real `η` (T2).

  Checked on 2000 random exact instances: 0 violations. Data processing (T4a) gives
  `hs 0 (M·μ)(M·P_H) ≤ hs 0 μ P_H`: **mediation can only hurt the honest monitor**. This is the real
  safety/usefulness tension of the whole stack: the mediator must destroy attack/honeypot distinguishability
  (small `L`; T4c' says `L ≥ e^{ℒ(M|B̄)}` for content-preserving `M`), and it can't do so without also degrading the honest
  ROC. It is capability-free (all three laws are trusted components) and costs one line each. It is the only conjunct
  I know of that puts a *trusted-only* quantity on the usefulness side. See (f) in section 9.
- Also unaddressed: "honest" here also means *honest at the audit step*: benign flagged items are audited and always
  cleared (audit specificity 1). A false-positive audit would be a false shutdown not counted in `haltP`.

### F4. MAJOR: (e) is a restatement; the "frontier" is a corridor; the docstring sentence is misleading
- (e) conjunct 1 is (b) second part verbatim. Conjunct 2 is the frozen T3 domination form verbatim. Conjunct 3 is (c)
  at `hardKill`. Nothing new is derived; the conclusion `floor ≤ UB` is not even asserted. Duplicating a frozen
  statement in a second namespace is a drift risk.
- "So no choice of (n_h, n_s) certifies risk below (honest test survival) × α₀" reads as an impossibility. It is a
  *curve*: the floor `surv(n_h,n_s,α₀)·α₀` is small whenever `n_s` is small, and the honest survival collapses with it.
  The content only appears when combined with usefulness: **usefulness ≥ u ⇒ risk ≥ α₀·u** (the product inequality (P);
  `honestUse ≤ surv`). That is the actual Pareto line through the origin, and it holds for every `κ ∈ [0,1]`, every
  `b`, `N`, `r`, not only hard slack.
- Width of the corridor at realistic budgets (`n_h ≤ 100`; DESIGN §5): floor 0.009–0.047, counting UB at `L = 1`
  0.03–0.09, actual attained risk of the decodable designs 0.03–0.48 (table in section 5). So the frontier is tight
  only at `L = 1` or `n_h ≳ 10^3–10^4`. Call it a *sandwich* or *corridor*, not a frontier.
- `b` is degenerate in the safety half. First-bad-decides makes `b` matter only through `[0 < b]`. The draft's UB
  `(1−r) + r L (n_s+1)/(n_h+1)` carries the `1−r` term for **b = 0** too, where the true bound has no `1−r` (frozen
  T3a: `cat ≤ A` when `u ≥ b`). So at `b = 0` the corridor is loose by `1−r` for no reason. And the floor drops the
  `(1−r)(1−α₀)` that the exact value (c) contains. Both ends of the corridor lose the only place where `b` matters.

### F5. MAJOR: "usefulness" is not the literature's usefulness, and the iid model is optimistic
- `honestUse = P(no halt in N rounds)` is a *full-run probability*. Greenblatt et al. 2312.06942 (Fig. 2, Tables 3, 7),
  Ctrl-Z 2504.10374 (§2.3, Fig. 2) and LASR 2602.20628 (§2) define usefulness as a rescaled correctness rate / the
  *proportion of tasks completed by U*. Both are legitimate; the draft should name its quantity (`fullRunProb`) and
  add the other. It is a corollary of (a) applied at each horizon: `E[completed rounds] = ∑_{n=1}^{N} binCDF n b f₀`.
  At `N = 1000, b = 25, f₀ = 2%`: full-run probability 0.890, expected completed fraction 0.989. A factor 10 in loss.
- iid benign stream = exchangeable-with-constant-`f₀`. Real streams have task-difficulty mixtures; `P(Bin(N,f) > b)`
  is convex in `f` below the mode, so Jensen makes the iid formula **optimistic**. Example: `N = 100, b = 5`,
  `f ∈ {0.5%, 5%}` equally likely (mean 2.75%): iid false halt 5.8%, mixture 19.2%. The docstring lists "history-dependent
  honest streams" as not claimed but not this direction of bias.
- `b ≥ N` is a degenerate regime: `binCDF N b f = 1` for every `f`, so "always flag + audit everything" has
  usefulness 1 and risk `1−r`. The docstring's statement that always-flag is "useless" needs `b < N`.
- Product form: `honestUse = surv × (1 − haltP)` mirrors `protocolCat`'s own `surv × cat` product. It is a faithful
  mirror (same defining structure, honest rule has no seed), but "it is a product *because* ... fresh (A1)" overstates:
  it is a product *by definition of the recursion*; whether the operational protocol equals the recursion is the open
  VCVio bridge (STACK item 5), same status as UMPROT. Retraining-style slack (LASR App. E) would break it.

### F6. MAJOR: the headline design (class-aware slack) has no honest-side identity; (d) points the wrong way and is loose
- DESIGN §5's table and the brief's reading ("class-aware slack approaches α₀") rest on the class-aware design, but
  UMUSE contains no honest-side statement for it ("not stated here"). It is one line from frozen results:
  `stratSurv K Es φ₀ m sc = ∏_{e∈Es} binCDF m sc (∑_z K e z φ₀ z)` (T3b per class, hard slack). Freeze it as (b').
- (d) lower-tail Chebyshev gives a *necessary* condition `n_s ≥ nα − σ/√(1−ε)`. Its one-sided refinement (Cantelli,
  same moment lemma, same proof effort) gives `n_s ≥ nα − σ√(ε/(1−ε))`, 3x tighter at `ε = 0.1`.
  Example `n = 1000, α = 0.05`: Chebyshev `n_s ≥ 42.7`; Cantelli `47.7`; exact needed for false shutdown ≤ 10%: 59
  (normal approx 58.8). So the (d)-corollary understates required slack by ≈ 16 (i.e. 2.3σ), and the UMLOWER-based
  floor `k(n_s+1)/(4n)` inherits it (0.087 vs the true 0.12 at `k = 8`; actual risk 0.383).
- The direction needed for the *positive* claim ("class-aware slack sized for ε is at most about α₀ + small") is the
  **upper tail** (`n_s` sufficient): `(s+1−nα)²(1−binCDF n s α) ≤ nα(1−α)`. Checked: 0 violations / 14,003 grid points. In
  Cantelli form 0 / 10,409. Same proof as (d) (partial second moment ≥ ...). As a closed form it is loose (at
  `n = 10^4, k = 8, α = 0.05, ε = 0.1`: Cantelli-sized `s_c+1 = 131`, bound 0.105; exact `s_c = 80`, bound 0.0647, attained
  0.051; floor 0.045). So use it only as an asymptotic statement; keep exact binomial arithmetic for numbers.

### F7. MINOR: Witness weaknesses
- `α₀ = f₀ = 1/10` and `wφ` symmetric: a swapped `missRate`/`flagRate` definition (or swapped roles of `φ₀` and `1−φ₀`)
  would still pass. Use an asymmetric profile, e.g. `wφ true = 1/10`, `wφ false = 4/5` (so `α₀ = 1/10`, `f₀ = 1/5`).
- The Chebyshev witness (`n = 10, s = 1, α = 1/2`: `11/64 ≤ 5/2`) has slack 14x, so it would not catch a wrong
  constant. Use `n = 1, s = 0, α = 3/4`: LHS `9/64`, RHS `3/16` (ratio 0.75), or the Cantelli-tight `n = 1, s = 0, α = 19/20`.
- Deterministic `M`, point-mass `P_H, μ`: no instance of a mixing mediator or of `L > 1`. Add a second instance with
  a noisy `M` (e.g. 2x3) so the `∑_x μ x ∑_z` structure of `flagRate` and the sums in `push` are really exercised.
- Missing witnesses: `b = 0`, `r = 0`, `κ` soft, `n_s ≥ n_h`.

### F8. MINOR: definitions and hypotheses
- `haltP`, fidelity: **confirmed**. Same branches and budget rule as `cat`. Checked semantically: with `caughtP`
  (FLAG & audit & bad → `r`) and `cleanP` (N rounds, no terminal event), `cat + haltP + caughtP + cleanP = 1` on 300
  random exact instances with history-dependent generators, `r ∈ {0,1/3,1/2,1}`, `b ∈ 0..3`. So `haltP` scores the
  same tree, the halt event is correctly the third branch, and `r` is correctly irrelevant to it (a caught or an
  executed attack ends the protocol; neither is a halt).
- `α₀ = E_{push M P_H} φ₀`, `f₀ = E_μ E_M(1−φ₀)`: right rates for the survival and halt identities (a/b); they are
  the symmetric-error `ε` of LASR App. B.3 split into two numbers (LASR assumes false-negative = false-positive rate).
- `honestUse` hypotheses in (a)/(b): `IsRule φ₀` is *not needed* (identities are polynomial; verified with `φ` values
  in `[-1,2]`); `IsDist μ` is needed for `∑ = 1` only. Nonnegativity of `P_H` is needed only for `α₀ ∈ [0,1]`.
- Statement necessity: `μ` off Bad is necessary for (a) (instance: `μ` half on a bad point, `b = 0, N = 2`:
  `haltP = 5/8`, `1 − binCDF = 3/4`). The hypothesis `s ≤ nα` is necessary for (d) (`n = 4, s = 4, α = 1/2`: LHS 4 > RHS 1).
- Typing: `(fun _ _ => PH)` elaborates to `Unit → Hist X Z → X → ℝ`; parse of `a = b ∧ c ≤ d` and the `∧` chain in (e) is
  as intended.

## 2. Truth of the conjuncts (edge cases)

| conjunct | verdict | evidence |
|---|---|---|
| (a) `haltP = 1 − binCDF N b f₀` | TRUE | 472 exact instances, `N ∈ 0..4`, `b ∈ 0..4` (`N = 0`, `b = 0`, `b ≥ N` all covered), `μ` with zeros, `φ` even outside `[0,1]`. Identity is algebraic: `1−haltP = survH f₀ (hardKill b) N 0`. |
| (b) product identities | TRUE for arbitrary real `κ`, `n_h = 0`, `n_s ≥ n_h` | 282 exact instances with `κ` in `[-1/2, 3/2]`; `surv = survH α₀` and `surv (hardKill ns) = binCDF` both checked. |
| (c) identity | TRUE | 800 + 600 instances; `r ∈ {0,1/3,1/2,3/4,1}`, `b ∈ 0..3`, `N ∈ 1..3`, `α₀ ∈ {0,…,1}`. Needs `PH` on Bad. |
| (c) inequality | **FALSE for `κ ∉ [0,1]`** (F1); true for `κ ∈ [0,1]` | 0 violations for `κ ∈ [0,1]`. |
| (d) Chebyshev | TRUE | 0 / 10,261 grid points (`n ≤ 30`, `α ∈ {i/40}`, includes `n = 0`, `α ∈ {0,1}`, `s = nα`); `s ≤ nα` necessary. Max ratio LHS/RHS 0.975. |
| (e) | TRUE (consequence of T3, (b), (c) at `hardKill`) | 300 instances with random `ρ`, history-dependent `π`, `ns ≥ nh` allowed, `r ∈ {0,1/2,2/3,1}`, minimal `L`: `floor ≤ mimic ≤ UB` and `random pair ≤ UB` always. |

Edge cases you asked for, all checked:
`N = 0` (haltP 0, cat 0; (c) excludes it via `1 ≤ N`), `b = 0` (halts at first flag; floor `S α₀`; UB's `1−r` loose),
`b ≥ N` (usefulness test-survival only), `n_h = 0` (`S = 1`; floor `α₀`; UB ≥ 1 vacuous), `n_s ≥ n_h` (`binCDF = 1`),
`α₀ = 0` (floor 0; (c) risk `[b>0](1−r)`), `α₀ = 1` (`S = [ns ≥ nh]`; consistent), `r ∈ {0,1}`, `κ` outside `[0,1]` (F1),
`P_H` not on Bad (identity false, F2), `μ` with Bad mass (identity false, F8), `s > nα` in (d) (false).

## 3. Witness recomputation (exact, via the recursions in `lib.py`)

| claim | recomputed | match |
|---|---|---|
| `missRate wM wPH wφ` | 1/10 | yes |
| `flagRate wM wμ wφ` | 1/10 | yes |
| `haltP … 1 2 0 []` (b=1, N=2) | 1/100 | yes |
| `honestUse … (hardKill 0) 2 1 2` | 8019/10000 | yes (= 81/100 · 99/100) |
| `protocolCat`, r = 1, b = 1, N = 2, n_h = 2 | 81/1000 | yes |
| same, r = 1/2 | 891/2000 | yes (= 81/100 · 11/20) |
| `(1−1) + 1·(1·(0+1)/(2+1))` | 1/3 | yes; 81/1000 ≤ 1/3 |
| `(10·(1/2) − 1)² · binCDF 10 1 (1/2)` | 11/64 | yes; ≤ 5/2 (weak, F7) |

All eight numbers are right. The hypotheses listed in `Witness` are all satisfied by the instance; the witness is
non-vacuous but symmetric and deterministic (F7).

## 4. Fidelity of the draft to the protocol (brief item 1)

- `haltP` vs `cat`: same branch structure (PASS/bad, PASS/benign, FLAG/audit/bad, FLAG/audit/benign, FLAG/no audit).
  Halt scored 1 only on the unaffordable flag; caught/executed attacks absorb with 0; `r` absent. Partition check passes
  (F8).
- Honest monitor = any rule `φ₀`: the right abstraction for a stateless monitor with fresh coins; its two rates are the
  right sufficient statistics for the test and the stream. But it is *unconstrained*, which is F3.
- Benign law `μ` history-independent: faithful to the recursion, optimistic for real streams (F5).
- Product form: faithful mirror of `protocolCat`'s defining structure (F5).
- Not modelled (state it): audit specificity < 1; partial-credit usefulness; false-positive monitoring tests on real
  traffic (Greenblatt App. G binomial test with p = 0.03 and temporary swap); LASR counts only *dishonest* misses
  toward retraining slack (their `n_s` is adjusted by `1−ε`; here every miss counts, which is why honest `α₀` forces
  slack).

## 5. Numbers: the frontier table recomputed

Independent recomputation (`table.py`; exact `Fraction` cross-check at two points agrees to 1e-13):

| n_h | α₀ | k | n_s | risk_glob | s_c | risk_cls | mimic `surv·α₀` | `(s_c+1)/(m+1)` | `min(½, kα₀/4)` |
|---|---|---|---|---|---|---|---|---|---|
| 30 | .01 | 4 | 1 | 0.115 | 1 | 0.115 | 0.0096 | 0.250 | 0.010 |
| 30 | .05 | 4 | 3 | 0.284 | 2 | 0.194 | 0.0470 | 0.375 | 0.050 |
| 100 | .01 | 4 | 2 | 0.055 | 1 | 0.033 | 0.0092 | 0.077 | 0.010 |
| 100 | .01 | 8 | 2 | 0.113 | 1 | 0.068 | 0.0092 | 0.154 | 0.020 |
| 100 | .05 | 8 | 8 | 0.476 | 3 | 0.163 | 0.0468 | 0.308 | 0.100 |
| 100 | .05 | 16 | 8 | 1.000 | 2 | 0.227 | 0.0468 | 0.429 | 0.200 |
| 1000 | .05 | 8 | 59 | 0.383 | 12 | 0.064 | 0.0457 | 0.103 | 0.100 |
| 1000 | .01 | 8 | 14 | 0.076 | 4 | 0.020 | 0.0092 | 0.040 | 0.020 |
| 10000 | .05 | 8 | 528 | 0.387 | 80 | 0.051 | 0.0452 | 0.065 | 0.100 |

All 9 rows' `n_s`, `s_c`, `risk_glob`, `risk_cls` reproduce the brief's output to 3 digits. The brief's "floor Cheb+UMLOWER"
column also reproduces (e.g. 0.041, 0.148, 0.096). Reading: true. A refinement the brief omits: at
`n_h ≤ 100` the class-aware risk is 3.5x–5x the mimic floor, so "close to the mimicry floor" holds only at
`n_h ≳ 10^3–10^4`, which DESIGN §5 itself calls unrealistic (honeypots cost human points; Greenblatt uses 30, LASR ≤ 100).

Slack-direction check: needed slack for ε = 0.1 at `n = 1000, α = 0.05`: Chebyshev 42.7, Cantelli 47.7, exact 59.

## 6. Is the mimicry floor meaningful? And the best small frontier statement

**Verdict on (c)/(e)**: meaningful in what it says (safety of a UM system cannot beat the honest monitor's own miss
rate times test survival), non-degenerate (checked), but:
1. it is the diagonal of the ROC (power ≥ size), i.e. the weakest possible lower bound on the game value
   `sup_{φ,x} S(E_qφ)(1−r+r E_{Mx}φ)`;
2. the generator "fresh honeypot draws" and `P_H ⊂ Bad` are unnecessary (F2);
3. at realistic budgets it is 3–10x below the attained risk of the designs the stack advocates (section 5);
4. it is folklore: LASR App. B.3 ("safety ... is still bounded by UM's honest abilities, just like in trusted
   monitoring") and App. B.4 (honest error rate ε, `n_s` adjusted by `1−ε`). The Lean value is the exact statement in
   the free-submission model, not the idea.

**Is there a strictly better frontier at similar cost?** Candidates from the brief:

- **(i) Global-slack corollary `risk ≥ ~kα₀/4` (UMLOWERF1 + (d))**: true and informative (it is the only candidate that
  captures the factor-`k` cost of a *global* counter, matching the table's 0.38 vs 0.05). Valid only for a *global*
  hard counter: usefulness forces tolerated `n_s ≳ nα₀`; a class-aware rule tolerates only `s_c` total misses in the
  sense of UMLOWER's `TestSetup`, so honest usefulness does *not* force a large tolerated `n_s` there. Needs UMLOWER as
  a fourth dependency; arithmetic only (min over `t`). Recommend: separate small campaign or write-up arithmetic;
  use the Cantelli form of (d). It is 3x–10x loose against exact attained risk.
- **(ii) Class-aware upper bound → α₀ (UMSTRAT + upper tail)**: true asymptotically (`α₀ + O(k√(α₀/(εn)))` by Chebyshev),
  but as a closed form it loses a factor 1.6 at `n = 10^4` (0.105 vs the exact counting 0.0647). Freeze only the
  honest-side identity (b') and the upper-tail lemma (d'); do the numbers by exact binomial arithmetic.
- **(iii) Usefulness to bound the adversarial gain over always-flag**: no upper bound can use usefulness (always-flag
  satisfies all of them), so the formal handle is a *lower* bound or an exact corner. Exact corner (free from (b)/(c'),
  `φ₀ = 0`): always-flag has `α₀ = 0`, `f₀ = 1`, so **risk = [0<b](1−r)** and **usefulness = binCDF N b 1 = [N ≤ b]**.
  So "always-flag satisfies every bound" can be made a one-line Lean corollary showing it sits at
  `(risk, use) = ([0<b](1−r), [N ≤ b])`, and that UMPROT's UB measures exactly the gain `r·L·(n_s+1)/(n_h+1)` over
  that baseline (b ≥ 1).

**The frontier statement I would freeze (small, honest, nearly free)**:
- (P) **Product inequality**: for `φ₀`, `κ ∈ [0,1]` (or `hardKill`), any `b, N, r`:
  `α₀ · honestUse ≤ protocolCat(view-blind pair at h = α₀) ≤ UMPROT bound (under L-domination)`.
  So usefulness `u` forces risk `≥ α₀ u`; at `L = 1` this is tight up to `surv` (F2.4), and at `L > 1` the gap is at
  most `L`.
- (f) **Honest ROC**: `α₀ + f₀ ≥ 1 − hs 0 (M·μ)(M·P_H)` and the `η`-form. This is the only trusted-only coupling.
- Together they give a chain `risk ≥ u·(1 − f₀ − TV)^+` in terms of trusted components and the false-flag rate.

## 7. Novelty / prior art (arXiv ids verified by fetch on 2026-10-07)

- Greenblatt, Shlegeris, Sachan, Roger, *AI Control: Improving Safety Despite Intentional Subversion*,
  arXiv:2312.06942 (Dec 2023): safety/usefulness frontier (Fig. 2, Table 7), usefulness = rescaled correctness;
  upfront evaluation of the untrusted monitor on 30 synthetic inputs; App. G: binomial-CDF test for excess false
  positives (p = 0.03) with temporary swap to T. The false-halt formula `P(Bin(N,f₀) > b)` and the false-shutdown formula
  `1 − binCDF` are the same tests, classical.
- Gardner-Challis, Bostock, Kozhevnikov, Sinclaire, Velja, Abate, Griffin, *When can we trust untrusted monitoring?
  A safety case sketch across collusion strategies*, arXiv:2602.20628 (Feb 2026; revised Sep 2026): honest error ε (App.
  B.3, symmetric), `n_s` adjusted by `1−ε` (App. B.5), "higher shutdown threshold ... less likely to shut down an
  honest model but also less likely to shut down a scheming model" = the safety/usefulness tension of (d); safety is
  "bounded by UM's honest abilities". Check against the revised version (the extract I read pre-dates the Sep 2026
  revision).
- Bhatt et al., *Ctrl-Z: Controlling AI Agents via Resampling*, arXiv:2504.10374 (Apr 2025): safety/usefulness Pareto
  frontier, usefulness as proportion of tasks.
- Griffin, Thomson, Shlegeris, Abate, *Games for AI Control*, arXiv:2409.07985: the game-theoretic safety/usefulness
  model (not checked in depth for trivial-protocol corners).
- Pure mathematics, all classical: binomial CDF/Beta duality (`∫₀¹ binCDF(n,s,h) dh = (s+1)/(n+1)`, behind T3c), Chebyshev
  (1867), Cantelli (1928; one-sided), binomial median (Kaas–Buhrman 1980), Neyman–Pearson / hockey-stick ROC (T2).
- Calibrated label: (a), (b), (d), (d'), (f), always-flag corner: **classical** (infrastructure). (c')/(P): **trivial
  corollary of frozen T3*** (honest label), with the modest observation that the floor is attained by a view-blind
  pair. No novel mathematics here; the value is closing the "always-flag" loophole in Lean and having exact formulas on
  both sides of the same recursion.

## 8. Lean encoding and effort (brief item 7)

| item | effort | notes |
|---|---|---|
| (a) | small–medium | Prove `1 − haltP … n u h = survH f (hardKill b) n u` for **all** `u` by induction on `n` (the `[u<b]` coefficient is exactly `1 − hardKill b u`, so no side condition); `f := ∑ x, μ x * ∑ z, M x z * (1 − φ z)`, `p + f = 1` from `IsKernel`+`IsDist μ`; `μ`-support kills the `Bad x` branches under the sum. Then rewrite with frozen UMSURV T3b-hard (only `j = 0` is exposed in the frozen `Claim`; use the internal general-`j` lemma if the `.lean` file has one, else a 10-line induction). |
| (b) | small | `∑ push = 1`, frozen T3b + T3b-hard, and (a). |
| (c)/(c') | small–medium | one-step unfold of `cat (N+1) 0 []`; inner `cat n …` terms are multiplied by `0`/discarded because `Bad x`; algebra with `∑_z M x z = 1`. (c') (fixed `x`, constant rule) is *easier* than (c) (no `PH x ≠ 0 → Bad x` juggling under sums). `b ≥ 1` is frozen T3* at `φ = const`. |
| (P) | small | `0 ≤ binCDF N b f₀ ≤ 1` from frozen "survival is a probability" at `hardKill`; `0 ≤ α₀ ≤ 1`; one `nlinarith`/`mul_le_mul`. |
| (d) Chebyshev / Cantelli | medium (80–150 lines) | the real work: second moment of the binomial. Prove `∑ pmf = 1`, `∑ j·pmf = nα`, `∑ j²·pmf = nα(1−α)+n²α²` (induction on `n` with the Pascal recurrence, or `Nat.choose` `j·C(n,j) = n·C(n−1,j−1)`), then `∑_{j≤s} pmf·(nα−j+u)² ≥ F·(nα−s+u)²` and optimise `u` (Cantelli) or `u = 0` (Chebyshev). (d') identical on the upper tail. If time-boxed, freeze Chebyshev (d) only. |
| (f) | small | frozen T1/T2 instantiated at `P = push M μ`, `Q = push M PH`, plus `IsDist (push M μ)`. |
| (b') | small | `Finset.prod` of frozen T3b per class. |
| Witness | small–medium | `simp [haltP, cat, surv, Fintype.sum_bool]` over `Bool`; the Chebyshev numbers need `binCDF` unfolded with `Finset.sum_range_succ`. |

Statement changes that make proofs easier *without* losing content: (1) state (c) with a fixed bad `x` and a constant
rule (no support hypothesis, no `Σ_x PH x` juggling); (2) drop the duplicated T3 and (b) copies from (e); (3) give
(a) in the form `1 − haltP = survH f (hardKill b) N 0` (then `binCDF` follows from frozen T3b-hard); (4) drop `IsRule φ₀`
from (a), (b) (not needed).

## 9. Final list of conjuncts to freeze, with Lean text

Keep `haltP`, `honestUse`, `missRate`, `flagRate` as drafted (rename `honestUse` to `fullRunProb` or add `expCompleted`
in the docstring; see F5).

**(a)** false halt (as drafted).
```lean
(∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ₀ : Z → ℝ) (μ : X → ℝ) (b N : ℕ),
    IsKernel M → IsDist μ → (∀ x, μ x ≠ 0 → ¬ Bad x) →
    haltP Bad M φ₀ (fun _ => μ) b N 0 [] = 1 - binCDF N b (flagRate M μ φ₀))
```

**(b)** honest usefulness, any schedule and hard slack (as drafted; drop `IsDist PH`'s nonneg use, keep as is).

**(b')** honest usefulness of the class-aware design (new; uses `PL_UMSTRATF1.stratSurv`).
```lean
(∀ (X Z C : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (K : C → Z → ℝ) (c : X → C) (Es : Finset C) (m sc b N : ℕ) (φ₀ : Z → ℝ) (μ : X → ℝ),
    IsKernel K → IsDist μ → (∀ x, μ x ≠ 0 → ¬ Bad x) →
    PL_UMSTRATF1.stratSurv K Es φ₀ m sc *
        (1 - haltP Bad (fun x => K (c x)) φ₀ (fun _ => μ) b N 0 [])
      = (∏ e ∈ Es, binCDF m sc (∑ z, K e z * φ₀ z)) *
          binCDF N b (flagRate (fun x => K (c x)) μ φ₀))
```

**(c')** view-blind floor (replaces (c); exact value, `b = 0` included, no `κ`, no `P_H ⊂ Bad`).
```lean
(∀ (X Z : Type) [Fintype X] [Fintype Z] [DecidableEq X] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r h : ℝ) (b N : ℕ) (x : X),
    IsKernel M → IsDist PH → Bad x → 1 ≤ N →
    protocolCat Bad M PH κ nh r b N (fun _ : Unit => 1) (fun _ => fun _ : Z => h)
        (fun _ _ x' => if x' = x then 1 else 0)
      = survH h κ nh 0 * (h + (if 0 < b then (1 - r) * (1 - h) else 0)))
```

**(P)** product-form frontier (the Pareto line `risk ≥ α₀ · usefulness`), hard slack, with the UMPROT upper end.
```lean
(∀ (X Z : Type) [Fintype X] [Fintype Z] [DecidableEq X] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (PH : X → ℝ) (nh ns b N : ℕ) (r L : ℝ) (φ₀ : Z → ℝ) (μ : X → ℝ) (x : X),
    IsKernel M → IsDist PH → IsRule φ₀ → IsDist μ → (∀ y, μ y ≠ 0 → ¬ Bad y) →
    Bad x → 1 ≤ N → 0 ≤ r → r ≤ 1 → 0 ≤ L → (∀ y, Bad y → ∀ z, M y z ≤ L * push M PH z) →
    missRate M PH φ₀ * honestUse Bad M PH (hardKill ns) nh b N φ₀ (fun _ => μ) ≤
      protocolCat Bad M PH (hardKill ns) nh r b N (fun _ : Unit => 1)
        (fun _ => fun _ : Z => missRate M PH φ₀) (fun _ _ x' => if x' = x then 1 else 0) ∧
    protocolCat Bad M PH (hardKill ns) nh r b N (fun _ : Unit => 1)
        (fun _ => fun _ : Z => missRate M PH φ₀) (fun _ _ x' => if x' = x then 1 else 0)
      ≤ (1 - r) + r * (L * (((ns : ℝ) + 1) / ((nh : ℝ) + 1))))
```
(second part is frozen T3 instantiated; it makes the sandwich an explicit conclusion rather than three parallel
facts, which is what (e) failed to do).

**(d)** slack cost, Cantelli form (implies the drafted Chebyshev form since `σ² ≥ 0`).
```lean
(∀ (n s : ℕ) (α : ℝ), 0 ≤ α → α ≤ 1 → (s : ℝ) ≤ n * α →
    ((n : ℝ) * α * (1 - α) + ((n : ℝ) * α - s) ^ 2) * binCDF n s α ≤ n * α * (1 - α))
```
Checked: 0 violations on 7,277 grid points (closed hypothesis, `n = 0` and `α ∈ {0,1}` included).

**(d')** upper-tail twin (sufficient slack), needed for any positive "slack ≈ nα + O(σ)" claim.
```lean
(∀ (n s : ℕ) (α : ℝ), 0 ≤ α → α ≤ 1 → (n : ℝ) * α ≤ s + 1 →
    ((n : ℝ) * α * (1 - α) + ((s : ℝ) + 1 - n * α) ^ 2) * (1 - binCDF n s α) ≤ n * α * (1 - α))
```
Checked: 0 violations on 10,409 grid points.

**(f)** honest ROC constraint (the trusted-only coupling).
```lean
(∀ (X Z : Type) [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH μ : X → ℝ) (φ₀ : Z → ℝ) (η : ℝ),
    IsKernel M → IsDist PH → IsDist μ → IsRule φ₀ →
    1 - flagRate M μ φ₀ ≤ Real.exp η * missRate M PH φ₀ + hs η (push M μ) (push M PH))
```
(`η = 0` gives `α₀ + f₀ ≥ 1 − hs 0 (M·μ)(M·P_H)`; T4a then gives the weaker `hs 0 μ P_H` form.)

**Remark (not a conjunct, one-line corollaries)**: `(b), (c')` at `φ₀ = 0` give the always-flag corner
`(risk, use) = ([0<b](1−r), [N ≤ b])`; (a) at each horizon gives `E[completed] = ∑_{n=1}^N binCDF n b f₀`.

**Drop**: (e) as a separate conjunct; the old (c) (P_H ⊂ Bad mimic generator); the unconditional `κ` inequality.

**Optional, separate campaign**: global-slack corollary (UMLOWERF1 + (d)): `risk ≥ min(½, k(n_s+1)/(4n))` with
`n_s ≥ nα₀ − σ√(ε/(1−ε))` for a usefulness-calibrated global hard counter; arithmetic only.

## 10. Docstring overclaims to fix

1. "This needs no collusion, no seed and no capability." Delete "no capability" (the floor is `α₀`-valued, `α₀` is a
   capability measurement). Say: "floor is conditional on the measured honest honeypot-miss rate".
2. "So no choice of (n_h, n_s) certifies risk below (honest test survival) × α₀." Replace by: "usefulness ≥ u forces
   worst-case risk ≥ α₀·u" (P).
3. "Pareto statement/frontier": call (e) a sandwich; it is tight only at `L = 1` or `n_h ≳ 10^3`.
4. "capability-free": the usefulness half is conditional on `(α₀, f₀, μ)`, i.e. on honest-model behaviour; the safety
   half is the adversary-quantified bound. Mixing them in one `Claim` without this label contradicts the programme's
   own wording.
5. "It is a product because the honest monitor has no seed and the test and deployment calls are fresh (A1)": it is a
   product by the structure of the recursion (A1 is the unproved bridge to the operational protocol).
6. Usefulness definition: rename (`fullRunProb`) and note the difference from the literature (fraction of tasks);
   iid optimism; `b < N` assumption.
7. "(a monitor that FLAGs everything survives every test) so every bound is satisfied by a useless protocol": true only
   for `b < N` (at `b ≥ N` always-flag is fully "useful" with risk `1−r`). State the corner exactly.
8. The `1−r` term: at `b = 0` the UMPROT UB overstates by `1−r`; the exact mimic/view-blind value contains
   `(1−r)(1−α₀)` for `b > 0`. Do not drop either end of the corridor.

## 11. What I could not check

- No Lean was run; statement parse/typing checked by reading, proof effort estimated by analogy with the frozen files.
- The Gardner-Challis text I used for prior-art phrasing is the pre-revision extract in `<scratch>/lasr.txt`;
  the arXiv abstract page reports a September 2026 revision. Re-check the App. B.3/B.5 wording against the current version
  before citing line numbers.
- Griffin et al. 2409.07985: id and title verified, content not read in depth.
