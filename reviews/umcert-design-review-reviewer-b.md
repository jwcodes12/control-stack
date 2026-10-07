# UMCERT design review (hostile), Reviewer B, 2026-10-07

Subject: `PL_UMCERTF1` draft v0 (brief: `reviews/umcert-design-review-prompt.md`).
Scratch checks: `<scratch>/` (exact `Fraction` arithmetic mirroring Lean: `choose n j = 0` for `j > n`, `0^0 = 1`,
truncated Nat subtraction, `1/0 = 0`). No Lean/lake was run. All Lean text below is UNCOMPILED.

## 0. Verdict

**MINOR (accept after edits).** I could not falsify any of the nine conjuncts, including at every edge case in the brief.
Every hypothesis that is present is either needed or harmless, and every hypothesis that is absent is sufficiently implied
(table in section 2). The mathematics is classical packaging (first-bad-decides, a monotone grid bound, one induction for
`G0`). The problems are (a) three overclaims in the docstring, (b) the exactness story stops at the degenerate L = 1 although
the machinery gives exactness at realistic L for free, (c) no end-to-end statement composes `G0 + G + C` / `S1`, and (d) the
Witness is weaker than it looks. Four MAJOR items (I1 to I4) must land before freezing; they are additions and rewordings, not
repairs of false statements.

No FATAL issue. MAJOR: I1, I2, I3, I4 (section 1).

## 1. Issues, severity-tagged

### I1 (MAJOR, overclaim) The docstring claims more exactness than the Claim proves

Exact phrases:
- header: "and shows the certificate is EXACT";
- (S2) tail: "So the stratified design's exact worst case is ..., independent of the kernel K and of the number of classes";
- (X) title "Exactness at L = 1".

What is true, verified in Lean-semantics arithmetic:
- (R) is exact, as a reduction. (C) with a general envelope is an UPPER bound only. It is exact when the envelope is the ROC
  boundary of the worst mediator: (X) at L = 1, (S2) under decoding, and (Xp) below. It is NOT exact for a hockey-stick
  envelope `e^η t + δ` of a given mediator (the line touches the ROC curve at one point).
- "independent of K": true only among exactly-decodable `K` (`∀ e z, K e z ≠ 0 → g z = e`). Negative control: `K 0 = K 1`
  (not decodable), `Es = {0, 1}`, bad class 0, `m = 12, s_c = 1, r = 1, b = 1`. The family "PASS `true` at rate t" gives
  max_t binCDF(12,1,t)^2 t = 0.04517, and the per-seed bound (T3a times the product over both identical classes) gives exactly that max as the sup over all pairs. So at `U = 0.05` the
  LHS of (S2) is true and the RHS (sup 0.0683) is false: the iff FAILS without decoding. The hypothesis is load-bearing.
- "independent of the number of classes": `|Es|` does not enter the bound, but it enters the cost (m·|Es| honeypots).

Fix (docstring text):
> (R) is an exact reduction. (C) is an upper bound valid for every mediator that satisfies the envelope hypothesis; it is
> tight for the worst mediator in the class (X, Xp, S2), not for a given mediator. (S2): under exact class decoding the
> stratified worst case equals max_t binCDF(m,s_c,t)·capB(r,b,t) for every decodable K and every tested class set; |Es| enters
> only through the honeypot cost m·|Es|.

### I2 (MAJOR, value and faithfulness) (X) is a degenerate regime; exactness at realistic L is missing

`(∀ x, Bad x → ∀ z, M x z ≤ push M PH z)` with `M x`, `push M PH` both laws FORCES `M x = push M PH` for every bad x (equal
mass 1 pointwise-dominated). So (X) says: when honeypots are distributionally identical to the bad views, the sup equals
`max_t S(t) capB(t)`. That is the best conceivable mediator. It is a correct no-go (with (F): NO design certifies below the
AOQL), but every deployed mediator has L > 1 (UMHS T4c': L ≥ Σ_z max_x M x z). The DESIGN §5 "global" column is exactly the
exact sup at `L = k = 1/p`, and the stack already has the pieces: (R) at `ψ = t·1_{class}` and the UMNOGO conjunct (b).

Numerical confirmation (`tables.py`): max_t binCDF(100,n_s,t)·min(1, k t) reproduces DESIGN §5 "global" values to 3 digits:
(0,8) 0.0293 [0.029], (2,4) 0.0548 [0.055], (2,8) 0.1095 [0.110], (8,8) 0.4148 [0.415], (8,16) 0.8268 [0.827]. The counting
bound `L(n_s+1)/(n_h+1)` is 0.079, 0.119, 0.238, 0.713, **1.426 (vacuous)** for those rows.

Fix: add (Xp), exactness for content-preserving mediators with minimum bad-class coverage p (proof: (C) with env t = t/p via
the UMHS domination lemma and (E); (→) by (R) with ψ = u on the decoded class of x0, which has honeypot pass rate u·p and bad
pass rate u, then antitone `G0` for t > p). Verified: 420 random instances, 0 mismatches; 0 envelope violations.
```lean
  -- (Xp) exactness for content-preserving mediators, minimum bad-class honeypot mass p
  (∀ (X Z C : Type) [Fintype X] [Fintype Z] [DecidableEq C] (Bad : X → Prop) [DecidablePred Bad]
      (K : C → Z → ℝ) (c : X → C) (g : Z → C) (PH : X → ℝ) (p : ℝ)
      (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ),
      IsKernel K → (∀ e z, K e z ≠ 0 → g z = e) → IsDist PH → 0 < p →
      (∀ x, Bad x → p ≤ contentLaw c PH (c x)) → (∃ x, Bad x ∧ contentLaw c PH (c x) = p) →
      (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → 1 ≤ N →
      ((∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
          IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
          protocolCat Bad (fun x => K (c x)) PH κ nh r b N ρ φ π ≤ U) ↔
       (∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t κ nh 0 * capB r b (min 1 ((1 / p) * t)) ≤ U)))
```
Optional (X_L), exactness over the CLASS of L-dominated mediators (swap the sups): for `L ≥ 1`, `t ∈ [0,1]` the two-point mediator
`X = Z = Bool`, honeypot `PH = δ_hp`, `M hp = (1/L on true, 1 − 1/L on false)`, `M bad = δ_true` has ROC `a = min(1, L h)`.
So `sup over L-dominated (M, PH) of the worst case = max_t S(t) capB(min 1 (L t))`. Not required, but it states "this is the best
bound as a function of L alone", which is what a lab wants.

### I3 (MAJOR, packaging) No end-to-end certificate statement; (E) are restatements; (G) is not wired to (C)

The docstring promises "this turns a sup over t into finitely many rational inequalities", but no conjunct says
`GridCert … → protocolCat ≤ U`. To apply (G) to (C) one must prove, ad hoc each time, that `F t = capB r b (min 1 (env t))` is
monotone and nonnegative (needs `0 ≤ r ≤ 1`, env monotone and ≥ 0 on [0,1]) and that `S t = survH t κ nh 0` is antitone (G0).
The Witness does this composition by hand for two protocols. (E) are one-line restatements of UMHS T2 and a sum inequality.

Fix: add (CG) and (SG), keep (E).
```lean
  -- (CG) end-to-end: grid certificate, halting protocol, any monotone nonnegative envelope
  (∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (env : ℝ → ℝ) (U : ℝ)
      (ts : List ℝ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel M → IsDist PH → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
      (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 →
      (∀ x, Bad x → ∀ ψ : Z → ℝ, IsRule ψ → E (M x) ψ ≤ env (E (push M PH) ψ)) →
      (∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → env s ≤ env t) → (∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ env t) →
      GridCert (fun t => survH t κ nh 0) (fun t => capB r b (min 1 (env t))) U ts →
      protocolCat Bad M PH κ nh r b N ρ φ π ≤ U) ∧
  -- (SG) end-to-end: grid certificate, stratified design
  (∀ (X Z C Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop) [DecidablePred Bad]
      (K : C → Z → ℝ) (c : X → C) (Es : Finset C) (m sc b N : ℕ) (r U : ℝ) (ts : List ℝ)
      (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel K → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → 0 ≤ r → r ≤ 1 →
      (∀ x, Bad x → c x ∈ Es) →
      GridCert (fun t => binCDF m sc t) (fun t => capB r b t) U ts →
      stratProtocolCat Bad K c Es m sc r b N ρ φ π ≤ U)
```
In (CG), `0 ≤ U` is derivable (GridCert has at least one cell and both factors are ≥ 0), so the (C) hypothesis is discharged.
(CG) at `env t = L * t` (`0 ≤ L`) and `env t = Real.exp η * t + δ` (`0 ≤ δ`) are the user-facing corollaries of UMPROT T3's two
trusted-side hypotheses; do not add them as separate conjuncts, just use them in the Witness.

### I4 (MAJOR, rationale unformalised) The claim "replaces the Markov step" is not a Lean statement

Nothing in the Claim says the new certificate is never worse than UMPROT T3 / UMSTRAT (the CID's raison d'être). Add the
refinement (D): the counting bound satisfies the certificate hypothesis for every `t`, hard and soft slack, every b, so the best
certificate is ≤ the counting bound. Verified (`t_DG.py`): 0 violations in 123,000 hard-slack and 82,000 soft-slack grid
checks (r, L, b, n, s varied).
```lean
  -- (D) refinement: the counting bounds of UMPROT T3 satisfy the certificate hypothesis
  (∀ (n s b : ℕ) (r L t : ℝ), 0 ≤ r → r ≤ 1 → 0 ≤ L → 0 ≤ t → t ≤ 1 →
      survH t (hardKill s) n 0 * capB r b (min 1 (L * t)) ≤
        (1 - r) + r * (L * (((s : ℝ) + 1) / ((n : ℝ) + 1)))) ∧
  (∀ (n ns b : ℕ) (r L t : ℝ), 0 ≤ r → r ≤ 1 → 0 ≤ L → 1 ≤ ns → 0 ≤ t → t ≤ 1 →
      survH t (softKill ns) n 0 * capB r b (min 1 (L * t)) ≤
        (1 - r) + r * (L * ((ns : ℝ) / ((n : ℝ) + 1))))
```
Proof sketch (hard): `S ≤ 1` (UMSURV), `t·S(t) ≤ (s+1)/(n+1)` (UMSURV T3c via T3b-hard). For `b ≥ 1`:
`S(1−r+r·a) ≤ (1−r) + r·L·t·S`. For `b = 0`: with `B = L(s+1)/(n+1)`, if `B ≥ 1` then RHS `≥ 1 ≥ S·a`, else `S·a ≤ L t S ≤ B ≤ (1−r)+rB`.
Soft: UMSURV conjunct 3 gives `(1 − t/ns)^n`, then T3c'.

### I5 (MINOR) (S2) carries `1 ≤ b` for no mathematical reason; inconsistent with capB and with (R), (F), (X)

(S2)(→) is true at `b = 0` too (300 random decodable instances, b ∈ {0,1,2}: pair value equals binCDF·capB exactly, 0
failures). `1 ≤ b` is there only to reuse UMSTRAT's second conjunct. Drop it and prove the `b = 0` pair value with the same
helper as (R) (`cat` with fixed bad `x`, `N ≥ 1`, depends only on `M = K ∘ c`).
Fix: delete `1 ≤ b →` from (S2); the docstring "b ≥ 1" becomes "any b".

### I6 (MINOR) (F) and (X)(→) are (R)(→) restated; (F) re-proves UMUSE (c')

UMUSEF1 (c') already states `viewBlindRisk = survH h κ nh 0 * (h + [0<b](1−r)(1−h))` with `b = 0` included and no PH-support
hypothesis. `h + (1−r)(1−h) = 1 − r + r·h`, so (c') = `capB`. (F) = (c') plus instantiating the universal certificate at
ψ ≡ t. If UMCERT may import UMUSEF1, use (c'); otherwise prove one helper `oneShot_value` (below) and derive (R)(→), (F), (X)(→),
(S2)(→) from it. I recommend keeping (F) and (X) as named conjuncts (they are the AOQL floor and its tightness) but marking
them in the docstring as corollaries. (F) is true for all real `r` and all real `κ` (no range hypothesis needed), nonempty `Bad`
and `N ≥ 1` needed (empty Bad: LHS ⇔ 0 ≤ U).

### I7 (MINOR) `0 ≤ U` hypotheses: needed exactly where (and only where) stated

See table in section 2. (R), (C): needed only to dispatch empty `Bad` (counterexample for (C) below). (X), (F), (S1), (S2): absent
and sufficient, because the certificate side at `t = 0` already forces `U ≥ 0` (`survH 0 κ n j = 1`, `binCDF m s 0 = 1`, and
`capB r b 0 ∈ {1−r, 0} ≥ 0` for `r ≤ 1`). Optional tidy-up: replace `0 ≤ U` in (R) and (C) by `(∃ x, Bad x) ∨ 0 ≤ U`, which is
strictly weaker; low value, keep as is.

### I8 (MINOR, docstring scope)

- "history dependence ... do not help the colluders" is about the GENERATOR's history dependence (the monitor is stateless, A1;
  the generator even sees PASS/FLAG decisions). Say "generator history dependence".
- "waiting does not help" is specific to the HALTING variant. In a protocol where an exhausted budget lets flags pass
  (non-halting), a colluding monitor can FLAG benign items to burn the budget and then attack unmonitored, so waiting helps. Do not
  reuse (R) for UMDEFER-type models without re-deriving.
- "function of the trusted components only": it is a function of `(M, PH, κ, nh, r, b, Bad)`. `r` is a STANDING hypothesis
  (A6), `PH`/`L` is A9, `Bad` is the ground-truth catastrophe predicate. Say "of the modelled parameters (M, PH, κ, n_h, r, b,
  Bad); `N` and the colluders' strategy drop out for N ≥ 1".

### I9 (MINOR) AOQL labelling

The function `p·Pa(p)` with `Pa(p) = P(Bin(n,p) ≤ c)` is the large-lot average outgoing quality of the rectifying single sampling
plan (`AOQ = p·Pa(p)·(N_lot − n)/N_lot`), and its maximum is the AOQL (Dodge 1920s; tables Dodge and Romig, BSTJ Jan 1941;
Dodge–Romig tables compile `AOQL ≈ f(c)/n`, f(0) = 0.368, f(1) ≈ 0.84; the n→∞ limit of our numbers: max_λ λ(1+λ)e^{−λ} = 0.838).
The coincidence is formal: here `p` is a colluder's per-submission pass rate and the "outgoing quality" is one attack's success
probability. It matches AOQL exactly only for `r = 1` (b ≥ 1) or `b = 0`; for `r < 1`, b ≥ 1 the function is
`(1−r)·Pa + r·AOQ`. The docstring says "AOQL-type"; make that "for r = 1 or b = 0".

### I10 (MINOR) Witness

1. Conjunct 7 (∀ pairs ≤ 3/40) is an instance of the Claim. The Witness is then no longer an independent non-vacuity check (in
   earlier campaigns the Witness was purely computational). Move it to a corollary, or keep it and say "consumes (SG), (CG)".
2. Bracket is loose: `max_t t·binCDF(12,1,t) = 0.0683392329` at `t* = 0.1256048`. The Witness brackets `[0.06834, 0.075]` (10% gap).
   A 36-cell grid certifies `U = 69/1000`, a 23-cell grid certifies `7/100`. Both are within norm_num's comfort zone. Explicit
   grids (verified exactly, `grid.py`):
   - `U = 7/100`, 23 cells: `[0, 7/100, 87/1000, 97/1000, 13/125, 109/1000, 113/1000, 29/250, 119/1000, 61/500, 1/8, 16/125, 131/1000, 67/500, 137/1000, 141/1000, 73/500, 19/125, 4/25, 43/250, 193/1000, 237/1000, 19/50, 1]`
   - `U = 69/1000`, 36 cells: `[0, 69/1000, 861/10000, 477/5000, 507/5000, 1057/10000, 109/1000, 279/2500, 569/5000, 1157/10000, 587/5000, 1189/10000, 1203/10000, 76/625, 307/2500, 31/250, 313/2500, 79/625, 319/2500, 161/1250, 1301/10000, 657/5000, 83/625, 84/625, 681/5000, 691/5000, 281/2000, 1433/10000, 367/2500, 1513/10000, 1573/10000, 83/500, 899/5000, 41/200, 2643/10000, 5167/10000, 1]`
   - lower bound: `6833/100000 ≤ binCDF 12 1 (1/8) * (1/8)` holds (0.06833799); 17/250 = 0.068 is fine but wastes the 3e-4 margin.
3. The only new feature beyond UMPROT T3 at L > 1 (`min 1 (L t)`, the kink) is not exercised: at L = 1 the `min` never binds.
   Add one L > 1 instance and one soft-slack instance (numbers verified):
   - kink instance: `n_h = 100, n_s = 2, L = 8, r = 1, b = 1`: true max 0.1095 at t = 0.0225, counting bound 0.2376; grid for
     `U = 11/100` has 52 cells at denominator 10^5 (denominator 10^4 does not suffice because of the kink at 1/8; include 1/8 in the grid).
   - soft instance: `n_h = 100, n_s = 5, L = 1`: `max_t t(1−t/5)^100 = 0.018303`, counting bound `5/101 = 0.0495` (ratio 0.37 = 1/e);
     grid for `U = 19/1000` has 22 cells at denominator 10^4.
4. `r < 1` and `b = 0` are not instantiated. Use `r = 9/10, b = 1` once and recompute (max shifts), and one `b = 0` instance
   (the grid for `b = 0` is the same as for `r = 1`).
5. If `Nat.choose 100 8`-size terms appear, check that `norm_num`/`simp` evaluates `Nat.choose` (otherwise supply
   `Nat.choose_eq_descFactorial_div_factorial` or the explicit coefficient list).

### I11 (MINOR) (G) hygiene, computable checker, Bernstein

- (G) as stated is true. Edge cases: `ts = [0, 1]` is one cell; `ts` with `head? = some 0` and `getLast? = some 1` has length ≥ 2,
  so a singleton `[x]` (no pair, no cell inequality) cannot occur; duplicates are allowed; `U ≥ 0` follows from `S F ≥ 0` and one cell.
- Proof helper (the induction must carry the head, since the singleton case gives no cell inequality):
```lean
lemma gridOK_bound {S F : ℝ → ℝ} {U : ℝ}
    (hS : ∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → S t ≤ S s)
    (hF : ∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → F s ≤ F t)
    (h0 : ∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ S t ∧ 0 ≤ F t) :
    ∀ (rest : List ℝ) (s t : ℝ), 0 ≤ s → (∀ x ∈ s :: t :: rest, x ≤ 1) →
      GridOK S F U (s :: t :: rest) →
      ∀ u, s ≤ u → u ≤ ((s :: t :: rest).getLast (List.cons_ne_nil _ _)) → S u * F u ≤ U
```
  Cleaner: prove `∀ x ∈ ts, 0 ≤ x ∧ x ≤ 1` from `head? = some 0`, `getLast? = some 1`, and sortedness from `GridOK`; then induct on `rest`.
  Step: `u ≤ t` gives the cell `S u F u ≤ S s · F u ≤ S s · F t`; otherwise use the IH on `t :: rest` (`rest = []` is impossible since `u > t` and last = t).
- Computable checker: for design tables at `n_h = 100` a real-valued `GridOK` unfolded by `norm_num` is feasible but slow
  (hundreds of cells, 300-digit numbers). The scalable route is `Nat` arithmetic over a common denominator `D` with a checker
  `check : ℕ → ℕ → ... → List ℕ → Bool`, a one-time soundness lemma (cast to ℝ), and `by decide +kernel` (kernel GMP, no extra axiom,
  unlike `native_decide`). Do NOT compute `Nat.choose` by its defining recursion in the kernel (cost ~ n^k); use the
  multiplicative formula or `descFactorial / factorial`.
- Bernstein is not needed here. A monotone cell bound has error O(w); near the max the cell count scales as gap^(−1/2): 13 cells for 10%,
  23 for 2.3%, 36 for 1%, 144 for 0.09% (m=12, s_c=1). Bernstein or SOS certificates pay off only for the larger stateful-game project.

### I12 (MINOR) (S1) docstring: "No coverage or domination constant is needed"

The coverage hypothesis IS present: `∀ x, Bad x → c x ∈ Es`. The in-class fidelity assumption (a honeypot of class `e` has view law
exactly `K e`, the same as a bad submission of class `e`) is built into `stratSurv` (its test law is `K e`), i.e. L = 1 per class by
construction. That is trust hypothesis A9 (constructibility), not absence of one. Fix wording: "Because honeypots are generated per
class and the mediator is content-only, in-class domination holds with constant 1 by construction; the remaining trust
hypotheses are coverage (`c x ∈ Es`) and honeypot constructibility (A9)."

### I13 (NIT)

- Rename the envelope `g` to `env` in (C) and (E): `g` is the decoder in (S2) and `witnessK`.
- (S2) assumes decoding for ALL `e : C`; only classes in `Es` matter. Weaker hypothesis `∀ e ∈ Es, ∀ z, K e z ≠ 0 → g z = e` suffices
  mathematically but breaks reuse of UMSTRAT conj 2; leave as is.
- "A 14-point grid certificates" (grammar), and `GridCert` could return the cell count as a documented fact.

## 2. Truth table with edge cases (own exact checks)

| conjunct | verdict | edge cases verified |
|---|---|---|
| (R) | TRUE | One-shot attainment `protocolCat = survH(E_q ψ)·capB(E_{M x} ψ)`: 278 random instances with b ∈ {0..3}, N ∈ 1..4, nh ∈ 0..4, **arbitrary real r and κ** (even outside [0,1]), 0 failures; exact at `b = 0` (a flag halts, value `S·a`). Per-seed `risk ≤ max_x S·capB` on 500 random instances (history-dependent π, κ ∈ {0,1}, empty Bad in 1/7 of them), 0 violations. `N = 0` must be excluded: `protocolCat = 0` while the one-shot value is 1/2. `0 ≤ U` is needed only for empty Bad (LHS ⇔ 0 ≤ U, RHS vacuous). For nonempty Bad and U < 0 both sides are false. |
| (C) | TRUE | `N = 0`, `b = 0`, empty Bad (needs `0 ≤ U`; counterexample: Bad empty, `g ≡ −100`, κ ≡ 0, r = 1, b = 1, U = −1: certificate holds, risk 0 > U). g non-monotone / negative is harmless: with nonempty Bad the hypothesis forces `g t ≥ t` on [0,1] because the constant rule ψ ≡ t realises every `t ∈ [0,1]` (honeypot rate t, bad rate t). 1371 per-seed checks with L, TV and a non-monotone majorant, 0 violations. |
| (E) | TRUE | trivial; no sign condition on `L`; `δ` any real; `IsRule ψ` supplies `ψ ≥ 0`. |
| (G0) | TRUE | 3000 random schedules (κ ∈ {0,1} in 1/5), n ≤ 9, j ≤ 4, 0 violations; hypothesis `κ ∈ [0,1]` is necessary (κ ≡ −1/2 makes `S_1` increasing). Proof below. |
| (G) | TRUE | 300 random monotone/antitone piecewise-linear pairs, grids with duplicates, 36,000 point checks, 0 violations. |
| (F) | TRUE | true for all real r, κ; needs nonempty Bad and `N ≥ 1`; uses ψ ≡ t, and `Σ_z push z = 1`. |
| (X) | TRUE | hypothesis ⇔ `M x = push M PH` (both laws, pointwise ≤ ⇒ equal). `0 ≤ U` not needed: RHS at `t = 0` gives `U ≥ survH 0 · capB 0 ≥ 0`. |
| (S1) | TRUE | 1500 per-seed checks: random non-decodable kernels, `Es` with extra untested classes or empty, N ∈ 0..3, m ∈ 0..5, `s_c` up to 6 (so `s_c ≥ m`), b ∈ 0..2, r ∈ {0,…,1}: 0 violations vs `binCDF(m,s_c,A)·capB(A)`, A = max bad-class pass rate. `U ≥ 0` derivable at `t = 0`. `m = 0` or `s_c ≥ m` ⇒ binCDF ≡ 1 ⇒ certificate needs `U ≥ 1`, consistent. |
| (S2) | TRUE | attainment on 300 decodable instances incl. b = 0, extra classes in `Es`: `strat = binCDF(m,sc,t)·capB(r,b,t)`, 0 failures. Random-pair search (4000 φ per instance, 3 instances) never exceeds `sup_t`. Decoding is necessary (control 0.0452 vs 0.0683). |
| (Xp) (proposed) | TRUE | 420 attainments + 0 envelope violations. |
| (D) (proposed) | TRUE | 0 violations / 205,000 grid checks (hard 123,000, soft 82,000). |

My reading of the brief's items 1 and 2 follows from this table. In particular: (C) is true for `N = 0` and for empty `Bad` (given
`0 ≤ U`); the `0 ≤ U` hypotheses are needed where present and sufficient where absent; the `(Ω : Type)` quantification inside `↔`
creates no trap (universe 0 only needs to cover finite mixtures; any `Fintype Ω` instance gives the same sums; the (→) direction
instantiates `Ω := Unit`, `ρ := 1`, and a fixed-`x` generator; the Prop-valued quantification over `Type` is impredicative-safe).
Only genuine caveat: `Ω` is finite, which loses nothing because the per-seed bound is linear in `ρ`.

## 3. The only non-packaging mathematics: (G0)

Auxiliary lemma `aux`: for `κ ∈ [0,1]`, `0 ≤ h ≤ 1`: `(1 − κ j) · survH h κ n (j+1) ≤ survH h κ n j`.
- `n = 0`: `1 − κ j ≤ 1`.
- step: `(1−κ_j) S_{n+1}(h, j+1) = (1−h)(1−κ_j) S_n(j+1) + h(1−κ_j)(1−κ_{j+1}) S_n(j+2)`; by IH(j) the first piece is `≤ (1−h) S_n(j)`, by IH(j+1) times `1 − κ_j ≥ 0` the second is `≤ h(1−κ_j) S_n(j+1)`; the sum is `S_{n+1}(h, j)`.

Antitone, induction on `n` generalising `j`, with `u(h) = S_n(h,j)`, `v(h) = (1−κ_j) S_n(h,j+1)`, `S_{n+1}(h,j) = (1−h)u + h v` and
`(1−t)u(t) + t v(t) = (1−s)u(t) + s v(t) + (t−s)(v(t) − u(t))`.
Then `(t−s)(v(t)−u(t)) ≤ 0` by `aux` at `t`, and `(1−s)u(t) + s v(t) ≤ (1−s)u(s) + s v(s)` by the two IHs (`0 ≤ s ≤ 1`, `1−κ_j ≥ 0`).
About 25 lines with `nlinarith`/`mul_nonneg`. No calculus, no coupling.

## 4. Provability and helper lemmas (item 8)

All conjuncts are provable. Reuse and helper lemmas:

1. `push_sum : IsKernel M → IsDist PH → ∑ z, push M PH z = 1`.
2. `survE : IsKernel M → IsDist PH → surv (push M PH) φ κ n j = survH (E (push M PH) φ) κ n j` (UMSURV T3b; `E P f` is definitionally `∑ P z * f z`).
3. `E_mem : IsKernel M → IsRule φ → 0 ≤ E (M x) φ ∧ E (M x) φ ≤ 1`.
4. `cat_nonpos_bad : (∀ x, ¬ Bad x) → cat Bad M φ π r b n u h = 0` (induction on `n`).
5. `perSeed : T3a at A := max_x E (M x) φ` (`Finset.exists_max_image` on the filter; nonempty Bad), giving `cat ≤ capB r b A` at `u = 0`.
6. `oneShot_value : IsKernel M → Bad x → 1 ≤ N → protocolCat Bad M PH κ nh r b N (fun _ : Unit => 1) (fun _ => ψ) (fun _ _ x' => if x' = x then 1 else 0) = survH (E (push M PH) ψ) κ nh 0 * capB r b (E (M x) ψ)` for ALL `b`, all real `r`, `κ` (UMPROT T3* covers `b ≥ 1` only; `b = 0` is a short unfold: `Σ_z M x z (ψ z + (1 − ψ z)·0)`). The strat version only needs `cat` with `M := K ∘ c`.
7. `capB_mono`, `capB_nonneg` (`0 ≤ r ≤ 1`, `0 ≤ a ≤ 1`).
8. `prod_le_single : 0 ≤ f e ≤ 1 for e ∈ Es → ∏ e ∈ Es, f e ≤ f e0` (`Finset.mul_prod_erase`, `Finset.prod_le_one`); and `binCDF ∈ [0,1]` from UMSURV's last conjunct + T3b-hard.
9. `survH_zero : survH 0 κ n j = 1` and `binCDF m s 0 = 1` (to derive `0 ≤ U` in (X), (S1), (S2), (CG)).
10. `gridOK_bound` (section 1, I11).

Split/drop recommendations: keep (R) as one iff (the ∀-U form avoids any `sSup` over a Type-quantified family, which is the right design). Do not state an `sSup` version. Keep (E) (cheap). Keep (F) and (X) as corollaries. No conjunct should be dropped for truth reasons.

## 5. Decision relevance (item 6)

What a lab gains beyond UMPROT / UMSTRAT:
1. Certified numbers tighter by a factor 1.7 to 2.7, and non-vacuous where the counting bound exceeds 1.
   Exact ratios `cert / counting` (`tables.py`): stratified L = 1: (7,0) 0.39, (7,1) 0.46, (7,2) 0.52, (12,0) 0.38, (12,1) 0.44,
   (12,3) 0.53, (25,1) 0.43, (6,2) 0.53, (100,0) 0.37, (100,2) 0.46, (100,5) 0.54, (100,8) 0.58. Soft slack `(n_h, n_s) = (100, 5)`: 0.0183 vs 0.0495 (ratio 1/e = 0.37).
   Global L = k rows: 0.0293/0.0792, 0.0548/0.1188, 0.1095/0.2376, 0.4148/0.7129, **0.8268/1.4257**.
2. Fewer honeypots for a fixed target (the honeypot is a human-labelled point, DESIGN §5 stresses their cost). Minimum n_h with `r = 1`,
   cert versus counting: s = 0, U = 0.01: 37 vs 99; s = 1, U = 0.05: 17 vs 39; s = 2, U = 0.10: 14 vs 29; s = 5, U = 0.05: 64 vs 119;
   L = 8, s = 2, U = 0.10: 110 vs 239.
3. A Lean-checked floor. With (F), no honeypot design of this protocol class can certify below `max_t S(t) capB(t)`. Together with (X)/(Xp)
   the DESIGN §5 numbers are two-sided in Lean (upper by (CG), lower by (R)/(S2)), not "exact sups of a family".
4. (R) collapses red-team search in the halting model to `x` (a bad class) and `ψ` (one rule): shared randomness, generator adaptivity
   and the attack round are irrelevant. LASR and Greenblatt-style evaluations optimise `(θ, β)` numerically; here `β = 1` is optimal.
   That is a real conceptual simplification, but it holds only for the halting variant (I8).
5. A tooling milestone for (A): a certificate form with a soundness theorem and a rational checker.

Is it worth a CID? Yes, as infrastructure, if I1 to I4 land. Value is "Lean-checked design calculator and AOQL no-go", not a new
security insight. What would make it more useful (in order): (a) (Xp) so the DESIGN global column is two-sided; (b) a soft-slack instance
(the largest ratio gain, 1/e) and an L > 1 kink instance in the Witness; (c) the n_h = 100 DESIGN rows via a `decide +kernel`
checker rather than `norm_num`; (d) (D), so a downstream user cannot do worse by adopting the certificate; (e) an inverse-design
statement (minimal `m` for a target `U`) is a corollary, not needed now.

## 6. Prior art and novelty (item 7), ids verified this session

- Acceptance sampling AOQL: Dodge and Romig, "Single Sampling and Double Sampling Inspection Tables", Bell System Technical Journal,
  January 1941 (existence confirmed by search; the AOQL concept and tables; book form Wiley 1944/1959). `AOQ(p) = p·Pa(p)·(N−n)/N`,
  AOQL = max over p; `Pa(p) = P(Bin(n,p) ≤ c)` for the single sampling plan. The function in (F)/(X)/(S2) is the large-lot AOQ with
  `n = n_h`, `c = n_s`. Known (classical). Page numbers not checked.
- Games for AI Control, arXiv 2409.07985 (Griffin, Thomson, Shlegeris, Abate): verified title and authors. Proposition 4.1 and the red
  team "memoryless (its actions depend only on the last observation)" confirmed on the HTML page. So GAC checks the Red best response
  within the memoryless class; (R) is a different statement (adaptive generator, shared seed, for a stateless monitor, in a halting model).
- Ctrl-Z, arXiv 2504.10374 (Bhatt et al.): verified title and authors. Appendix E is "Untrusted Monitoring" with E.1 "Simplifying
  Assumptions Made for Untrusted Monitoring" and E.2 "Parameters and Optimization"; the red/blue parameters are numerically optimised, not
  closed form. (Full content of E.1 not re-read.)
- LASR "When can we trust untrusted monitoring? A safety case sketch across collusion strategies", arXiv 2602.20628 (Gardner-Challis et al.):
  verified title and authors. The red team optimises a decision threshold θ on the monitor's collusion ROC curve and the attack probability
  β; the equilibrium is estimated numerically. B.3 "Imperfect Backdoor Detection", B.5 "Modelling Slack Honeypots" (each missed honeypot
  triggers a gradient update with probability 1/n_s, i.e. the soft-slack model), B.6 "Win/Continue/Lose Calculations" (binomial to Poisson).
  This is exactly the setting; UMCERT's cert hypothesis is the Lean-checked analogue of "bound the collusion ROC curve, then optimise
  over the threshold". (C)'s envelope `env` is a ROC bound. Calibrate: UMCERT is not new modelling; its contribution is the exact
  reduction (R) (so β drops out), the monotone-grid soundness theorem, and checkable numbers.
- Greenblatt et al., arXiv 2312.06942 "AI Control: Improving Safety Despite Intentional Subversion" (verified title/authors): the original
  protocol-vs-red-team framing and the upfront-honeypot untrusted monitoring this model abstracts.
- Novelty, calibrated: classical / modest formal infrastructure. (R) is a packaging of T3a + T3* (every nontrivial step was already frozen).
  New content: (G0) (induction), (G) (list induction), (Xp) / (D) if added. No outreach-worthy novelty, consistent with the programme ruling.

## 7. Final list of conjuncts to freeze

Keep, with edits shown:

1. **(R)** as drafted (rename nothing; keep `0 ≤ U`; docstring per I1, I8).
2. **(C)** as drafted, envelope renamed `env`; keep `0 ≤ U`.
3. **(E)** as drafted (two one-liners), `g` renamed `env` in the docstring.
4. **(G0)** as drafted.
5. **(G)** as drafted (statement unchanged; helper `gridOK_bound`).
6. **(CG)**, **(SG)** NEW (I3).
7. **(F)** as drafted (docstring: "view-blind pair; corollary of (R); UMUSE (c')").
8. **(X)** as drafted; docstring: "the hypothesis forces `M x = push M PH` for every bad `x`: perfect honeypots".
9. **(Xp)** NEW (I2).
10. **(S1)** as drafted; docstring per I12.
11. **(S2)** with `1 ≤ b →` deleted (I5); docstring per I1.
12. **(D)** NEW (I4), two conjuncts (hard, soft).
Optional, not required to freeze: (X_L) (class-exactness over L-dominated mediators).

Witness: replace by (i) 36-cell grid for `U = 69/1000` (or 23-cell for 7/100), (ii) lower bound `6833/100000 ≤ ...` at `t = 1/8`,
(iii) soft-slack instance `(n_h, n_s) = (100, 5)`, `U = 19/1000`, (iv) one `L > 1` kink instance, (v) `r = 9/10` or `b = 0` instance.
Mark conjunct 7 (the universal "∀ pairs ≤ 3/40") as a corollary that consumes (SG)/(CG), or drop it. The three-conjunct structure of
earlier Witnesses (computational facts only) is the target.

Proposed replacement docstring paragraph (truthful scope):
> Certificate form of the halting-protocol bound (PL_UMPROTF1) and the stratified bound (PL_UMSTRATF1). (R): in the halting model
> the exact worst case over all colluding pairs (shared seed, stateless monitor, adaptive generator) equals the worst one-shot pair
> `survH(E_{M·PH} ψ)·capB(E_{M x} ψ)`, for every valid κ, every b, every N ≥ 1; it is a function of (M, PH, κ, n_h, r, b, Bad) and is
> specific to the halting variant. (C), (CG): any envelope `env` of the bad views' pass rates over the honeypot pass rate yields a
> bound `U` as soon as `S(t)·capB(min 1 (env t)) ≤ U` for `t ∈ [0,1]` (never worse than UMPROT T3: (D)); a grid of rational cells
> certifies this. Exactness: (F) universal floor (view-blind pair, the AOQL of the single sampling plan at r = 1 or b = 0), (X) at
> perfect honeypots (L = 1, i.e. `M x = push M PH`), (Xp) for content-preserving mediators with coverage `p`, (S2) for the stratified
> design under exact decoding. Not exact for an arbitrary mediator or an arbitrary hockey-stick envelope.

## 8. Scratch checks

| file | check | result |
|---|---|---|
| `lib.py` | Lean-semantics mirror (`choose`, `0^0`, `cat`, `surv`, `survH`, `binCDF`, `capB`); T3b-hard identity | OK |
| `w1.py`, `ctl.py` | Witness grid cell by cell; `t* = 0.1256047650`, `max = 0.0683392329`; `f(1/8) = 0.06833799 ≥ 17/250`; min slack 0.0010836 | OK |
| `t_g0.py` | (G0) 3000 schedules; aux lemma `(1−κ_j) S_n(j+1) ≤ S_n(j)`; necessity of κ ∈ [0,1] | 0 violations |
| `t_R.py` | (R) attainment (278, any real r, κ, b ∈ 0..3) and per-seed bound (500) | 0 failures |
| `t_C.py` | (C) 1371 checks; TV envelope; `0 ≤ U` counterexample; `N = 0` counterexample | 0 violations |
| `t_S.py` | (S1) 1500; (S2) attainment 300; random-pair search; non-decodable control (0.0452) | 0 violations |
| `t_Xp.py` | (Xp) 420 attainments, envelope check | 0 mismatches |
| `t_DG.py` | (D) hard and soft, (G) random lists | 0 violations |
| `tables.py`, `grid.py`, `grid2.py`, `mincount.py` | DESIGN rows, ratios, grids, minimal honeypot counts | as quoted |
| `numerics/umcert_check.py` (the repo script, rerun) | all its checks reproduced | OK |
