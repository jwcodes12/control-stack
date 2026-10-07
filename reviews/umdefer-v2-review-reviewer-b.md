# UMDEFER v2 -- independent hostile review (Reviewer B)

Scope: `ledger/UMDEFER.lean` (v2), against the v1 brief and Reviewer A's v1 review.
No Lean/lake was run (per instructions); all Lean text below is untested. All brute force is exact `Fraction`
arithmetic, scratch in `<scratch>/` (`lib.py`, `t_*.py`).

## 0. Verdict: MINOR (accept after the three mandatory fixes M1-M3)

Every conjunct of v2's Claim and Witness is TRUE as stated (about 170,000 exact checks, no counterexample, including
all the edge cases you listed). I found no falsity, no vacuity, no ℕ-subtraction / `0^0` / `choose` trap. What remains is:

- M1 (fidelity, cheap): the contract says "uniform conditional FLOOR alpha" but `catD` encodes an exactly-constant
  fresh coin. The floor reading is a claim about the contract that Lean does not check.
- M2 (docstring falsehood / overclaim): "need about 60% of deferred items audited" is false as a necessity statement
  (the Lean certificate itself shows about 32% suffices), the audit load is adversary-controlled, and the
  decision-relevance paragraph omits that halting dominates deferral in this safety-only model.
- M3 (tightness not formal): the "ratio is attained in the limit" fact is no longer a conjunct (v1 had it only in numerics;
  Reviewer A asked for it formally).

Everything else is MINOR/NIT. v2 is a large improvement over v1; Reviewer A's FATAL-class concerns (false asymptotic, missing
finite horizon, theta = 0 boundary, no-go quantifiers) are all genuinely fixed.

---

## 1. Reviewer A's numbered points: status in v2

| # | Reviewer A point | v2 status | New problem introduced? |
|---|-----------|-----------|--------------------------|
| 1 | uncharged deferred audits | PARTIAL. Documented as "separately funded service" (acceptable option 1 of Reviewer A's three) and load stated. Dynamics unchanged. | The load sentence understates: the untrusted monitor controls the number of flags, so load is up to `q(1-η)N`, not a "small reserve" (issue M2b). The sound halt-on-reserve-exhaustion variant is dominated by the unmetered bound (verified, issue S2). |
| 2 | q*r must be a conditional floor, not an average | PARTIAL. Parameterised by `alpha`, contract text good, Reviewer A's 371/2000 example cited. | YES: Lean has constant fresh-coin alpha, not a floor (M1). Independence of recall across repeated audits of the same content is not stated (S3). |
| 3 | replacement is a hybrid protocol; trusted replacement not failure-free | FIXED (named "audit-then-defer-after-exhaustion"; Replacement contract; "not a general model of labs' routing"). No `eps_T` term, acceptable. | No. |
| 4 | not a Ctrl-Z model | FIXED (explicit disclaimer). | No. |
| 5 | explain the max (attack at u<b decides at once) | FIXED (docstring (b) explains; no "geometric trial" for arbitrary generators). | No. |
| 6 | finite horizon, theta = 0, attainment | MOSTLY FIXED: `finiteCap`, no `0<theta`, attainment equality (c), division-free closed form. MISSING: the limit / tightness of the ratio as a formal conjunct (M3). | No. |
| 7 | (c) too coarse; make finite curve primary | MOSTLY FIXED: certificate (d) + coarse corollary with `[0<b]`; N = 0 is fine (looser but valid). NOT done: hockey-stick / soft slack / general kappa; corollary not capped at 1 and `protocolCatD ≤ 1` is not a conjunct (S1). | No. |
| 8 | false asymptotic in (d) | FIXED: `t_K = 1/sqrt(K+1)` is correct (I checked numerically: nh=100: 0.37 at K=1e4, 0.90 at K=1e6, 0.99 at K=1e8). | (e') is a pure analysis fact, not tied to `protocolCatD` (S4). |
| 9 | quantify every honeypot law; drop `b ≤ N` | FIXED, verified (all N incl. N<b, all PH, t in {0,1}, ns ≥ nh, nh = 0). | No. |
| 10 | burn legitimacy / scope | FIXED (scope paragraph; Greenblatt App. G and LASR inverse honeypots named as guards; not a necessity theorem). | Residual phrase "no-go for every honeypot law" in the Novelty paragraph overclaims (S5). |
| 11 | lab decision as feasible target risk | PARTIAL: prose corollary only; uses r = 1 (worst case for q), says "need", no feasibility floor `1-r` discussion, no no-regret threshold, no statement that halting dominates (M2). | The "need 60%" claim is false (see 2.4). |
| 12 | domination / adversary-scope contract | NOT FIXED: nothing about class coverage (UMHS domination from content-only mediator), sup-vs-average of the pass bound `A`, or that the monitor must be unable to tell test from deployment (S6). | No. |
| 13 | Witness does not exercise retry suppression | MOSTLY FIXED (29/200 vs 19/100, finiteCap, 3/16 all verified). Protocol-level certificate (d), the coarse corollary, (c) tie to `retry`, and (e') are still not exercised (S7). | No. |
| 14 | novelty narrowed | MOSTLY FIXED (Shlegeris post and LASR u/(c+u) cited; claim narrowed). Games for AI Control and Ctrl-Z are absent from the Novelty paragraph; "no-go for every honeypot law" overstated (S5). | No. |

---

## 2. TRUTH: independent brute force

Method. A transcription of `catD` (identical recursion, history tuples `(x,z,pass)`), plus an exact Bellman maximiser
`Vstar(n,u)` = sup over ALL history-dependent randomised generators (the recursion is linear in `π`, so the optimum is
deterministic and depends on `(n,u)` only). Checking `Vstar ≤ finiteCap` is therefore strictly stronger than testing
random generators; I did both.

### 2.1 (a)
- `catD η=1 = cat` and for arbitrary real `r, α`, arbitrary (non-kernel) `M, φ, π`: 500 instances, exact. The
  statement is hypothesis-free and TRUE.
- `0 ≤ catD ≤ 1`: holds in all 16,879 Vstar instances (incl. empty `Bad`).

### 2.2 (b) finiteCap, the main risk
- 16,879 instances, `Vstar ≤ finiteCap` with `A` = true max bad pass prob, `A = 1`, and `A0 + 1/7`; plus 600 random
  history-dependent generators. Parameters drawn from `{0,1,1/2,1/4,3/4,1/3,1/10}` for `r,η,α,φ` (so theta = 0,
  A = 0, A = 1, r in {0,1}, eta in {0,1} all occur), `b ≤ 4`, `N ≤ 9`, `u0 ≤ 6` (u > b, u = b, n ≤ b-u, b = 0, N = 0).
  0 violations. 6,886 of them are exactly tight.
- The induction side conditions needed for the proof (checked on 20,000 random points each): `finiteCap(n-1,u) ≤
  finiteCap(n,u)`, `finiteCap(n-1,u+1) ≤ finiteCap(n,u)` (the two benign-continuation steps), monotone in `n`, and
  monotone in `A` on [0,1] for r, theta in [0,1]. 0 violations. (It is NOT monotone in `u`: `cap(n,u+1) > cap(n,u)`
  happens 1088/20000 times -- harmless, the proof never needs it, but do not state it.)
- NEW FACT (strengthens (b)): `finiteCap` is the EXACT worst case. On the two-item instance (benign view flagged
  w.p. 1, attack view passed w.p. A) `Vstar = finiteCap` in 4000/4000 random parameter draws, for every `(r,η,α,A,b,N,u)`.
  So (b) is not merely an upper bound; it is the sup over generators. This could be a formal tightness conjunct (S8).
- Interleaving benign/bad: covered by Vstar (the maximiser may attack at u < b, but then the state is decided with
  `1-r+rA`; it may burn only part of the audits, which is dominated by the induction steps above).
- Floor generalisation (relevant to M1): replacing constant `α` by an arbitrary history-dependent hazard
  `α(h,x,z) ≥ α0` keeps `catD ≤ finiteCap r A (θ(η,α0))` (500 random instances, 0 violations). So the floor reading is
  TRUE; it just is not what the Lean states.

### 2.3 (c) attainment, closed form, ratio
- `catD φ=const A, π=point mass x, u ≥ b = retry A θ n` for ARBITRARY reals `r, η, α, A` (outside [0,1], 1500
  instances, arbitrary prefix history `h`, arbitrary kernel `M`): exact. The hypothesis `b ≤ u` is essential
  (counter: r=1, α=1/2, b=1, u=0, n=2 gives 1/10, not 29/200).
- Closed form `(θ + A(1-θ)) retry A θ n = A(1 - ((1-A)(1-θ))^n)` for arbitrary reals: 5000 instances, exact
  (it is a polynomial identity: `1-(1-A)(1-θ) = θ + A - Aθ`).
- Ratio `retry ≤ A/D` needs `A ≤ 1`, `θ ∈ [0,1]`, `D > 0` and all are used (A = 3/2: retry 3 = 39/32 > A/D = 6/5;
  θ < 0 also fails). `θ = 0, A > 0` is covered and gives the bound 1 (`retry = 1-(1-A)^n`). `A = 0` gives 0.
- Limit: `retry A θ n → A/D` (e.g. 0.181818... vs 0.181818... at n = 200). TRUE but not a conjunct (M3).

### 2.4 (d) certificate and coarse corollary
- Per-seed argument checked exactly on 1461 random protocol instances (Ω ≤ 2 seeds, history-dependent `π ω`, hard slack,
  `L` = minimal domination constant plus slack): `S(h_ω)·catD ≤ S(h_ω)·finiteCap r (min 1 (L h_ω)) θ b N 0`, with
  `surv = binCDF(nh,ns,h_ω)`, and each bad pass prob ≤ `min 1 (L h_ω)`. 0 violations.
- Coarse corollary `max([0<b]((1-r)+rH), H/θ)`: 1428 protocol instances, plus 123,000 `(nh,ns,b,N,r,θ,L,t)` grid points
  (`S(t)·finiteCap(min 1 (L t)) ≤ coarse`), plus 2000×41 points with `b>0, N ≤ b` specifically. 0 violations.
  ANSWER to your question: yes, `max(if 0<b then (1-r)+rH else 0, H/θ)` is a valid upper bound when `b>0` but `N ≤ b`
  (N ≥ 1: the attack-at-once term `1-r+rA` is the cap and it IS the first term; N = 0: cap is 0 and the bound is ≥ 0).
  Valid, loose when N = 0, and it can be vacuous (H/θ > 1, e.g. 600 at θ = 1/100, L = 10).
- Proof side conditions confirmed: `A_ω = min 1 (L h)` is a valid bad-pass bound needs `L ≥ 0`, `push M PH ≥ 0`, `φ ≥ 0`
  and `E(M x) φ ≤ 1`; `D ≥ θ`; T3c at `t = h ∈ [0,1]`; `surv ≥ 0` needs `kappa ∈ [0,1]` (true for hardKill).
- finiteCap monotonicity in `A` is NOT needed for (d) (the pointwise `A_ω` is plugged in exactly) but it makes the
  coarse corollary and any looser-envelope use clean (lemma in section 5).

### 2.5 The 1/θ factor and the "60%" example (decision relevance)
- Tight asymptotically (`A/D ≈ A/θ` as `A→0`), loose at the optimum. With `L=1, ns=5, nh=10^4, ε=1e-3, r=1, b=0`:
  coarse needs θ ≥ H/ε = 0.5999; the exact `sup_t S(t)·retry(min(1,t), θ, N)` is ≤ ε iff θ ≥ 0.3165 (identical for
  N = 10^3 ... 10^9). The 0.3165 is also necessary within the domination class (the identity-mediator/point-mass-honeypot
  instance attains it). So "need about 60%" is FALSE as written; 60% suffices, about 32% is needed (M2a).
- With `r<1` the floor `1-r` dominates quickly (r = 0.99: floor 0.0106 vs the example's 1e-3 target is unreachable at ANY q),
  and the retry term binds only if `H/θ > (1-r)+rH`, i.e. `θ < H/((1-r)+rH)` (about 0.057 at H = 6e-4, r = 0.99). The
  example's r = 1 is the worst case for required q (no-regret then needs θ = 1).

### 2.6 (e) no-go and (e')
- 4000 random draws of `(nh ≤ 7, ns ≤ 9, b ≤ 5, N ≤ 9, t, PH(true))` with `t, PH(true)` including 0, 1, and `r` an arbitrary
  real in [-8,8]: `protocolCatD = binCDF nh ns (PH true · t) · (1 - (1-t)^(N-b))` exactly, including N < b (both 0),
  N = b, t = 0, t = 1 (`0^0 = 1` convention gives 0 at N = b), nh = 0, ns ≥ nh. The lower bound `(1-t)^nh ... ≤ ...` holds for
  every `PH` because `binCDF ≥ (1-h)^nh ≥ (1-t)^nh` for `h = PH(true)·t ≤ t`; it does NOT need monotonicity of binCDF in h.
- Clean proof route: for the instance, `catD n u h = 1 - (1-t)^(n - (b-u))` whenever `(u<b → count_flags h = u) ∧ (b ≤ u → b ≤
  count_flags h)`; I verified this uniform formula on 500 states (`t_inv.py`). One lemma, induction on n generalising `u h`.
- (e'): mathematically true (`(1-s)^nh → 1`, `(1-s)^K ≤ exp(-sK) = exp(-K/√(K+1)) → 0`). Numerics: nh = 100 row: 0.0, 0.0,
  0.366, 0.905, 0.990 for K = 1e1, 1e2, 1e4, 1e6, 1e8. The asymptotics are slow; the sup over t is much better (the
  existing `umdefer_check.out`: nh=100, ns=5, K=1000 gives 1.000).

### 2.7 Witness
All five Witness items verified exactly: 29/200, 19/100, `theta 0 (1/2) = 1/2`, `finiteCap 1 (1/10) (1/2) 1 3 0 = 29/200`
(= max(1/10, retry 2)), 3/16. Argument orders match the definitions (`catD ... r η α b n u h`, `protocolCatD ... r η α b N ρ φ π`).

### 2.8 Sanity of the contract counterexample
Reviewer A's deployment-wide coin example: (1/2)(1/10) + (1/2)(1-(9/10)^3) = 371/2000 = 0.1855 > 2/11 = 0.1818 and also >
`retry (1/10) (1/2) 3 = 0.16525`. Confirmed.

---

## 3. FIDELITY

### 3.1 Is the docstring's protocol faithful to `catD`?
Yes, line by line: `u<b` branch = PROT; at `u ≥ b`, `(1-η)·((1-α) if Bad else 1)·cont` is exactly "halt w.p. η, else defer;
deferred bad ends safely w.p. α; benign continues"; `(1-η)(1-α) = 1-θ` is a hypothesis-free polynomial identity.
The generator seeing `(x,z,false)` for deferred rounds is harmless (history-uniform induction). One nuance the docstring
should state: `η>0` also halts on BENIGN exhausted flags (availability cost; irrelevant for safety).

### 3.2 Issues

**M1 -- MAJOR (cheap) -- the "uniform conditional floor" is not what `catD` encodes.**
`catD` multiplies by `1 - α` with a constant `α`, i.e. an exactly-fresh coin of probability exactly `α` independent of
`(h,x,z)`. The contract says the safe-end probability must only be `≥ α` conditional on the history; Reviewer A's point 2 asked
for the theorem to be proved FOR THE FLOOR. The floor version is true (verified, 2.2) and the proof is no harder,
but as frozen the Lean says less than the docstring. Fix (replace `α : ℝ` by a hazard function; constants recover everything):

```lean
noncomputable def catD {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r η : ℝ)
    (α : Hist X Z → X → Z → ℝ) (b : ℕ) : ℕ → ℕ → Hist X Z → ℝ
  | 0, _, _ => 0
  | n + 1, u, h => ∑ x, π h x * ∑ z, M x z *
      (φ z * (if Bad x then 1 else catD Bad M φ π r η α b n u (h ++ [(x, z, true)])) +
       (1 - φ z) * (if u < b then
                      (if Bad x then 1 - r else catD Bad M φ π r η α b n (u + 1) (h ++ [(x, z, false)]))
                    else (1 - η) * ((if Bad x then 1 - α h x z else 1) *
                      catD Bad M φ π r η α b n u (h ++ [(x, z, false)]))))
```
(b) becomes (add `α₀`, replace the `0 ≤ α → α ≤ 1` hypotheses):
```lean
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r η α₀ A : ℝ)
      (α : Hist X Z → X → Z → ℝ) (b : ℕ),
      IsKernel M → IsRule φ → (∀ h, IsDist (π h)) → 0 ≤ r → r ≤ 1 → 0 ≤ η → η ≤ 1 → 0 ≤ α₀ →
      (∀ h x z, Bad x → α₀ ≤ α h x z ∧ α h x z ≤ 1) → 0 ≤ A → A ≤ 1 →
      (∀ x, Bad x → E (M x) φ ≤ A) →
      ∀ n u h, catD Bad M φ π r η α b n u h ≤ finiteCap r A (theta η α₀) b n u)
```
(`α₀ ≤ 1` follows if any bad `x` exists; otherwise add it.) (a), (c), (d), (e) specialise with `fun _ _ _ => α₀`
(for (c)/(e) the statement is unchanged with that substitution). The only proof change: in the exhausted branch use
`(1-η)(1-α h x z) ≤ 1-θ(η,α₀)` and `≥ 0`.

**S3 -- MINOR (contract wording) -- recall independence across repeated audits.**
"each caught with recall r" is the most fragile assumption of the whole v2: PROT only ever audits an attack once (the first
miss is a catastrophe), so per-audit independence never mattered. UMD retries the SAME content, so the contract needs
"recall `r` conditional on earlier missed audits of the same or equivalent content, i.e. auditor noise is fresh per audit".
A deterministic auditor that misses a repeatable attack has `α_eff = 0` even though its average recall is `r`. Add to the
docstring: the guarantee is for `α(h,x,z)` as defined by the contract; nothing certifies `α = q r` for a content-deterministic
reviewer.

**M2 -- MAJOR (docstring) -- resource and decision claims.**
(a) "need about 60% of deferred items audited": false as necessity (2.5: exact threshold 0.3165). Say "the coarse
corollary certifies at 60%; the finite certificate certifies already at about 32% (r=1, b=0); no lower θ works against
the identity-mediator instance".
(b) "Their expected load is q times the number of exhausted-budget flags, honest ones included": add that the number of
flags is ADVERSARY-CONTROLLED (the colluding monitor flags every benign item for free), so the worst-case load is
`q(1-η)N`, proportional to the deployment horizon. "Separately funded" therefore means unmetered. Remark to add (true,
verified by exact DP on 600 instances, 53 strictly lower): the protocol that stops (halts) when a finite reserve `d` of
deferred audits is exhausted has value ≤ the unmetered `catD` with `α = q r` (halting is safe, coupling), so (b)-(d) remain
valid UPPER bounds for the metered, fail-safe variant, at the price that the adversary can force a halt (DoS) by burning the
reserve. Not formalised; state as a remark only, or add a counter `v` and a conjunct if you want it in Lean.
(c) Decision relevance. In this safety-only model the halting action `η = 1` is optimal: risk ≤ `(1-r)+rH` independent of
horizon and of q. UMDEFER therefore does NOT say "defer rather than halt"; it PRICES availability: if you refuse to halt on an
unaffordable flag you must buy a stopping hazard `θ ≥ H/ε` (coarse) or the exact finite curve, and to leave the halting
bound untouched `θ ≥ H/((1-r)+rH)`. The v1 sentence "Usefulness of the deferral (availability) is not modelled" was
dropped in v2; restore it, because without it the corollary reads as a recommendation. Also say the example is r = 1, the
worst case for q, and that any target ε below `1-r` is unreachable at every `q`.

**S2 -- see M2(b).**

**S6 -- MINOR -- Reviewer A #12 not addressed.** (b)/(d) hypotheses are sup-type (every bad submission, every `ω`), not averages;
the frozen UMHS class-coverage theorem (content-only mediator, honeypot mass ≥ p on every bad class ⇒ `L = 1/p`) is the one
structural route to the domination hypothesis; and "every colluding pair" presupposes a monitor that is stateless and
cannot tell honeypot from deployment (the frozen model assumption). One sentence each in the docstring.

**S5 -- MINOR -- novelty wording.** "the no-go for every honeypot law" -> "the no-go for every honeypot law on the two-point
space (the identity-mediator instance; point mass is the strongest, by `PH(true) t ≤ t`)". Add the missing prior art to the
Novelty paragraph: Games for AI Control (Griffin-Thomson-Shlegeris-Abate, arXiv 2409.07985; I checked the abstract: a POSG
model of AI-control evaluations focused on trusted monitoring; I could not confirm the Defer action from the fetched text, so
cite it for "a formal game model with a deferral-type action exists" only after checking the PDF), and Ctrl-Z (2504.10374).
Shlegeris' Redwood post (Nov 2024, "Win/continue/lose scenarios and execute/replace/audit protocols", fetched): states
safety odds as `P(caught) / (P(caught) + P(attack succeeds))` per step with a 26%/(26%+3%) ≈ 90% example. With `u = A`,
`c = (1-A)θ`: `u/(u+c) = A/(A+(1-A)θ) = A/D` exactly. So (c)'s ratio is the post's formula; what v2 adds is the
adaptive-generator finite-horizon version, the burn mechanism, and the honeypot composition. The docstring says this already.

---

## 4. Remaining items (all MINOR/NIT)

- **M3 -- (c) limit/tightness not formal.** Add:
```lean
  (∀ (A θ : ℝ), 0 ≤ A → A ≤ 1 → 0 ≤ θ → θ ≤ 1 → 0 < θ + A * (1 - θ) →
      Filter.Tendsto (retry A θ) Filter.atTop (nhds (A / (θ + A * (1 - θ)))))
```
  (true: `c = (1-A)(1-θ) ∈ [0,1)`, `retry = A(1-c^n)/(1-c)`.) Together with (c) attainment this makes the ratio a sharp
  sup, not just an upper bound.
- **S1 -- (a)/(d) small additions.** `0 ≤ protocolCatD ≤ 1` (needs `κ i ∈ [0,1]`): add as a conjunct for `hardKill ns`, so
  the coarse corollary can be stated `min 1 (max ...)`. Also generalise (d) (below).
- **S4 -- (e') not tied to the protocol.** State it for the protocol value:
  `∀ nh ns b PH, IsDist PH → PH true = 1 → Tendsto (fun K => protocolCatD ... (N := b+K) ... (t := tK K)) atTop (nhds 1)`
  or a one-line `squeeze` conjunct using (e); otherwise (e') is a free-floating analysis lemma. (The squeeze needs the
  upper bound `protocolCatD ≤ 1`.)
- **S7 -- Witness additions** (all values exact, verified):
```lean
  retry (1/10) (1/2) 2 = 29/200 ∧
  -- (d)/(c) applicability: point-mass honeypots, view-blind attack passes w.p. 1/2, theta = 1/2, b = 0, N = 2, nh = 2:
  -- survival 1/4, retry 5/8, product 5/32 <= coarse bound H/theta = (1/3)/(1/2) = 2/3
  protocolCatD (X := Bool) (Z := Bool) (Ω := Unit) (fun x => x = true)
      (fun x z => if z = x then 1 else 0) (fun x => if x = true then 1 else 0) (hardKill 0) 2
      1 0 (1/2) 0 2 (fun _ => 1) (fun _ z => if z = true then 1/2 else 0) (fun _ => burnThenAttack 0)
    = 5/32
```
  (`burnThenAttack 0` attacks at once because `0 < 0` is false.) The coarse bound is loose here (2/3); that is honest.
- **S8 (optional) -- formal tightness of `finiteCap`.** Exact worst case (2.2). A conjunct of the form
  `∃ π, (∀ h, IsDist (π h)) ∧ catD (Bool identity instance, φ = fun z => if z = true then A else 0) ... n u [] = finiteCap ...`
  needs a generator that counts `u + flags` to choose attack-now vs burn; only worth it if you want (b) to be a two-sided
  theorem. (e) already gives the `θ = 0, u = 0` case.
- **S9 -- generalise (d)** to arbitrary `κ` and an envelope `Amax`, so domination, hockey-stick and soft slack are
  one-line corollaries (PROT has all four; UMDEFER has one):
```lean
  (∀ (X Z Ω : Type) ... (nh b N : ℕ) (r η α₀ U : ℝ) (κ : ℕ → ℝ) (Amax : ℝ → ℝ) ...,
      IsKernel M → IsDist PH → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
      (∀ i, 0 ≤ κ i ∧ κ i ≤ 1) → 0 ≤ r → r ≤ 1 → 0 ≤ η → η ≤ 1 → 0 ≤ α₀ → α₀ ≤ 1 →
      (∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ Amax t ∧ Amax t ≤ 1) →
      (∀ ω x, Bad x → E (M x) (φ ω) ≤ Amax (∑ z, push M PH z * φ ω z)) →
      (∀ t, 0 ≤ t → t ≤ 1 → survH t κ nh 0 * finiteCap r (Amax t) (theta η α₀) b N 0 ≤ U) →
      protocolCatD Bad M PH κ nh r η (fun _ _ _ => α₀) b N ρ φ π ≤ U)
```
  Domination: `Amax t = min 1 (L t)` (needs the 3-line `E (M x) φ ≤ L Σ q φ ∧ ≤ 1`); hockey-stick: `min 1 (exp η' t + δ)` via T2;
  soft slack: `κ = softKill ns`. The proof is the same pointwise-per-seed argument (T3b + `surv ≥ 0` + `IsDist ρ`).
- **S10 -- no-regret / target corollary (cheap, decision relevant):**
```lean
  ∀ ... (ε : ℝ), 0 < theta η α₀ → (0 < b → (1 - r) + r * H ≤ ε) → H ≤ ε * theta η α₀ → protocolCatD ... ≤ ε
```
  with `H := L * (((ns : ℝ) + 1) / ((nh : ℝ) + 1))`. Immediate from the coarse corollary (`max_le`, `div_le_iff`).
- **NIT:** docstring (b) says "retry n - (b - u)": truncated natural subtraction; say so. Docstring should note that `η = 1`
  halts at an unaffordable flag, not at `u = b` (subsequent PASSes still execute). Docstring header should say the
  trusted replacement is assumed failure-free (it does) and, if desired, a conservative `+ N·ε_T` bound.
- **NIT (Lean):** `burnThenAttack` via `h.filter ... .length` is fine and decidable; keep it (it matches the English). Do
  not replace it by `h.length`: equal on reachable histories but less faithful and not simpler once you carry the
  `u = min (count) b` invariant anyway.

---

## 5. Lean encoding: what makes (b)/(d) hard, what helps

- (b) is a standard induction on `n` generalising `u h`, then `by_cases hu : u < b`, `simp [catD, hu]`. The bad/benign
  split is per `x`; the per-`x` inner sum lemma is: for `IsDist (M x)`,
  `Σ_z M x z * (φ z * P z + (1 - φ z) * Q z) ≤ B` if `∀ z, P z ≤ B ∧ Q z ≤ B`, and for bad `x` the exact value
  `a + (1-a)(1-r)` resp. `a + (1-a) (1-θ) V` using `Σ_z M x z = 1`. Required scalar lemmas:
  `retry_nonneg`, `retry_le_one`, `retry_mono_n`, `retry_mono_A`, and the exhausted step
  `a ≤ A → V ≤ retry n → a + (1-a)(1-θ) V ≤ retry (n+1)` (Reviewer A's `retry_step_supersolution` gives the shape; here the cleaner
  proof is "RHS is increasing in `a` and in `V` because `(1-θ)V ≤ 1`").
- The two nat-arithmetic facts, both `omega`: for `u < b`, `n ≥ 1`: `n - 1 - (b - (u+1)) = n - (b - u)` and the weakening
  `n - 1 - (b - u) ≤ n - (b - u)`. The `if n = 0` guard in `finiteCap` forces a case split in every lemma. Cleaner: define
  `finiteCap` by structural recursion on `n` mirroring `catD`
  (`capB 0 u = 0`; `capB (n+1) u = if u < b then max (1-r+rA) (max (capB n u) (capB n (u+1))) else A + (1-A)(1-θ) capB n u`),
  prove `catD ≤ capB` by a one-line induction, and prove `capB = finiteCap` separately (pure arithmetic, no measure
  theory). This isolates the nat-subtraction pain from the probability pain. (Verified: `capB` recursion computes the same
  value as `finiteCap` because it is the Bellman operator for the worst-case instance, i.e. Vstar on the two-item instance.)
- Division: nowhere in (b)/(d)-certificate (good). The coarse corollary needs `A/D ≤ L t/θ`, via `div_le_div` or, better, the
  multiplicative form `D · retry ≤ A` (from the closed form, `c^n ≥ 0`).
- `finiteCap` monotone in `A` (needed for neatness): `retry_mono_A`:
  `retry A' (n+1) - retry A (n+1) = (A'-A)(1-(1-θ) retry A' n) + (1-A)(1-θ)(retry A' n - retry A n)`; both terms ≥ 0 on [0,1]
  (`retry ≤ 1`). `finiteCap` monotone in `A`: `max_le_max` + `retry_mono_A` + `r ≥ 0`.
- (e): prove the uniform lemma `catD n u h = 1 - (1-t)^(n - (b-u))` under the invariant
  `(u < b → count h = u) ∧ (b ≤ u → b ≤ count h)`, `count h := (h.filter (fun e => e.2.2 = false)).length`. Then the
  protocol sum is `Σ_Unit` and `surv (push M PH) φ κ nh 0 = survH (PH true * t) κ nh 0 = binCDF ...` by frozen T3b
  (needs `Σ push M PH = 1` and `Σ q z φ z = PH true * t`, where `φ false = 0`).
- (e) lower bound: `binCDF nh ns h ≥ (1-h)^nh` (the `j = 0` term, other terms ≥ 0) and `(1-h)^nh ≥ (1-t)^nh` for
  `0 ≤ h ≤ t ≤ 1` (`pow_le_pow_left`); times `1 - (1-t)^K ≥ 0`.
- (e'): `Real.add_one_le_exp`/`Real.one_sub_le_exp_neg` for `(1-s)^K ≤ exp (-s K)`, `tendsto_pow_const_div_const_pow...` or
  direct: `s K = K/√(K+1) ≥ √K - 1 → ∞`; `(1-s)^nh → 1` by `Tendsto.pow`.

---

## 6. Final conjunct list I would freeze (v3)

1. Halting recovery (`catD η=1 = cat`; `protocolCatD η=1 = protocolCat`), `0 ≤ catD ≤ 1`, and `0 ≤ protocolCatD ≤ 1` for kappa in [0,1].
2. (b) finite state bound with the hazard FLOOR `α₀ ≤ α(h,x,z) ≤ 1` on bad submissions, every `θ ∈ [0,1]` (M1 text above).
3. (c) attainment `catD = retry A θ n` (constant hazard, `b ≤ u`, arbitrary reals), division-free closed form, ratio bound,
   AND the limit `retry → A/D` (M3).
4. (d) general certificate in `κ` and `Amax`, instantiated by domination (hard slack) at least; coarse corollary
   `max([0<b]((1-r)+rH), H/θ)`, optionally capped at 1; target-risk/no-regret corollary (S10).
5. (e) no-go equality for every Bool `PH` and every `N` (natural subtraction), the point-mass-style lower bound for every `PH`.
6. (e') protocol-level limit along `t_K = 1/√(K+1)` (S4).
7. (optional) `finiteCap` tightness on the two-item instance (S8).
8. Witness: existing five items + `retry (1/10) (1/2) 2 = 29/200` + the 5/32 protocol-level instance.

Drop nothing; do not claim: necessity of incrimination, a Ctrl-Z model, a lab recommendation, or "60% needed".
