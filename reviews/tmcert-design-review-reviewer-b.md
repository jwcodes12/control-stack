# TMCERT v0 hostile design review (Reviewer B 5.5), 2026-10-07

Reviewer scope: the draft Lean statement and brief in `reviews/tmcert-design-review-prompt.md`. I did not run `lake` or Lean.
All numeric checks are exact-rational (`fractions.Fraction`) unless marked float. Scratch files (all in
`<temporary path> B-tmcert/`): `lean_mirror.py` (literal mirror of `Game`/`Lawful`/`risk`/`Vstar`/`gac`/`memoryless`/`RiskCert`),
`t5_witness.py`, `hunt_t1_t4.py`, `gac_faithful.py`, `nature_gap.py`, `nature_gap2.py`, `poly_t5.py`, `t5_variant.py`,
`gap_family.py`, `realistic_mirror.py`, `run_realistic.py`, `blue_opt.py`, `noisy_clock.py`, `c_only.py`; downloaded
sources `gb.txt` (Greenblatt et al.), `p_2412.12480.txt` (Mallen et al.), `p_2501.17315.txt` (Korbak et al.),
`p_2504.10374.txt` (Ctrl-Z); GAC v2 text from `<temporary path>` (read: Sec. 3, 4, App. B, App. C.1, C.2).

---------------------------------------------------------------------------------------------------------------------

## 0. Verdict: MAJOR revisions (no FATAL)

Every conjunct of `Claim` and of `Witness` is TRUE as stated (section 1). Nothing is false and nothing is vacuous in
the sense of an unsatisfiable hypothesis. The problems are about what the statement *means* and what it *omits*:

- The headline "(T4) exactly" is not what T4 proves, and the name `memoryless` mislabels the Red class (MAJOR M1).
- There is no formal bridge from `gac` to GAC Prop 4.1, although "first instance: Prop 4.1" is the selling point (M2).
- The T5 toy has a degenerate Blue (no defer zone once coins run out). With the defer zone kept at c = 0, as in GAC's
  protocols and in `gac_realistic.py`, the N = 2, C = 1 gap vanishes and first appears at N = 3 (M3).
- T5/numerics are framed as an objection to GAC, but GAC states that Red gets the null observation, "does not observe the
  time or number of audit coins left". The clock issue is known prior art (Greenblatt et al. fn 4, Mallen et al., Korbak
  et al., Ctrl-Z) (M4).
- The certificate can only ever certify the full-information value, so TMCERT cannot reproduce GAC's own numbers
  (0.36 vs 0.71 at GAC scale). The "blind class" half is missing (M5).
- T3 is disconnected from the game and from the model uncertainty (M6).

Novelty verdict: T1/T2/T3 are textbook (finite-horizon verification theorem, robust-MDP rectangularity, Bellman
optimality). That is acceptable infrastructure per the programme rules. The new content is (i) a kernel-checkable certificate
format in the AI-control setting, (ii) a clean, exact "clock/budget-awareness gap" family, and (iii) the observation that
a protocol optimised against GAC's iid Red is MORE exploitable by a clocked Red (my numerics, section 3). The principle
"Red must not know the round index" is NOT new.

---------------------------------------------------------------------------------------------------------------------

## 1. Truth of every conjunct and the Witness (what I checked)

| item | check | result |
|---|---|---|
| T5 (memoryless) | `risk (memoryless b) 2 1 []` = 7b/8 - 5b^2/8 on a 101-point rational grid; 49/160 - (7b/8 - 5b^2/8) = (5/8)(b - 7/10)^2 | true; max 49/160 at b = 7/10 |
| T5 (clocked, Vstar) | clocked = 5/8; `Vstar exG 2 1` = 5/8; Vstar tables `(0,0), (1,1/4), (1,5/8)` | true; 49/160 < 5/8 |
| Witness | `Lawful exG`; `RiskCert` with `V n = exV n (n <= 2), 1 (n > 2)`: all inequalities for n < 60, all s, a | holds; analytic proof for n >= 3: V = 1 and cat + sum K <= 1 (mass) |
| Witness remark | `V = Vstar` only for n <= 2: `Vstar 3 1` = 13/16, not 1 | docstring should not call the extended table "Vstar exG" (MINOR m4) |
| T1 | 1800 random tests: random lawful games (|S| <= 3, |A| <= 3, N <= 4, up to 3 models, random admissible subset), random history-dependent randomised Red, random model selector depending on (h,s,a), certificate = robust Vstar + monotone slack | 0 violations |
| T1 attainment (robust) | Markov nature-argmax + Red-argmax attains the rectangular robust value exactly, 200/200 | true (the draft only states the single-model version) |
| T2 | Vstar is a certificate, is below every certificate, deterministic Markov argmax policy (depends on `h.length`, `s`) attains it: 300 random games, ties allowed | 0 failures; also `0 <= Vstar <= 1` always |
| T3 | random substochastic and non-stochastic `Kh`, negative rewards, sub-solution `W`: `W <= ER` | 0 violations |
| T4a | `Lawful (gac ...)` for random parameters satisfying the hypothesis, including edge values 0/1, C = 0..3 | 0 violations; hypotheses are exactly what is needed (cat >= 0 needs TD <= 1, K(true) >= 0 needs TA <= TD, 1 - FA >= 0) |
| T4b | one line: each risk <= U, so the rho-average <= U | true, trivial convexity (`memoryless` and `Game` play no role) |

Edge cases.
- N = 0: risk = 0 <= V 0 s0. Fine.
- Empty A: `IsPolicy` fails at `(h = [], s0)` (empty sum is 0, not 1), so T1 is vacuously true there. Harmless.
- Empty Theta, or `adm` empty: the selector premise cannot hold (Omega is nonempty because the rho's sum to 1), so T1 is vacuous. Harmless.
- One action: forced policy, fine.
- C = 0: `gac` has `Fin 1`; a = false keeps the state; true catastrophe 1 - TD + TA. Fine.
- Lawful with mass < 1: fine (the missing mass is the safe sink).
- Negative V: impossible. For a nonempty A, `RiskCert` plus `cat >= 0`, `K >= 0` forces `V n s >= 0` by induction. T1 itself needs only `V 0 >= 0` and `K >= 0`.
- Nature's selector depending on the seed: allowed, and strictly stronger than needed (nature knows Red's private seed). Sound, conservative.

Unused hypotheses. T1 uses neither `cat >= 0` nor the mass bound `cat + sum K <= 1`; it uses only `K >= 0`. `Lawful` is
therefore over-hypothesised for T1/T2/T3 (and the signed-cost / expected-harm reading of GAC Sec. 3 would be covered for free).
The mass clause is used by no conjunct except the conclusion of T4a. No conjunct exercises "probability" semantics
(`Vstar <= 1`).

---------------------------------------------------------------------------------------------------------------------

## 2. Issues

### M1 (MAJOR) T4 "exactly", and the class that `memoryless` really is

Where: the prose of (T4) ("sound exactly for the class of Reds whose per-round action law ignores the history, including
the round index"), the conjunct (T4b), and the name `memoryless`.

Why wrong.
1. (T4b) proves only "if sup_beta <= U then every mixture of constants <= U". That is the one-line convexity of an average.
   It says nothing about "exactly". The converse "unsound for any class strictly larger" is FALSE as a general claim:
   if C = 0, or N <= C + 1 (section 3), the constant policy beta = 1 attains Vstar, so enlarging the class changes nothing.
   My table (`gap_family.py`, TA = TD = 3/4 while c > 0, TD = 3/4 also at c = 0, FA = 1/2): gap = 0 for C = 0 and for every N <= C + 1; gap > 0 for N >= C + 2.
   Even N >= C + 2 is not sufficient: TA = 1/2, TD = 3/4, FA = 1/10, C = 1, N = 3 has gap exactly 0 (both 21/64, attained at beta = 1); the gap appears at N = 4.
   So a clean iff does not exist at this generality; the true condition is parameter dependent.
2. `memoryless` is a misnomer. In GAC's own formalism ("memoryless: its actions depend only on the last observation") a
   Red whose observation is the round index IS memoryless. GAC's class is memoryless AND null observation
   (App. B: "ΩR := {onull}"). The draft's `clocked` Red is memoryless in GAC's sense once ΩR ∋ n. The restriction that matters is the
   observation set, not memory.
3. `memoryless β` also ignores the STATE `s`. T4's prose says "ignores the history, including the round index" and never
   mentions the coin count. A Red that sees only the coins, no clock, attacks iff c = 0: risk 0.5745 at GAC scale versus 0.3575 for the best
   fixed beta (`c_only.py`, float). Hierarchy at GAC scale (100 problems, 2 coins, audit FPR 2%, defer FPR 10%):
   null 0.3575 < coins-only 0.5745 < clock-only 0.6688 < both 0.7090.

Fix (conceptual, and it gives the real "exactly when").
- Reframe: a Red with a fixed unknown backdoor rate beta is a FIXED-UNKNOWN-MODEL nature; a clocked or state-aware Red is a
  RECTANGULAR (history-dependent) nature. Concretely, let Theta = [0,1] and `Gβ` the single-action game with the mixed kernel
  `K = β·K_true + (1-β)·K_false`. A constant selector is GAC's Red; a history-dependent selector is the full-information Red.
  Then "memoryless WLOG" iff "the best constant selector attains the rectangular value" (that is a tautology, but it shows
  that T4/T5 and item 2 of the brief (fixed-but-unknown model) are the SAME statement).
- Rename `memoryless` to `constRed` (or `blindIID`), and state T4b as `mixture_const_le`.
- State the WLOG half you can prove (conjunct W below): `C = 0 → risk (constRed 1) = Vstar`, and for time-homogeneous
  parameters `N ≤ C+1 → risk (constRed 1) = Vstar`. The NOT-WLOG half is the instance of M3.
- Replace the word "exactly" by the actual claim: "sound for every Red whose per-round action law is independent of
  (n, s, history)".

### M2 (MAJOR) no formal bridge from `gac` to GAC Prop 4.1; and `gac` agrees with GAC only if TA n 0 = 0

Where: (T4a) (Lawful only) and the docstring "first instance: Prop 4.1".

Facts I checked (Python mirror versus the GAC recurrence, exact rationals, `gac_faithful.py`).
- With p_H^FNR = p_H^FPR = 0, GAC's recurrence (App. C.1, main-text lambda coefficients with `λ6 = f(q^d)`) is
  p[m,c] = β f(qa) + [β (f(qd) - f(qa)) + (1-β)(1-qa)] p[m-1,c] + (1-β) qa p[m-1,c-1] for c >= 1,
  p[m,0] = (1 - β + β f(qd)) p[m-1,0], p[0,c] = 1.
  (The App. C.1 proof text prints `(1 - q^d)β` at the boundary; that is a typo against the main-text λ6 = f(q^d). `gac`
  matches λ6 = f(q^d).)
- `risk (memoryless β)` of `gac` with `TA n c = f(qa (n+1) c)`, `TD n c = f(qd (n+1) c)`, `FA n c = qa (n+1) c` equals 1 - p
  EXACTLY in 200/200 random instances when `qa(.,0) = 0`.
- When `TA n 0 > 0` (which `Lawful`'s hypothesis allows) they differ in 89/200 instances: `gac` follows the main-text sentence
  "if the protocol attempts to audit when no audit coins are left, the code is run instead" (audit zone = catastrophe at
  c = 0), whereas App. C.1 says "Audit actions are ignored" and its boundary formula treats the audit zone as deferral. GAC's
  footnote 14 ("Audit and Run are equivalent when c = 0, assume that Blue never attempts an audit") reconciles them only for
  q^a_{m,0} = 0. So GAC is internally inconsistent off that slice; `gac` is faithful on the slice and the statement should say so.
- Indexing is right: GAC's `m` counts the current problem (z^c_m, "m problems remaining"), so `TA n c` = GAC's `q_{n+1,c}`.
  Folding (m,c)-dependent thresholds into `TA n c, TD n c, FA n c` is faithful (Blue's thresholds enter the safety recursion
  only through f(q^a), f(q^d), q^a). The hypotheses `TA <= TD <= 1` encode nested audit/defer zones.
- Timing: in GAC, Red's action at step t fixes b of problem t+1 (Red chooses simultaneously with Blue's handling of the
  previous problem). In `gac` Red's action concerns the current problem and a state-aware Red sees c AFTER the previous audit.
  So a Lean full-information Red is slightly more informed than a GAC-timed one. This is sound (superset) but "full
  information" in the numerics is not GAC-timed. MINOR; say so.
- Perfect auditor only (p_H = 0); usefulness not modelled. Fine as scope.

Fix (Lean). Add a faithfulness conjunct, with the c = 0 slice as an explicit hypothesis:
```lean
/-- GAC Prop 4.1 / App. C.1 (perfect auditor). `z m c` = P(no catastrophe), m problems left including the current one. -/
noncomputable def zGAC (f : ℝ → ℝ) (qa qd : ℕ → ℕ → ℝ) (β : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | m+1, 0 => (1 - β + β * f (qd (m+1) 0)) * zGAC f qa qd β m 0
  | m+1, c+1 =>
      β * f (qa (m+1) (c+1))
      + (β * (f (qd (m+1) (c+1)) - f (qa (m+1) (c+1))) + (1 - β) * (1 - qa (m+1) (c+1))) * zGAC f qa qd β m (c+1)
      + (1 - β) * qa (m+1) (c+1) * zGAC f qa qd β m c
-- Claim: ∀ C f qa qd, f 0 = 0 → (∀ m, qa m 0 = 0) → (hyps: f monotone, f ≤ 1, 0 ≤ qa ≤ qd ≤ 1 ...) →
--   ∀ β ∈ [0,1], ∀ m (c : Fin (C+1)),
--   1 - risk (fun _ : Unit => gac C (fun n c => f (qa (n+1) c)) (fun n c => f (qd (n+1) c)) (fun n c => qa (n+1) c))
--         (fun _ _ _ => ()) (constRed β) m c [] = zGAC f qa qd β m c.val
```
Proof is an induction on m with `Fin.sum_univ`-style row sums (algebra after unfolding `risk` over Bool and `Fin (C+1)`).
Without this conjunct, "GAC Prop 4.1 instance" is an unchecked claim.

### M3 (MAJOR) the T5 toy is a degenerate Blue; the faithful instance needs N >= 3

Where: `exTA, exFA, exG` with `exG := gac 1 exTA exTA exFA`.

`exTA` is also passed as the defer parameter, so `TD n 0 = exTA n 0 = 0`: once the coin is gone Blue RUNS EVERYTHING with no
monitoring at all. GAC's protocols (and `gac_realistic.py`: `TD = tpr(qd)` independent of c) keep the defer threshold at c = 0.

Check (`poly_t5.py`, exact). N = 2, C = 1, TA = 3/4 and FA = 1/2 while c = 1, but TD = 3/4 at c = 0: best fixed beta = 1 with risk 1/4,
Vstar = 1/4. NO GAP. The reason: in the last round a deferred backdoor is as safe as an audited one, and coin depletion
matters only if >= 2 rounds remain after exhaustion. The smallest gap for this Blue is at N = 3 (C = 1), and in general
needs N >= C + 2. Also `gac_small.py`'s M = 2 gaps come from `qd(m,c) = qa(m,c) + 1/10`, i.e. a defer threshold that is WEAKER at c = 0
than at c >= 1; they are not gaps for a constant-defer Blue.

Replacement instance (N = 3, C = 1; verified exactly; polynomial identity verified on a rational grid):
- Blue: `TA(c≥1) = 3/4`, `TD ≡ 3/4` (all c, no separate defer zone but defer kept at c = 0), `FA(c≥1) = 1/2`, `TA(0) = FA(0) = 0`.
- Every constant β: `risk = 3/4 β - 21/32 β² + 5/32 β³`, and
  `13/50 - risk = (5/32)(β - 4/5)²(13/5 - β) ≥ 0` on [0,1], with equality at β = 4/5. So `sup_β = 13/50 = 0.26`.
- Blind clocked "wait one round, then backdoor twice": risk `11/32 = 0.34375`; `Vstar exG3 3 1 = 11/32` (the best of all 8
  deterministic open-loop sequences; no coin information needed).
- Certificate: `Vstar` table `n=1: (1/4,1/4)`, `n=2: (7/16,1/4)`, `n=3: (37/64, 11/32)` for (c=0, c=1), extended by 1 for n >= 4,
  has no violated inequality up to n = 40.
```lean
noncomputable def exTA3 (_n c : ℕ) : ℝ := if 0 < c then 3/4 else 0
noncomputable def exTD3 (_n _c : ℕ) : ℝ := 3/4
noncomputable def exFA3 (_n c : ℕ) : ℝ := if 0 < c then 1/2 else 0
noncomputable def exG3 : Game (Fin 2) Bool := gac 1 exTA3 exTD3 exFA3
/-- blind clocked Red: wait one round, then backdoor every round -/
def clocked3 : RHist (Fin 2) Bool → Fin 2 → Bool → ℝ :=
  fun h _ a => if h.length = 0 then (if a then 0 else 1) else (if a then 1 else 0)
-- T5': ∀ b ∈ [0,1], risk (memoryless b) 3 1 [] = 3/4*b - 21/32*b^2 + 5/32*b^3 ∧ (… ≤ 13/50)
--      IsPolicy clocked3 ∧ risk clocked3 3 1 [] = 11/32 ∧ Vstar exG3 3 1 = 11/32 ∧ (13/50 : ℝ) < 11/32
```
The sup bound is `nlinarith [mul_nonneg (sq_nonneg (b - 4/5)) (by linarith : 0 ≤ 13/5 - b)]` after `ring_nf`.
Keep the N = 2 toy if you want the smallest example, but label it "no-defer-at-exhaustion toy".

### M4 (MAJOR) T5/numerics are mis-framed as a counterexample to GAC; the clock objection is known prior art

GAC states the assumption explicitly.
- Sec. 3: "the protocol will have access to the state of the untrusted AI system and, therefore, we model Red as memoryless".
- Footnote 13 and App. B: "Since Red also does not observe the time or number of audit coins left, we model Red as receiving
  a null observation in every case. ... (Note that this is not true for all Control Games.)"
- Sec. 8 notes that the "memoryful-leader, memoryless-follower" requirement is a restriction (it precludes many existing solvers).
So Prop. 4.1 is correct for its stated Red class. T5 is a SENSITIVITY result about the stated assumption, not a counterexample.
In GAC's own formalism a clocked Red is a game with ΩR ∋ n.

Prior art (ids verified by downloading the PDFs; quotes from the extracted text):
- Greenblatt, Shlegeris, Sachan, Roger, arXiv 2312.06942, Sec. 2.1 footnote 4: "the attack policy doesn't know how many problems it's
  been asked to solve so far. We make this assumption because the AI developer always gets to choose what context to provide the LLM."
  The 15% win probability of upfront auditing presupposes this (my inference: with a clock the attacker simply waits out the audited prefix).
- Mallen, Griffin, Wagner, Abate, Shlegeris, arXiv 2412.12480, Sec. 1: "The developer resets the AI's context after each problem and
  ensures there is no distributional shift, so the AI does not know how many problems it has solved so far". App. G.2 "Upfront Audit With
  Distributional Shift": if the AI can tell evaluation from deployment, the optimal strategy wins with probability 1.0. (Griffin is
  co-author of both this and GAC.)
- Korbak et al., arXiv 2501.17315 ("A sketch of an AI control safety case"): assumes untrusted models are stateless; lists removing
  "obvious coordination signals like timestamps (E9.3)" and input filters for distribution shift (E9.2) as evidence items; warns about
  "subtle environmental cues or Schelling points".
- Bhatt et al., Ctrl-Z, arXiv 2504.10374: "The models T and U are stateless between calls"; App. L allocates the audit budget A(t) = k e^{-rt},
  front-loaded, justified by "the red team will attack with probability p" per step, i.e. precisely the no-clock assumption.
- Neighbours outside AI control: sequential inspection games with limited inspections (Avenhaus, von Stengel, Zamir, "Inspection Games",
  Handbook of Game Theory vol. III, 2002, pp. 1947-1987; Dresher 1962 is the classical origin, not re-verified); the absent-minded-driver
  structure (Aumann-Hart-Perry 1997, cited by Mallen et al. in a footnote). A stateless blind Red is an imperfect-recall Red, a clocked
  Red is perfect recall: this is standard.
- Sleeper Agents (Hubinger et al., 2401.05566) shows year-conditioned triggers; I could not confirm the wording in the extracted text, cite from memory with that caveat.

Is the round index a realistic observation? In GAC's iid-task model, no (tasks exchangeable, no feature carries n). In agentic
deployments it is plausible: timestamps (Korbak E9.3), task ids, repository state, 100,000 sequential tasks (Ctrl-Z). It also does
not have to be exact: with a blind Red that has a NOISY clock `o = m + N(0,w²)`, attacking iff `o <= j` (`noisy_clock.py`, float,
GAC scale): risk 0.661 (w = 3), 0.646 (w = 6), 0.611 (w = 12), 0.543 (w = 25), versus 0.3575 for the best fixed β.
A one-bit clock "am I in the last ~13 of 100 problems" already gives 0.669.

Numerics at GAC scale (`realistic_mirror.py` / `run_realistic.py`, float; reproduces `gac_realistic.py`):

| Blue (audit FPR, defer FPR) | best fixed β | clocked "attack iff m <= j" (= best 1-bit window; local search found nothing better) | full information |
|---|---|---|---|
| 2%, 10% | 0.3575 (β = 0.065) | 0.6688 (j = 13) | 0.7090 |
| 3%, 10% | 0.3565 | 0.8035 (j = 14) | 0.8474 |
| 5%, 20% | 0.2674 | 0.8990 (j = 24) | 0.9558 |
| 1%, 10% | 0.3835 | 0.5074 (j = 12) | 0.5262 |

All four rows of `gac_realistic.py` reproduced to 4 digits. Caveat: these Blues are FLAT constant-FPR protocols, not GAC's
optimised ones. I therefore also ran Blue optimisation (`blue_opt.py`, float; per-(m,c) audit FPR in [0, 0.10], defer FPR fixed at
0.10, coordinate descent from the flat start; local optima, not certified global):

| N, C | Blue | max_β risk | clocked "iff" | full info |
|---|---|---|---|---|
| 100, 2 | flat 2% | 0.3575 | 0.6688 | 0.7090 |
| 100, 2 | optimised against iid Red (GAC style) | 0.3468 | 0.7733 | 0.8753 |
| 100, 2 | optimised against full information (min Vstar) | 0.4126 | 0.4132 | 0.4152 |
| 30, 2 | flat 2% | 0.3342 | 0.3739 | 0.3889 |
| 30, 2 | optimised against iid Red | 0.2828 | 0.5542 | 0.6736 |
| 30, 2 | optimised against full information | 0.3320 | 0.3330 | 0.3339 |

Finding: protocol optimisation against the memoryless Red makes the protocol MORE clock-exploitable (0.67 -> 0.77, full info 0.71 -> 0.88),
as in Ctrl-Z's front-loaded audit schedule. Designing against full information costs only about +0.07 risk relative to GAC's
optimum (0.347 -> 0.415) and back-loads the audit FPR (0.006 early, 0.024 at m = 25 versus 0.037 up front). That is the
decision-relevant statement, and a better headline than "0.36 versus 0.67".

Fix (text). Replace "counterexample to GAC / GAC's Red is memoryless with a fixed beta" by: "GAC's Red has the null observation
(ΩR = {onull}; GAC App. B). We show the safety number is not robust to dropping that assumption: a clock bit, or the audit-budget state, raises
risk from 0.36 to 0.67 / 0.57 at GAC scale, an optimised Blue is worse, and a full-information-robust Blue recovers most of it. The no-clock
assumption is the one GAC inherits from Greenblatt et al. fn 4 and Mallen et al."

### M5 (MAJOR) the certificate can only certify the full-information value, so TMCERT cannot certify GAC's own claim

T2 says every certificate is at least Vstar. So T1 can never prove a bound below 0.709 for the GAC-scale protocol, while GAC's
claim (under its stated assumption) is 0.3575. The draft's sentence "the certificate method loses nothing; no observation restriction is
assumed" is true only relative to the full-information adversary. For the deployment assumption everybody actually
uses (stateless Red) the certificate is a factor ~2 too pessimistic.

This is consistent with the programme ("capability-free, conditional on explicit trust hypotheses"): the explicit hypothesis
is `H_blind` (Red's observation is independent of (n, s)). Then the right theorem pair is:
1. capability-free: T1 against full information (Vstar);
2. conditional: `H_blind → risk ≤ sup_β risk (constRed β)`, with a CHECKABLE certificate for the sup (the draft's T4b hypothesis
   `∀ b ∈ [0,1], risk ≤ U` is a continuum of reals; no Lean-checkable format is offered).
For 2, certificate form: risk(constRed β) is a polynomial of degree N in β; write it in the Bernstein basis on a grid
of sub-intervals (de Casteljau subdivision), coefficients computed by the same O(N·C) DP in exact rationals; all coefficients
<= U on every sub-interval implies sup <= U (Mathlib has `bernsteinPolynomial`, nonnegative with sum 1). This matches the
UMCERT grid pattern (G). N = 100, C = 2: about 300 cells per β-interval, trivial for `decide` on integer-scaled arithmetic.
For a clocked blind Red (observation = n only) the exact value is an open-loop (POMDP-without-observations) optimum; a sound
upper-bound certificate is a convex piecewise-linear function on the (C+1)-simplex of beliefs (alpha vectors), checkable
for tiny C like GAC's. I would NOT put this in v1; I would state the full-information T1/T2 plus the constant-β certificate
and leave the clocked class as a numerically evidenced gap (lower bound by an explicit Red, as T5).

### M6 (MAJOR) T3 is disconnected from the game and from model uncertainty

(T3) is the textbook sub-solution bound for an arbitrary substochastic `Kh` and `rew`. Nothing ties `Kh` to the Blue
controller inside `G`, so "honest usefulness of THIS protocol" is not expressed. It also has no uncertainty (`adm`) while T1 has,
so the usefulness guarantee is for a fixed known model: asymmetric, and false under the very uncertainty T1 certifies against.
`gac` cannot even state GAC's usefulness: it has no defer FPR for safe solutions (`FD`), and GAC's Prop. C.2 counts
`(1 - q^d) + q^a` used solutions per round.

Fix.
```lean
def honestChain {S A} (G : Game S A) (a0 : A) : ℕ → S → S → ℝ := fun n s s' => G.K n s a0 s'
/-- robust usefulness certificate: sub-solution for every admissible model -/
def UseCert {S A Θ} [Fintype S] (G : Θ → Game S A) (adm : Θ → Prop) (a0 : A) (rew : Θ → ℕ → S → ℝ) (W : ℕ → S → ℝ) : Prop :=
  (∀ s, W 0 s ≤ 0) ∧ ∀ th, adm th → ∀ n s, W (n+1) s ≤ rew th n s + ∑ s', (G th).K n s a0 s' * W n s'
-- Claim: for every admissible selector θ (history-dependent), expected honest reward ≥ W N s0.
-- GAC bridge: with FD, rew n c = (1 - FD n c) + (if 0 < c then FA n c else 0)  [TA n 0 = FA n 0 = 0],
--   ER (honestChain (gac …) false) rew = uGAC (App. C.2).
```
`uGAC` is the C.2 recurrence `u^c_m = (1-qd) + qa·u^{c-1}_{m-1} + (1-qa)·u^c_{m-1}` (c >= 1), `u^0_m = (1-qd) + u^0_{m-1}`, `u^c_0 = 0`.

---------------------------------------------------------------------------------------------------------------------

### MINOR issues

- m1 (T1 shape). The seeds `Ω`, `ρ`, and a seed-dependent `θ ω` add nothing: the bound is pointwise per `ω`, and the average of
  bounded quantities is bounded. Randomisation of Red is already covered by `σ` being behavioural (Kuhn's theorem, perfect recall:
  `RHist` contains Red's own actions and the states). Nature's selector is deterministic and can be pure WLOG (the objective is
  linear in nature's mixing). State T1 as a single `(σ, θ)` with the invariant `∀ n s h, risk … n s h ≤ V n s` (stronger and
  reusable by T4/T5) and derive "seeded" as a one-line corollary.
- m2 (nature model). Selecting θ after seeing Red's current action `a` is harmless: nature and Red are on the same side (both maximise
  risk), so max_a max_θ = max_θ max_a. The rectangular selector (a different model in every (n,s,a) cell) is a STRICTLY stronger adversary than a
  fixed-but-unknown model, and it is the right one for a per-cell certificate check, but it is conservative for an ROC confidence
  set (a single ROC cannot give high FPR in early cells and low TPR in later ones). Exact example (`nature_gap2.py`, `gac`, C = 1,
  N = 2, two models, index 0 = last round): model 1 has `TA = TD = (1/2, 1/2)`, `FA = (0, 0)`; model 2 has `TA = TD = (1, 1/2)`,
  `FA = (0, 1/2)`. Each model alone has `Vstar = 1/2`; the rectangular value is 3/4 (nature uses model 2 in the first round for its
  FA = 1/2 and model 1 in the last round for its smaller TA). Provide the weaker statement as a separate corollary:
  `(∀ θ adm, RiskCert (fun _ : Unit => G θ) (fun _ => True) (V θ)) → ∀ σ θ adm, risk (G θ) σ N s0 [] ≤ V θ N s0`
  (trivial from T1 with `Θ = Unit`). Note M1: this fixed-model reading is exactly GAC's blind class when Θ is the β-simplex.
- m3 (coverage claim). "Every observation-restricted Red is covered" is true for Reds whose information is a function of the
  `(S × A)` history. A Red with extra non-persistent information (task content, the monitor's zone draw) is covered only if
  future transitions are conditionally independent of that information given `(n, s, a)`. That is the iid-task hypothesis and
  should be stated as such in the docstring; for non-exchangeable task streams `S` must absorb the task context.
- m4 (Witness docstring). "Vstar exG is a certificate ... explicit table" is true for n <= 2 only; the Witness's `V n = 1`
  for n > 2 is a valid but non-tight certificate (checked). Say so, and note the tail is `Lawful`-mass (cat + sum K <= 1).
- m5 (T2 scope). Tightness is stated for a single model only. The robust statement holds and is cheap: for a finite model set
  `Θ`, `Vrob (n+1) s = max_{θ adm, a} (cat + Σ K Vrob n)` is a certificate, is below every certificate, and is attained by a Markov
  pair `(σ, θ)` (verified 200/200). Without it, "the certificate method loses nothing" is unproved for exactly the part
  (uncertainty) the draft advertises.
- m6 (unused strength). Add `Vstar ≤ 1`, `0 ≤ risk ≤ 1` (uses the mass clause of `Lawful`), and a lemma `RiskCert → 0 ≤ V` so that
  `Lawful` is not decorative and silly certificates are excluded in the checker.
- m7 (checker data type). `TA, TD, FA` are free reals: no ROC structure (TA = f(FA)), no score laws, no thresholds. The
  `gac` interface is therefore a parameter interface, not a Beta-score model. Discretised scores in GAC (6 decimals) cannot hit exact FPR levels;
  an ROC-with-intervals interface (below) is the natural way.
- m8 (T5 docstring). "at a 2-problem, 1-coin instance" and "audit zone 3/4 for a backdoor and 1/2 for a safe solution while a coin remains, no defer zone, and no audit
  without a coin" is accurate but should add "and no monitoring at all after exhaustion" (M3).

---------------------------------------------------------------------------------------------------------------------

## 3. Answers to the seven check items

1. Truth. All conjuncts and the Witness are true; edge cases in section 1. Over-hypothesised, not under-: `Lawful` is stronger than T1/T2/T3 need.
2. `risk` as "every history-dependent Red". Yes: Red seeing `(h, s)` covers every Red whose information is a function of the
   `(S × A)`-history, including blind, clocked and budget-aware Reds (the m3 caveat). Seeding adds nothing beyond behavioural
   randomisation (Kuhn); it is redundant, not wrong. Nature selector: correct as the (s,a)-rectangular robust-MDP model of
   "uncertainty in conditional transitions" (Iyengar 2005; Nilim-El Ghaoui 2005; not re-fetched), conservative versus a
   fixed-unknown model (gap 3/4 vs 1/2 above). Both statements should be present (m2).
3. `gac` fidelity. Matches GAC App. C (state c, coins, audit/defer/run zones, audit of a safe solution uses a coin, defer continues,
   caught backdoor to safe sink) exactly when `TA n 0 = 0` (M2); folding thresholds into `TA/TD/FA` of `(n, c)` and the
   indexing `n = remaining - 1` are right; the audit-with-no-coin convention is GAC §4 (run), whereas App. C ignores the audit
   (internal GAC inconsistency, harmless under footnote 14).
4. T4 and "exactly when". T4b is convexity, not an iff (M1). The real exactly-when is information-theoretic: the constant-β
   class attains Vstar iff the Bellman argmax can be taken constant on the reachable set (tautologically crisp, but it gives conditions):
   C = 0, or time-homogeneous with N <= C + 1, WLOG; N >= C + 2 and parameter inequalities, gap (table below). Fair objection? As
   an objection to GAC's theorem, no (M4). As a sensitivity/decision result, yes, and the optimised-Blue finding makes it stronger.
5. Novelty. The principle is known (M4 list). New: exact small instance with the faithful Blue (M3), the budget-awareness channel (0.57),
   noisy-clock sensitivity, and the optimised-Blue exploitation numbers. T1/T2: classical (also Funke-Jantsch-Baier TACAS 2020,
   arXiv 1910.10636, Farkas certificates for MDP reachability bounds; CertRL 2009.11403 and Isabelle AFP "MDP-Algorithms" formalise
   Bellman optimality). The Lean artifact for AI control is the contribution; do not claim novelty of the verification theorem.
6. Lean encoding (estimates, no compile). T1: induction on `n` generalised over `s h`, `Finset.sum_le_sum`,
   `mul_le_mul_of_nonneg_left`, ~40 lines; uses only K >= 0. T2 (a)/(b): `Finset.le_sup'`, `Finset.sup'_le`, ~25 lines. T2 (c): pick
   `a*` per `(n, s)` with `Finset.exists_mem_eq_sup'`, define `σ h s a := if a = astar (N - h.length - 1) s then 1 else 0`
   (depends only on `h.length` and `s`), prove `∀ n s h, h.length + n = N → risk … n s h = Vstar G n s` by induction with
   `Finset.sum_eq_single`; ~60-80 lines; the invariant `h.length + n = N` is the only delicate point (use `Nat` subtraction safely).
   `Lawful (gac …)`: row sums over `Fin (C+1)`: for a = false, c > 0, rewrite `c'.val + 1 = c.val ↔ c' = ⟨c.val - 1, _⟩`
   (`Fin.ext_iff`, `omega`) and use `Finset.sum_ite_eq'`; ~40 lines. Witness: `rcases n with _|_|_|n`, `fin_cases`, `norm_num`; the
   `n >= 3` branch from the mass clause. T5: `simp [risk, memoryless, gac, exTA, exFA, Fin.sum_univ_two, Fintype.sum_bool]` then `ring`/`nlinarith`;
   `Vstar` on `Bool`: `Fintype.univ_bool`, `Finset.sup'_insert`. Nothing needs `native_decide`.
7. What is missing for the checker at GAC scale (ranked):
   (a) a computable rational checker `checkCert : (n,s,a,vertex) → V → Bool` with `checkCert_sound : checkCert = true → RiskCert …`
       (soundness bridge); integer-scale the table so the kernel uses accelerated Nat arithmetic (`Int` over a common denominator), no `gcd`;
   (b) interval models: per-cell parameters `(TA, TD, FA)` in a box. `cat` and `K` are AFFINE in `(TA, TD, FA)` and the cell inequality is
       affine in them, so checking the 8 vertices per cell (vertex lemma, convexity) suffices; this replaces an infinite `Θ`;
   (c) the Bernstein/subdivision certificate for the blind class (M5), reusing UMCERT's grid pattern;
   (d) usefulness (M6) with `FD` and Prop. C.2;
   (e) ROC from score laws: finite pmf for safe/backdoored scores and `TA = tail mass above the threshold` with monotonicity,
       so the estimated-ROC interval (e.g., Clopper-Pearson) maps to a box;
   (f) the bridge `zGAC` (M2).
   A 100-problem, 2-coin certificate is 300 numbers and 600 inequalities per model vertex: kernel-checkable.

Gap table (time-homogeneous `gac`, TD(0) = TD(c>0), TA(0) = FA(0) = 0; full-information minus best constant β, `gap_family.py`, float to 1e-4;
N down, C across; TA = TD = 3/4, FA = 1/2):

| N \ C | 0 | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|---|
| 2 | 0 | 0 | 0 | 0 | 0 | 0 |
| 3 | 0 | 0.0837 | 0 | 0 | 0 | 0 |
| 4 | 0 | 0.1815 | 0.0461 | 0 | 0 | 0 |
| 5 | 0 | 0.2713 | 0.1240 | 0.0234 | 0 | 0 |
| 6 | 0 | 0.3450 | 0.2137 | 0.0755 | 0.0117 | 0 |
| 7 | 0 | 0.4016 | 0.3009 | 0.1482 | 0.0439 | 0.0059 |
| 8 | 0 | 0.4429 | 0.3776 | 0.2302 | 0.0969 | 0.0249 |

Over 7 parameter sets x N = 2..8 x C = 1..5, `N <= C + 1` never had a gap (necessary condition N >= C + 2 for a gap held in all 245 cases);
sufficiency failed for parameter sets where always-attack remains greedy-optimal (e.g. TA = 1/2, TD = 3/4, FA = 1/10: gap 0 at N = 3, C = 1).

---------------------------------------------------------------------------------------------------------------------

## 4. Fixes in priority order

1. M2: add the `zGAC` bridge conjunct (with `TA n 0 = 0`); otherwise "Prop 4.1 instance" is unchecked.
2. M3: replace the T5 instance by `exG3` (N = 3, defer kept at c = 0); keep the N = 2 toy only as a labelled degenerate example.
3. M1/M4: rename `memoryless`, drop "exactly", reframe T5 as a sensitivity result against GAC's stated null-observation assumption;
   cite Greenblatt fn 4, Mallen et al. (Sec. 1, App. G.2), Korbak E9.3, Ctrl-Z App. L; add the budget-awareness channel and the
   optimised-Blue numbers (clearly marked float, local-search).
4. M5: state the two-tier theorem (capability-free full-information T1/T2; conditional `H_blind → ≤ sup_β` with a Bernstein/grid certificate).
5. M6/m5: robust usefulness certificate tied to the same game; robust tightness (finite Θ).
6. m1/m2: simplify T1 (single σ, θ, invariant for all n s h; weaken to K >= 0); add the fixed-model corollary and the 3/4 vs 1/2 gap example.
7. Add the consumption conjunct (T1 applied to the Witness) so the pipeline "certificate to bound to Red's reach" is actually exercised.

---------------------------------------------------------------------------------------------------------------------

## 5. Final conjunct list I would freeze (TMCERT v1)

Definitions: `Game`, `Lawful` (keep, but add `KNonneg`), `RHist`, `IsPolicy`, `risk`, `RiskCert`, `Vstar`, `ER`, `gac`, `constRed`
(renamed `memoryless`), `zGAC`, `uGAC`, `honestChain`, `UseCert`, instances `exG3`, `clocked3` (and the labelled N = 2 toy `exG`).

1. (Sound) For one policy `σ` and one admissible selector `θ`: `∀ n s h, risk G θ σ n s h ≤ V n s` under `KNonneg` and `RiskCert`.
   Corollaries: the seeded mixture form; the fixed-model form (`V θ` per admissible θ); `0 ≤ V` for nonempty A.
2. (Tight) `Vstar` is a certificate, is least, and is attained by a deterministic Markov argmax Red (`h.length`, `s`); the robust analogue
   with finite `Θ` (attained by a Markov pair); `0 ≤ Vstar ≤ 1` for `Lawful`.
3. (gac lawful) `Lawful (gac C TA TD FA)` under the draft's hypotheses.
4. (gac faithful) `1 - risk (constRed β) = zGAC` for `TA n 0 = 0` (GAC Prop. 4.1).
5. (Blind class) `mixture_const_le`: sup over constant β bounds every mixture of constants (convexity), plus a Bernstein/grid certificate
   lemma turning a finite coefficient check into `∀ b ∈ [0,1], risk (constRed b) ≤ U`.
6. (WLOG half) `C = 0 → risk (constRed 1) = Vstar` for `gac`; optionally `N ≤ C+1` for time-homogeneous parameters.
7. (Gap half, T5') exact instance `exG3`: constant β risk `= 3/4 b - 21/32 b² + 5/32 b³ ≤ 13/50`, `clocked3` risk `= 11/32 = Vstar exG3 3 1`; `13/50 < 11/32`.
   (Optionally also the N = 2 no-defer-at-exhaustion toy: `7/8 b - 5/8 b² ≤ 49/160 < 5/8`.)
8. (Consumption/Witness) `Witness` for `exG3`: `Lawful`, `RiskCert` for all n, and the conclusion `∀ σ, IsPolicy σ → risk exG3 σ 3 1 [] ≤ 11/32`
   (T1 applied) together with attainment by `clocked3`.
9. (Usefulness) `UseCert` soundness for every admissible selector, bridged to `gac` via `honestChain` and `uGAC` (Prop. C.2).

Everything else (numerics at GAC scale, optimised-Blue results, noisy-clock curve, observation hierarchy 0.36 / 0.57 / 0.67 / 0.71)
stays as float numerics labelled as such, with the explicit scope line: "these are not Lean theorems".
