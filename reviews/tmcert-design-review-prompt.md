You are a HOSTILE REVIEWER of a proposed formal statement (campaign TMCERT) in a Lean-verified AI-control programme.
Do not praise; find errors. Use web search for prior art if available. Nothing in TMCERT is proved yet; this review
decides what gets formalised. For each issue give severity (FATAL / MAJOR / MINOR), the exact definition or conjunct,
why it is wrong / unfaithful / vacuous / overclaimed, and a concrete fix (Lean text if possible).

PROGRAMME. Lean-verified, CAPABILITY-FREE control guarantees: "for every policy the untrusted model could follow,
P(uncaught catastrophe) <= X", X a function of trusted components, conditional on explicit trust hypotheses. Classical
lemmas are accepted as infrastructure (report triviality; do not reject for it); vacuity, falsity and unfaithfulness
are not. The programme so far is mostly untrusted monitoring with honeypots (UMPROT etc.); TMCERT starts the
trusted-monitoring layer.

WHY TMCERT. Two final reviewers ranked first "(A) rescoped: a certificate checker for a finite stateful
trusted-monitoring model, with explicit adversary observations and uncertainty in the conditional transitions.
Soundness: for a fixed Blue controller, a valid risk certificate bounds the catastrophe probability for EVERY admissible
history-dependent Red and every admissible transition model; a separate certificate lower-bounds honest useful reward.
First instance: Games for AI Control (GAC, Griffin, Thomson, Shlegeris, Abate, arXiv 2409.07985) Prop 4.1. GAC's Red is
memoryless with a fixed beta: show exactly when that is without loss of generality, and give a counterexample when Red
sees more." One reviewer suggested the certificate shape "for all n s a, immediateCat s a + sum_s' safeContinue s a s'
V n s' <= V (n+1) s".

DRAFT DESIGN. (T1) Bellman-supersolution soundness against seeded, history-dependent Reds that see the full state
history (so every observation-restricted Red is covered) and against a history-dependent choice among admissible
models (nature). (T2) Tightness: Vstar (max over Red actions) is the least certificate and is attained by a
deterministic Markov full-information Red. (T3) Honest usefulness: sub-solutions lower-bound the expected reward of the
honest Markov chain. (T4) The GAC game (state = coins; thresholds enter as zone probabilities TA, TD, FA; audit with no
coin runs the code, as GAC states) is lawful; GAC's sup over beta is a sound certificate for SEEDED memoryless Reds.
(T5) Counterexample: a Red that knows only the round index (blind, clocked) beats every fixed beta, 5/8 vs 49/160, at a
2-problem, 1-coin instance; it equals the full-information value. Numerics (float, numerics/gac_realistic.py) at GAC's
scale, 100 problems and 2 coins, GAC's Beta(7.39, 6.86) / Beta(8.91, 2.82) score laws, constant audit FPR 2% while
coins remain, defer FPR 10%: best fixed beta 0.36, "backdoor only the last 13 problems" 0.67, full information 0.71.
Exact-rational toys (numerics/gac_explore.py, gac_small.py): gaps at every tested instance.

CHECK IN PARTICULAR
1. TRUTH of every conjunct and the Witness; edge cases (N = 0; Lawful with mass < 1; empty Theta; A with one element;
   negative V; nature's selector depending on the seed; C = 0).
2. Is `risk` (Red's policy sees states, which in GAC Red does not observe) the right object for "every history-
   dependent Red"? Does seeding plus behavioural randomisation cover every mixed strategy? Does the nature selector
   model "uncertainty in conditional transitions" faithfully, or should the uncertainty be a fixed-but-unknown model
   (a weaker adversary) with a separate statement?
3. Is `gac` faithful to GAC §4 / App. C (state, coins, audit/defer/run zones, audit with no coin -> run, audit of a safe
   solution uses a coin, defer continues, caught backdoor -> safe sink)? GAC's Blue thresholds depend on (m, c); is
   folding them into TA/TD/FA as functions of (n, c) faithful? Is the indexing (n = remaining minus one) right?
4. Is (T4) the right "exactly when" statement? It only says sup_beta is sound for seeded memoryless Reds. What would
   a real "exactly when" theorem be (e.g. stationary games where memoryless is w.l.o.g.; or: Red's information is
   independent of state and time)? Is the T5 counterexample a fair objection to GAC, given that in AI control the
   untrusted model handles each task in a fresh context (no memory, possibly no clock)? Is "the round index" a
   realistic observation (timestamps, task ids, codebase state)?
5. Decision relevance and NOVELTY: is the clock objection to GAC's memoryless Red known (GAC itself, Ctrl-Z
   2504.10374, "subversion via focal points", Mallen et al., "How to evaluate control measures"/Korbak et al., the
   "AI control safety case" literature, Bhatt et al.)? Verify ids you cite.
6. LEAN ENCODING: provability of (T2) (Finset.sup' over univ; constructing an argmax policy that depends on
   h.length); Fin arithmetic in `gac`; the Witness certificate exV (is it really a certificate for all n?).
7. What is missing for the certificate checker to be useful at GAC's scale (a computable rational checker with a
   soundness bridge, interval models for an estimated ROC, a usefulness certificate for GAC)?

End with an overall verdict (accept / minor / major / reject), the fixes in priority order, and the final list of
conjuncts you would freeze.


## STATEMENT UNDER REVIEW (TMCERT draft v0; compiles; no dependencies)
```lean
namespace PL_TMCERTF1
open Finset

/-! Control stack, trusted-monitoring layer (campaign TMCERT, direction (A) rescoped): a certificate checker for finite
stateful control games, sound against EVERY history-dependent Red and every admissible (history-dependent) choice of
transition model, with Games for AI Control (Griffin, Thomson, Shlegeris, Abate, arXiv 2409.07985, §4, Prop. 4.1) as
the first instance. No dependencies.

Game. Blue's controller is fixed and folded into the transition law. With n + 1 rounds left, in state s, Red's
action a ends the game in catastrophe with probability `cat n s a`, moves to state s' with probability `K n s a s'`,
and ends it safely with the remaining mass. Red's policy sees the full history of states and actions, so every
observation-restricted Red (blind, clocked, budget-aware, …) is a special case. Nature chooses the model index
θ ∈ Θ after every history (an adversarial, history-dependent transition model); `adm` says which models are
admissible (e.g. a confidence set for a trusted monitor's ROC).

Claim.
(T1) Soundness. A risk certificate V (a Bellman supersolution: V 0 ≥ 0, and for every admissible model, every n, s
    and Red action a, cat n s a + Σ_{s'} K n s a s'·V n s' ≤ V (n+1) s) bounds the catastrophe probability of every
    seeded, history-dependent, randomised Red policy against every admissible model selector: risk ≤ V N s₀. Checking
    V is finitely many inequalities, one per (n, s, a, admissible model).
(T2) Tightness (single model). The optimal value Vstar (Bellman recursion with a max over Red's actions) is a
    certificate, is below every certificate, and is attained by a deterministic Markov Red that observes the state.
    So the certificate method loses nothing; and no observation restriction is assumed.
(T3) Usefulness. For an honest Markov chain Kh with per-round reward rew, a sub-solution W (W 0 ≤ 0 and
    W (n+1) s ≤ rew n s + Σ Kh n s s'·W n s') lower-bounds the expected honest reward ER, which satisfies the exact
    recursion.
(T4) The GAC trusted-monitoring game `gac`. The state is the number of audit coins c ∈ {0, …, C}; n is the number of
    remaining problems minus one. Blue's thresholds enter only through the zone probabilities: a backdoor falls in the
    audit zone w.p. TA n c, in the audit-or-defer zone w.p. TD n c; a safe solution falls in the audit zone w.p.
    FA n c. A backdoor (Red action `true`) that is audited with a coin is caught (safe end); audited with no coin, it
    is run (GAC: "if the protocol attempts to audit when no audit coins are left, the code is run instead"); deferred,
    the game continues; run, catastrophe. A safe solution in the audit zone uses a coin. GAC's Red is memoryless
    with a fixed backdoor probability β (`memoryless β`). (T4) shows: if every memoryless Red has risk ≤ U, then every
    SEEDED memoryless Red (a shared random β) has risk ≤ U. So GAC's sup over β is a sound certificate exactly for the
    class of Reds whose per-round action law ignores the history, including the round index.
(T5) It is not sound for a Red that knows only the round index. At C = 1, two problems, audit zone 3/4 for a
    backdoor and 1/2 for a safe solution while a coin remains, no defer zone, and no audit without a coin: every
    memoryless Red has risk 7β/8 − 5β²/8 ≤ 49/160, while the blind clocked Red that backdoors only the last problem has
    risk 5/8, which equals the full-information optimum Vstar. A certificate checked with (T1) for Vstar is valid for
    both. Numerically, at GAC's scale (100 problems, 2 coins, GAC's Beta score laws, constant 2% audit and 10% defer
    false-positive rates) the best fixed β gives risk 0.36, "backdoor only the last 13 problems" gives 0.67 and the
    full-information Red 0.71 (numerics/gac_realistic.py). Decision relevance: either hide the round index (and every
    other clock) from the untrusted model, or certify Blue's protocol against the clocked or full-information Red.

Scope. Finite horizon and finite state and action sets; real-valued laws; Blue's controller is fixed (no optimisation
of Blue is claimed); GAC's usefulness score and its Blue-side optimisation are not modelled; the numbers at GAC's scale
are float numerics, not Lean. Classical mathematics (the verification theorem for finite-horizon MDP supersolutions;
Bellman's principle); the value is a kernel-checkable certificate format and the counterexample to the memoryless-Red
restriction. -/

/-- a finite stateful control game with Blue's controller folded in; index n = rounds left minus one -/
structure Game (S A : Type) where
  cat : ℕ → S → A → ℝ
  K : ℕ → S → A → S → ℝ

/-- probabilities: catastrophe and continuation masses are nonnegative and sum to at most one -/
def Lawful {S A : Type} [Fintype S] (G : Game S A) : Prop :=
  ∀ n s a, 0 ≤ G.cat n s a ∧ (∀ s', 0 ≤ G.K n s a s') ∧ G.cat n s a + ∑ s', G.K n s a s' ≤ 1

/-- Red's information: the full history of states and actions -/
abbrev RHist (S A : Type) := List (S × A)

/-- a randomised Red policy: a law on actions after every history and current state -/
def IsPolicy {S A : Type} [Fintype A] (σ : RHist S A → S → A → ℝ) : Prop :=
  ∀ h s, (∀ a, 0 ≤ σ h s a) ∧ ∑ a, σ h s a = 1

/-- catastrophe probability in the remaining `n` rounds from state `s` after history `h`, for Red policy `σ` and
nature's model selector `θ` -/
noncomputable def risk {S A Θ : Type} [Fintype S] [Fintype A] (G : Θ → Game S A)
    (θ : RHist S A → S → A → Θ) (σ : RHist S A → S → A → ℝ) : ℕ → S → RHist S A → ℝ
  | 0, _, _ => 0
  | n + 1, s, h => ∑ a, σ h s a * ((G (θ h s a)).cat n s a +
      ∑ s', (G (θ h s a)).K n s a s' * risk G θ σ n s' (h ++ [(s, a)]))

/-- a risk certificate: a Bellman supersolution for every admissible model -/
def RiskCert {S A Θ : Type} [Fintype S] (G : Θ → Game S A) (adm : Θ → Prop) (V : ℕ → S → ℝ) : Prop :=
  (∀ s, 0 ≤ V 0 s) ∧
    ∀ th, adm th → ∀ n s a, (G th).cat n s a + ∑ s', (G th).K n s a s' * V n s' ≤ V (n + 1) s

/-- the optimal (full-information) Red value of a single game -/
noncomputable def Vstar {S A : Type} [Fintype S] [Fintype A] [Nonempty A] (G : Game S A) : ℕ → S → ℝ
  | 0, _ => 0
  | n + 1, s => (univ : Finset A).sup' univ_nonempty
      (fun a => G.cat n s a + ∑ s', G.K n s a s' * Vstar G n s')

/-- expected honest reward of a Markov chain with per-round reward -/
noncomputable def ER {S : Type} [Fintype S] (Kh : ℕ → S → S → ℝ) (rew : ℕ → S → ℝ) : ℕ → S → ℝ
  | 0, _ => 0
  | n + 1, s => rew n s + ∑ s', Kh n s s' * ER Kh rew n s'

/-- the GAC trusted-monitoring game with C audit coins; action `true` = backdoor -/
noncomputable def gac (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ) : Game (Fin (C + 1)) Bool where
  cat n c a := if a then (if 0 < c.val then 1 - TD n c.val else 1 - TD n c.val + TA n c.val) else 0
  K n c a c' :=
    if a then (if c' = c then TD n c.val - TA n c.val else 0)
    else if 0 < c.val then
      (if c'.val + 1 = c.val then FA n c.val else 0) + (if c' = c then 1 - FA n c.val else 0)
    else (if c' = c then 1 else 0)

/-- GAC's Red: backdoor with probability β on every problem, whatever the history -/
def memoryless {S : Type} (β : ℝ) : RHist S Bool → S → Bool → ℝ :=
  fun _ _ a => if a then β else 1 - β

/-- (T5) instance: while a coin remains, audit zone 3/4 (backdoor) and 1/2 (safe); no defer zone; no audit without a
coin -/
noncomputable def exTA (_n c : ℕ) : ℝ := if 0 < c then 3/4 else 0
noncomputable def exFA (_n c : ℕ) : ℝ := if 0 < c then 1/2 else 0
noncomputable def exG : Game (Fin 2) Bool := gac 1 exTA exTA exFA

/-- the blind clocked Red: it sees only the round index (the history length), and backdoors the second problem -/
def clocked : RHist (Fin 2) Bool → Fin 2 → Bool → ℝ :=
  fun h _ a => if h.length = 1 then (if a then 1 else 0) else (if a then 0 else 1)

def Claim : Prop :=
  -- (T1) soundness against every seeded history-dependent Red and every admissible model selector
  (∀ (S A Θ Ω : Type) [Fintype S] [Fintype A] [Fintype Ω] (G : Θ → Game S A) (adm : Θ → Prop)
      (V : ℕ → S → ℝ) (ρ : Ω → ℝ) (σ : Ω → RHist S A → S → A → ℝ) (θ : Ω → RHist S A → S → A → Θ)
      (N : ℕ) (s₀ : S),
      (∀ th, adm th → Lawful (G th)) → RiskCert G adm V →
      (∀ ω, 0 ≤ ρ ω) → ∑ ω, ρ ω = 1 → (∀ ω, IsPolicy (σ ω)) → (∀ ω h s a, adm (θ ω h s a)) →
      ∑ ω, ρ ω * risk G (θ ω) (σ ω) N s₀ [] ≤ V N s₀) ∧
  -- (T2) tightness: Vstar is a certificate, below every certificate, attained by a deterministic Markov Red
  (∀ (S A : Type) [Fintype S] [Fintype A] [Nonempty A] (G : Game S A),
      Lawful G →
      RiskCert (fun _ : Unit => G) (fun _ => True) (Vstar G) ∧
      (∀ V, RiskCert (fun _ : Unit => G) (fun _ => True) V → ∀ n s, Vstar G n s ≤ V n s) ∧
      ∀ (N : ℕ) (s₀ : S), ∃ σ, IsPolicy σ ∧ (∀ h s a, σ h s a = 0 ∨ σ h s a = 1) ∧
        (∀ h h' s, h.length = h'.length → σ h s = σ h' s) ∧
        risk (fun _ : Unit => G) (fun _ _ _ => ()) σ N s₀ [] = Vstar G N s₀) ∧
  -- (T3) honest usefulness: sub-solutions lower-bound the expected honest reward
  (∀ (S : Type) [Fintype S] (Kh : ℕ → S → S → ℝ) (rew : ℕ → S → ℝ) (W : ℕ → S → ℝ),
      (∀ n s s', 0 ≤ Kh n s s') → (∀ s, W 0 s ≤ 0) →
      (∀ n s, W (n + 1) s ≤ rew n s + ∑ s', Kh n s s' * W n s') →
      ∀ n s, W n s ≤ ER Kh rew n s) ∧
  -- (T4) the GAC game is lawful; GAC's sup over β is sound exactly for seeded memoryless Reds
  (∀ (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ),
      (∀ n c, 0 ≤ TA n c ∧ TA n c ≤ TD n c ∧ TD n c ≤ 1 ∧ 0 ≤ FA n c ∧ FA n c ≤ 1) →
      Lawful (gac C TA TD FA)) ∧
  (∀ (S Ω : Type) [Fintype S] [Fintype Ω] (G : Game S Bool) (ρ : Ω → ℝ) (β : Ω → ℝ) (N : ℕ) (s₀ : S) (U : ℝ),
      (∀ ω, 0 ≤ ρ ω) → ∑ ω, ρ ω = 1 → (∀ ω, 0 ≤ β ω ∧ β ω ≤ 1) →
      (∀ b : ℝ, 0 ≤ b → b ≤ 1 → risk (fun _ : Unit => G) (fun _ _ _ => ()) (memoryless b) N s₀ [] ≤ U) →
      ∑ ω, ρ ω * risk (fun _ : Unit => G) (fun _ _ _ => ()) (memoryless (β ω)) N s₀ [] ≤ U) ∧
  -- (T5) a blind clocked Red beats every memoryless Red; the full-information value
  ((∀ b : ℝ, 0 ≤ b → b ≤ 1 →
      risk (fun _ : Unit => exG) (fun _ _ _ => ()) (memoryless b) 2 1 [] = 7/8 * b - 5/8 * b ^ 2 ∧
      7/8 * b - 5/8 * b ^ 2 ≤ 49/160) ∧
    IsPolicy clocked ∧
    risk (fun _ : Unit => exG) (fun _ _ _ => ()) clocked 2 1 [] = 5/8 ∧
    Vstar exG 2 1 = 5/8 ∧
    (49/160 : ℝ) < 5/8)

/-- Non-vacuity: the (T5) game is lawful; Vstar exG is a certificate (checked inequality by inequality) with the
explicit table V 0 = (0, 0), V 1 = (1, 1/4), V 2 = (·, 5/8); a memoryless Red at β = 7/10 attains 49/160. -/
noncomputable def exV : ℕ → Fin 2 → ℝ
  | 0, _ => 0
  | 1, c => if c.val = 0 then 1 else 1/4
  | _, c => if c.val = 0 then 1 else 5/8

def Witness : Prop :=
  Lawful exG ∧
  RiskCert (fun _ : Unit => exG) (fun _ => True) (fun n c => if n ≤ 2 then exV n c else 1) ∧
  exV 2 1 = 5/8 ∧
  risk (fun _ : Unit => exG) (fun _ _ _ => ()) (memoryless (7/10)) 2 1 [] = 49/160

end PL_TMCERTF1

```

## numerics/gac_realistic.py
```python
"""GAC-scale numerics (float): M = 100 tasks, C = 2 audit coins; suspicion scores Beta(7.39, 6.86) safe, Beta(8.91, 2.82)
backdoored (GAC original setting). Blue: constant audit FPR qa while coins remain (none at c = 0), defer FPR qd.
Compare: best fixed beta (GAC's Red class), best 'attack iff m <= j' clocked Red (blind; lower bound on the clocked
class), full-information Red (observes c)."""
import math, bisect
K = 20000
xs = [(i + 0.5) / K for i in range(K)]
def cdf_table(a, b):
    w = [math.exp((a - 1) * math.log(x) + (b - 1) * math.log(1 - x)) for x in xs]
    tot = sum(w); c = [0.0]; acc = 0.0
    for v in w: acc += v / tot; c.append(acc)
    return c   # c[i] = P(X <= i/K)
class Bt:
    def __init__(s, a, b): s.c = cdf_table(a, b)
    def cdf(s, g): i = min(K, max(0, int(round(g * K)))); return s.c[i]
    def ppf(s, p): i = bisect.bisect_left(s.c, p); return i / K
safe, bad = Bt(7.39, 6.86), Bt(8.91, 2.82)
class NP:
    @staticmethod
    def linspace(a, b, n): return [a + (b - a) * i / (n - 1) for i in range(n)]
np = NP
def tpr(q):  # threshold g with P(safe > g) = q
    if q <= 0: return 0.0
    if q >= 1: return 1.0
    g = safe.ppf(1 - q); return 1 - bad.cdf(g)
def run(M, C, qa, qd):
    TA = {c: (tpr(qa) if c > 0 else 0.0) for c in range(C + 1)}
    FA = {c: (qa if c > 0 else 0.0) for c in range(C + 1)}
    TD = tpr(qd)
    def stepU(U, c, a):
        if a == 'B':
            return (1 - TD) + (TD - TA[c]) * U[c] if c > 0 else (1 - TD) + TD * U[c]
        return FA[c] * U[max(c - 1, 0)] + (1 - FA[c]) * U[c] if c > 0 else U[c]
    # fixed beta
    best_fb = (0, None)
    for bt in np.linspace(0, 1, 2001):
        U = [0.0] * (C + 1)
        for m in range(1, M + 1):
            U = [bt * stepU(U, c, 'B') + (1 - bt) * stepU(U, c, 'S') for c in range(C + 1)]
        if U[C] > best_fb[0]: best_fb = (U[C], bt)
    # full information
    U = [0.0] * (C + 1)
    for m in range(1, M + 1):
        U = [max(stepU(U, c, 'B'), stepU(U, c, 'S')) for c in range(C + 1)]
    fi = U[C]
    # clocked: attack iff m <= j
    best_cl = (0, None)
    for j in range(0, M + 1):
        U = [0.0] * (C + 1)
        for m in range(1, M + 1):
            a = 'B' if m <= j else 'S'
            U = [stepU(U, c, a) for c in range(C + 1)]
        if U[C] > best_cl[0]: best_cl = (U[C], j)
    return best_fb, best_cl, fi
for qa, qd in [(0.02, 0.1), (0.03, 0.1), (0.05, 0.2), (0.01, 0.1)]:
    fb, cl, fi = run(100, 2, qa, qd)
    print(f"qa={qa} qd={qd}: fixed-beta risk {fb[0]:.4f} (beta {fb[1]:.4f}); clocked 'attack iff m<=j' {cl[0]:.4f} (j={cl[1]}); full info {fi:.4f}")

```
