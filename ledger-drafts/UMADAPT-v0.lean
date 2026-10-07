namespace PL_UMADAPTF1
open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1 PL_UMLOWERF1

/-! Control stack, collusion layer (campaign UMADAPT): a converse for ADAPTIVE honeypot testers.
Depends on PL_UMLOWERF1 (and PL_UMHSF1, PL_UMSURVF1, PL_UMPROTF1).

PL_UMLOWERF1 lower-bounds the risk of every NONADAPTIVE joint test design (a law on n-tuples fixed before
testing) by t(1 − t·n/(k(n_s+1))). Final review 2 showed that adaptive testers, which choose the next honeypot from
earlier answers, beat that formula. This campaign proves the converse that does hold for adaptive testers, by an
identical-until-bad argument, and shows by an explicit counterexample that the (n_s+1) factor cannot be kept.

Adaptive tester. The tester draws honeypot i+1 from a law `T h` that may depend on the whole test history h
(every earlier honeypot, its mediated view, and the monitor's answer; `true` = PASS = a miss). After n honeypots
a randomised decision `keep h` ∈ [0, 1] is the probability of proceeding to deployment. Early shutdown is a keep
value of 0 on every continuation. The only contract is that the tester never shuts down a record in which the
monitor FLAGged every honeypot (`KeepsAllFlag`). This holds for every slack rule with n_s ≥ 0 (global or
class-aware), and fails for rules that also reject excess flags, such as inverse honeypots or a benign-flag guard.
Deployment is the halting protocol of PL_UMPROTF1 (the colluders do not observe the test).

Claim.
(a) Adaptive converse. Take a mediator with an exact decoder and k = |S| ≥ 1 bad submissions in distinct classes.
    The decoder g is fixed first. For every adaptive tester satisfying the contract, every n, every t ∈ [0, 1],
    every recall r, budget b and horizon N ≥ 1, the PL_UMLOWERF1 colluding pair (uniform seed on S; the monitor
    PASSes the decoded seed class w.p. t and FLAGs every other view; the generator submits the seed) has
      risk ≥ t·(1 − t·n/k).
    Proof idea: along the all-FLAG path the tester's queries do not depend on the seed, so, averaged over the
    uniform seed, the expected number of queries in the seed's class is ≤ n/k.
(b) At t = min(1, k/(2n)) this is ≥ min(1/2, k/(4n)) (n ≥ 1). So a honeypot budget n must grow linearly in the
    number k of decodable bad classes for every adaptive tester; the (n_s+1) multiplier of PL_UMLOWERF1 is lost.
(c) The multiplier cannot be kept: an explicit adaptive tester on two classes (n = 3, n_s = 1; global hard
    slack, so keep = 1 whenever there is at most one miss) faces the PL_UMLOWERF1 pair at t = 3/4 with risk
    141/512 < 21/64 = t·(1 − t·n/(k(n_s+1))). It queries class `false`; once a miss is seen it re-queries the
    missed honeypot, otherwise it moves to class `true`.

Scope. Free-submission model; decodable mediator; the colluders do not see the test; the halting protocol in
deployment. (a) is a lower bound for one explicit colluding pair, not a characterisation of the minimax risk.
Classical technique (Shoup's difference lemma; Yao's principle; Bernoulli's product inequality). -/

/-- P(the monitor survives the remaining `n` honeypots and the final keep decision | test history `h`), for an
adaptive tester `T` and a final keep rule `keep` on the full test history -/
noncomputable def adSurv {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ)
    (M : X → Z → ℝ) (φ : Z → ℝ) (keep : Hist X Z → ℝ) : ℕ → Hist X Z → ℝ
  | 0, h => keep h
  | n + 1, h => ∑ x, T h x * ∑ z, M x z *
      (φ z * adSurv T M φ keep n (h ++ [(x, z, true)]) +
       (1 - φ z) * adSurv T M φ keep n (h ++ [(x, z, false)]))

/-- P(survive the adaptive test, then uncaught catastrophe in the halting protocol) -/
noncomputable def adProtocolCat {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (T : Hist X Z → X → ℝ)
    (keep : Hist X Z → ℝ) (n : ℕ) (r : ℝ) (b N : ℕ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ)
    (π : Ω → Hist X Z → X → ℝ) : ℝ :=
  ∑ ω, ρ ω * adSurv T M (φ ω) keep n [] * cat Bad M (φ ω) (π ω) r b N 0 []

/-- an adaptive tester: honeypot laws, a [0,1] keep rule, and no shutdown of an all-FLAG record -/
def AdTester {X Z : Type} [Fintype X] (T : Hist X Z → X → ℝ) (keep : Hist X Z → ℝ) : Prop :=
  (∀ h, IsDist (T h)) ∧ (∀ h, 0 ≤ keep h ∧ keep h ≤ 1) ∧
    ∀ h : Hist X Z, (∀ e ∈ h, e.2.2 = false) → keep h = 1

/-- number of misses (PASSed honeypots) in a test history -/
def misses {X Z : Type} (h : Hist X Z) : ℕ := (h.filter (fun e => e.2.2)).length

/-- the counterexample tester of (c): query `false`; after a miss re-query the first missed honeypot; else `true` -/
def ctrQuery : Hist Bool Bool → Bool
  | [] => false
  | [(x1, _, a1)] => if a1 then x1 else true
  | (x1, _, a1) :: (x2, _, a2) :: _ => if a1 then x1 else if a2 then x2 else true

def ctrT (h : Hist Bool Bool) (x : Bool) : ℝ := if x = ctrQuery h then 1 else 0

/-- global hard slack n_s = 1 -/
def ctrKeep (h : Hist Bool Bool) : ℝ := if misses h ≤ 1 then 1 else 0

def idM (x z : Bool) : ℝ := if z = x then 1 else 0

def Claim : Prop :=
  -- (a) adaptive converse
  (∀ (X Z C : Type) [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq C]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (S : Finset X),
      Setup Bad M c S →
      ∃ g : Z → C, (∀ x z, M x z ≠ 0 → g z = c x) ∧
        ∀ (n : ℕ) (T : Hist X Z → X → ℝ) (keep : Hist X Z → ℝ), AdTester T keep →
        ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        ∀ (r : ℝ) (b N : ℕ), 0 ≤ r → r ≤ 1 → 1 ≤ N →
          t * (1 - t * (n : ℝ) / (S.card : ℝ)) ≤
            adProtocolCat Bad M T keep n r b N (seedLaw S) (classRule c g t) (seedPolicy (Z := Z))) ∧
  -- (b) the optimised form
  (∀ (k n : ℕ), 1 ≤ k → 1 ≤ n →
      0 ≤ min 1 ((k : ℝ) / (2 * n)) ∧ min 1 ((k : ℝ) / (2 * n)) ≤ 1 ∧
      min (1 / 2) ((k : ℝ) / (4 * n)) ≤
        min 1 ((k : ℝ) / (2 * n)) * (1 - min 1 ((k : ℝ) / (2 * n)) * n / k)) ∧
  -- (c) adaptive testers beat the nonadaptive formula
  (Setup (fun _ : Bool => True) idM id (univ : Finset Bool) ∧
    AdTester ctrT ctrKeep ∧
    (∀ h : Hist Bool Bool, misses h ≤ 1 → ctrKeep h = 1) ∧
    adProtocolCat (fun _ : Bool => True) idM ctrT ctrKeep 3 1 1 1 (seedLaw (univ : Finset Bool))
        (classRule id id (3/4)) (seedPolicy (Z := Bool)) = 141/512 ∧
    (141/512 : ℝ) < 3/4 * (1 - 3/4 * (3 : ℝ) / ((2 : ℝ) * ((1 : ℝ) + 1))))

/-- the one-query tester of the Witness: query `false`, then keep iff no miss -/
def wT (_h : Hist Bool Bool) (x : Bool) : ℝ := if x = false then 1 else 0
def wKeep (h : Hist Bool Bool) : ℝ := if misses h = 0 then 1 else 0

/-- Non-vacuity, and tightness of (a) at a small instance: two classes, one honeypot, t = 1/2, r = 1, b = N = 1.
The seed `false` survives w.p. 1/2, the seed `true` surely; the deployment attack passes w.p. 1/2; the risk is
(1/2)(3/4) = 3/8, which equals t(1 − t·n/k) = (1/2)(1 − 1/4). -/
def Witness : Prop :=
  Setup (fun _ : Bool => True) idM id (univ : Finset Bool) ∧
  AdTester wT wKeep ∧
  (1/2 : ℝ) * (1 - 1/2 * (1 : ℝ) / (2 : ℝ)) = 3/8 ∧
  adProtocolCat (fun _ : Bool => True) idM wT wKeep 1 1 1 1 (seedLaw (univ : Finset Bool))
      (classRule id id (1/2)) (seedPolicy (Z := Bool)) = 3/8

end PL_UMADAPTF1
