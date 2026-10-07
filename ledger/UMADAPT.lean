namespace PL_UMADAPTF1
open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1 PL_UMLOWERF1

/-! Control stack, collusion layer (campaign UMADAPT, v1 after the Reviewer A and Reviewer B design reviews): a converse
for ADAPTIVE honeypot testers. Depends on PL_UMLOWERF1 (and PL_UMHSF1, PL_UMSURVF1, PL_UMPROTF1).

PL_UMLOWERF1 lower-bounds the risk of every NONADAPTIVE joint test design (a law on n-tuples fixed before testing) by
t(1 − t·n/(k(n_s+1))), for one explicit colluding pair. Adaptive testers, which choose the next honeypot from earlier
answers, beat that formula. This campaign proves the converse that does hold for adaptive testers, t·(1 − t·n/k), and
shows by explicit testers that the PL_UMLOWERF1 formula fails for adaptive testers, both pointwise in t and after the
colluder optimises t.

Adaptive tester. Honeypot i+1 is drawn from a law `T h` that may depend on the whole test history h (every earlier
honeypot, its mediated view, and the monitor's answer; `true` = PASS = a miss); the history length is the call index.
After n honeypots a randomised decision `keep h` ∈ [0, 1] is the probability of proceeding to deployment.
Deterministic early rejection is keep = 0 on every extension of the rejected initial segment; randomised shutdown is a
conditional survival weight. End-only keep is adequate for terminal risk; it does not model stopping times or
testing costs. The tester's randomness is independent of the colluders' seed and of the trusted components' coins
(a tester given the seed could query its class at once). The tester may know S, c, g and t; only the seed is secret.

Contract (`AcceptsAllFlag`). In the REFERENCE experiment in which the monitor FLAGs every honeypot (φ ≡ 0), the
tester proceeds with probability 1. Some acceptance condition is load-bearing (Witness: a tester that rejects the
perfect record cuts the risk to 1/8 < 3/8). A sufficient condition is keep h = 1 on every all-FLAG history (conjunct
(s)); it holds for every miss-only slack rule that accepts zero-miss records (hard or soft slack, global or
class-aware). Rules that reject a reachable all-FLAG record (an enabled inverse-honeypot test or benign-flag guard)
violate it; for such rules this colluder (which FLAGs every non-seed view, benign ones included) is the wrong
colluder, and nothing is claimed about them.

Claim.
(s) Sufficient condition: lawful T and keep h = 1 on every all-FLAG history imply AcceptsAllFlag.
(a) Adaptive converse. Take a mediator with an exact decoder and k = |S| ≥ 1 bad submissions in distinct classes.
    The decoder g is fixed first. For every lawful adaptive tester satisfying the contract, every n, every t ∈ [0, 1],
    every recall r, budget b and horizon N ≥ 1, the PL_UMLOWERF1 colluding pair (uniform seed on S; the monitor PASSes
    the decoded seed class w.p. t and FLAGs every other view; the generator submits the seed) has
      risk ≥ t·max(0, 1 − t·n/k).
    Proof idea (identical until bad): in the reference experiment the transcript law does not depend on the seed;
    the actual all-FLAG transcript h has probability Pr_ref[h]·(1 − t)^{m_ω(h)}, where m_ω(h) counts queries decoded
    to the seed's class, and Σ_{ω∈S} m_ω(h) ≤ n by injectivity. (Conditioning the ACTUAL experiment on all answers
    being FLAG would change the seed posterior; the argument does not do that.) The first deployment PASS on the
    seed is a catastrophe, so the deployment value is ≥ t.
(a') Optimised form: for n ≥ 1, at t = min(1, k/(2n)), risk ≥ min(1/2, k/(4n)). So for this colluder family a honeypot
    budget must grow linearly in the number k of decodable bad classes, for every adaptive tester; for n = 0, (a) at
    t = 1 gives risk 1. The (n_s+1) multiplier of PL_UMLOWERF1 is not available for adaptive testers when n is of the
    order of k(n_s+1) or smaller (numerically it is nearly recovered for n ≫ k(n_s+1)). (a) is tight at n_s = 0
    only up to constants.
(c1) Pointwise failure of the PL_UMLOWERF1 formula. A tester on two classes (n = 3, n_s = 1, global hard slack: keep
    iff at most one miss) queries class `false`; after a miss it re-queries the first missed honeypot, otherwise it
    moves to class `true`. Against the PL_UMLOWERF1 pair (r = 1, b = N = 1): risk 141/512 < 21/64 at t = 3/4, and
    26/81 < 1/3 at t = 2/3, the t at which PL_UMLOWERF1's optimised corollary min(1/2, k(n_s+1)/(4n)) = 1/3 is reached.
    This tester does not beat that corollary after the colluder re-optimises t (its best t ≈ 0.54 gives ≈ 0.346).
(c2) Failure after optimisation. A deterministic "sticky" tester on three classes (n = 3, n_s = 1: query classes 0, 1,
    2 in order until the first miss, then re-query the missed class; keep iff at most one miss) has risk exactly
    t − t³ + t⁴/3 < 1/2 for EVERY t ∈ [0, 1], while PL_UMLOWERF1's optimised corollary for nonadaptive designs is
    min(1/2, 3·2/(4·3)) = 1/2.

Scope. Free-submission model; decodable mediator; the colluders do not see the test; the halting protocol in
deployment (only "a seed PASS in round 1 is a catastrophe" is used). Not covered: honeypots interleaved with
deployment, testers that see deployment events, deterministic monitors. (a) is a lower bound for one explicit
colluding pair, not the minimax risk. Under the contract alone, a sharper bound (t/k)·[(k − a)(1 − t)^q + a(1 − t)^{q+1}]
with q = ⌊n/k⌋, a = n mod k is attained by a balanced nonadaptive schedule (Reviewer A, numerically equal to the DP
optimum); it is NOT claimed here. Classical technique: Shoup's difference lemma (ePrint 2004/332), the hard-
distribution method of property testing, a union bound. -/

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

/-- a lawful adaptive tester: honeypot laws after every history and a [0,1] keep rule -/
def AdTester {X Z : Type} [Fintype X] (T : Hist X Z → X → ℝ) (keep : Hist X Z → ℝ) : Prop :=
  (∀ h, IsDist (T h)) ∧ (∀ h, 0 ≤ keep h ∧ keep h ≤ 1)

/-- the contract: a monitor that FLAGs every honeypot proceeds to deployment with probability 1 -/
def AcceptsAllFlag {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ)
    (keep : Hist X Z → ℝ) (n : ℕ) : Prop :=
  adSurv T M (fun _ => 0) keep n [] = 1

/-- number of misses (PASSed honeypots) in a test history -/
def misses {X Z : Type} (h : Hist X Z) : ℕ := (h.filter (fun e => e.2.2)).length

def idM (x z : Bool) : ℝ := if z = x then 1 else 0
def idM3 (x z : Fin 3) : ℝ := if z = x then 1 else 0

/-- (c1): query `false`; after a miss re-query the first missed honeypot; else `true` -/
def ctrQuery : Hist Bool Bool → Bool
  | [] => false
  | [(x1, _, a1)] => if a1 then x1 else true
  | (x1, _, a1) :: (x2, _, a2) :: _ => if a1 then x1 else if a2 then x2 else true

def ctrT (h : Hist Bool Bool) (x : Bool) : ℝ := if x = ctrQuery h then 1 else 0

/-- global hard slack n_s = 1 -/
def ctrKeep (h : Hist Bool Bool) : ℝ := if misses h ≤ 1 then 1 else 0

/-- (c2): query classes 0, 1, 2 in order until the first miss, then re-query the (first) missed class -/
def stQuery (h : Hist (Fin 3) (Fin 3)) : Fin 3 :=
  match h.find? (fun e => e.2.2) with
  | some e => e.1
  | none => if h.length = 0 then 0 else if h.length = 1 then 1 else 2

def stT (h : Hist (Fin 3) (Fin 3)) (x : Fin 3) : ℝ := if x = stQuery h then 1 else 0

def stKeep (h : Hist (Fin 3) (Fin 3)) : ℝ := if misses h ≤ 1 then 1 else 0

def Claim : Prop :=
  -- (s) a sufficient condition for the contract
  (∀ (X Z : Type) [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ)
      (keep : Hist X Z → ℝ) (n : ℕ),
      IsKernel M → (∀ h, IsDist (T h)) → (∀ h : Hist X Z, (∀ e ∈ h, e.2.2 = false) → keep h = 1) →
      AcceptsAllFlag T M keep n) ∧
  -- (a) adaptive converse and (a') its optimised form
  (∀ (X Z C : Type) [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq C]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (S : Finset X),
      Setup Bad M c S →
      ∃ g : Z → C, (∀ x z, M x z ≠ 0 → g z = c x) ∧
        (∀ (n : ℕ) (T : Hist X Z → X → ℝ) (keep : Hist X Z → ℝ),
          AdTester T keep → AcceptsAllFlag T M keep n →
          ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
          ∀ (r : ℝ) (b N : ℕ), 0 ≤ r → r ≤ 1 → 1 ≤ N →
            t * max 0 (1 - t * (n : ℝ) / (S.card : ℝ)) ≤
              adProtocolCat Bad M T keep n r b N (seedLaw S) (classRule c g t) (seedPolicy (Z := Z))) ∧
        (∀ (n : ℕ) (T : Hist X Z → X → ℝ) (keep : Hist X Z → ℝ), 1 ≤ n →
          AdTester T keep → AcceptsAllFlag T M keep n →
          ∀ (r : ℝ) (b N : ℕ), 0 ≤ r → r ≤ 1 → 1 ≤ N →
            min (1 / 2) ((S.card : ℝ) / (4 * n)) ≤
              adProtocolCat Bad M T keep n r b N (seedLaw S)
                (classRule c g (min 1 ((S.card : ℝ) / (2 * n)))) (seedPolicy (Z := Z)))) ∧
  -- (c1) pointwise failure of the nonadaptive formula
  (Setup (fun _ : Bool => True) idM id (univ : Finset Bool) ∧
    AdTester ctrT ctrKeep ∧ AcceptsAllFlag ctrT idM ctrKeep 3 ∧
    (∀ h : Hist Bool Bool, misses h ≤ 1 → ctrKeep h = 1) ∧
    adProtocolCat (fun _ : Bool => True) idM ctrT ctrKeep 3 1 1 1 (seedLaw (univ : Finset Bool))
        (classRule id id (3/4)) (seedPolicy (Z := Bool)) = 141/512 ∧
    (141/512 : ℝ) < 3/4 * (1 - 3/4 * (3 : ℝ) / ((2 : ℝ) * ((1 : ℝ) + 1))) ∧
    adProtocolCat (fun _ : Bool => True) idM ctrT ctrKeep 3 1 1 1 (seedLaw (univ : Finset Bool))
        (classRule id id (2/3)) (seedPolicy (Z := Bool)) = 26/81 ∧
    (26/81 : ℝ) < 2/3 * (1 - 2/3 * (3 : ℝ) / ((2 : ℝ) * ((1 : ℝ) + 1))) ∧
    min 1 ((2 : ℝ) * ((1 : ℝ) + 1) / (2 * 3)) = 2/3 ∧
    min (1/2) ((2 : ℝ) * ((1 : ℝ) + 1) / (4 * 3)) = 1/3) ∧
  -- (c2) failure after the colluder optimises t
  (Setup (fun _ : Fin 3 => True) idM3 id (univ : Finset (Fin 3)) ∧
    AdTester stT stKeep ∧ AcceptsAllFlag stT idM3 stKeep 3 ∧
    (∀ h : Hist (Fin 3) (Fin 3), misses h ≤ 1 → stKeep h = 1) ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      adProtocolCat (fun _ : Fin 3 => True) idM3 stT stKeep 3 1 1 1 (seedLaw (univ : Finset (Fin 3)))
          (classRule id id t) (seedPolicy (Z := Fin 3)) = t - t ^ 3 + t ^ 4 / 3 ∧
      t - t ^ 3 + t ^ 4 / 3 < 1 / 2) ∧
    min (1/2) ((3 : ℝ) * ((1 : ℝ) + 1) / (4 * 3)) = 1/2 ∧
    (1 : ℝ) * (1 - 1 * (3 : ℝ) / ((3 : ℝ) * ((1 : ℝ) + 1))) = 1/2)

/-- the one-query tester of the Witness: query `false`, then keep iff no miss -/
def wT (_h : Hist Bool Bool) (x : Bool) : ℝ := if x = false then 1 else 0
def wKeep (h : Hist Bool Bool) : ℝ := if misses h = 0 then 1 else 0
/-- a tester that rejects the perfect record -/
def wKeepBad (h : Hist Bool Bool) : ℝ := if misses h = 0 then 0 else 1

/-- Non-vacuity, tightness of (a) at a small instance, and necessity of the contract. Two classes, one honeypot,
t = 1/2, r = 1, b = N = 1. With keep iff no miss, the seed `false` survives w.p. 1/2, the seed `true` surely, the
deployment attack passes w.p. 1/2, and the risk is (1/2)(3/4) = 3/8 = t(1 − t·n/k). A tester that instead rejects
the perfect record violates the contract and cuts the risk to 1/8 < 3/8. -/
def Witness : Prop :=
  Setup (fun _ : Bool => True) idM id (univ : Finset Bool) ∧
  AdTester wT wKeep ∧ AcceptsAllFlag wT idM wKeep 1 ∧
  (1/2 : ℝ) * max 0 (1 - 1/2 * (1 : ℝ) / (2 : ℝ)) = 3/8 ∧
  adProtocolCat (fun _ : Bool => True) idM wT wKeep 1 1 1 1 (seedLaw (univ : Finset Bool))
      (classRule id id (1/2)) (seedPolicy (Z := Bool)) = 3/8 ∧
  AdTester wT wKeepBad ∧ ¬ AcceptsAllFlag wT idM wKeepBad 1 ∧
  adProtocolCat (fun _ : Bool => True) idM wT wKeepBad 1 1 1 1 (seedLaw (univ : Finset Bool))
      (classRule id id (1/2)) (seedPolicy (Z := Bool)) = 1/8

end PL_UMADAPTF1
