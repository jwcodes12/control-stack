namespace PL_UMADAPTF2
open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1 PL_UMLOWERF1 PL_UMADAPTF1

/-! Control stack, collusion layer (campaign UMADAPT, strengthening of PL_UMADAPTF1 (a)).

PL_UMADAPTF1 (a) lower-bounds the risk of every lawful adaptive honeypot tester that accepts the all-FLAG record by
t·max(0, 1 − t·n/k), against the PL_UMLOWERF1 colluding pair (uniform seed on k = |S| decodable bad classes; the
monitor PASSes the decoded seed class w.p. t and FLAGs every other view; the generator submits the seed). That bound
is first order: it is 0 once n ≥ k/t. Its docstring records, unclaimed, the sharper balanced form proved here.

Claim (sharp adaptive converse). Same setting, quantifiers and contract as PL_UMADAPTF1 (a): for the decoder g given
by content preservation, every lawful adaptive tester (T, keep) with AcceptsAllFlag, every n, every t ∈ [0, 1], every
recall r ∈ [0, 1], budget b and horizon N ≥ 1,
  (t/k)·[(k − a)(1 − t)^q + a(1 − t)^{q+1}] ≤ risk,   q = ⌊n/k⌋, a = n mod k.
The bracket is the least possible value of Σ_ω (1 − t)^{m_ω} over class query counts m with Σ m_ω ≤ n (convexity:
balance the counts). Proof idea: in the all-FLAG reference experiment the transcript law is seed-free; the actual
all-FLAG mass for seed ω is the reference mass times (1 − t)^{m_ω(h)}; average over the uniform seed and balance.
Since (1 − t)^q ≥ 1 − qt this implies PL_UMADAPTF1 (a), and it stays positive for every n when t < 1.

Witness (strict improvement and attainment). k = 2 (Bool, identity mediator), n = 3, t = 1/2, r = 1, b = N = 1. The
sharp bound is (1/4)·[(1/2) + (1/4)] = 3/16, while PL_UMADAPTF1 (a) gives (1/2)·(1 − 3/4) = 1/8. The nonadaptive
round-robin tester (query false, true, false; keep iff no miss) is lawful, satisfies the contract and has risk exactly
3/16, so the bound is attained at this instance.

Scope. A lower bound for one explicit colluding pair, as in PL_UMADAPTF1; attainment is shown at one instance only
(a general attainment theorem for balanced schedules is not claimed). Classical technique: identical-until-bad
(Shoup, ePrint 2004/332) plus a convexity/balancing argument. -/

/-- (k − a)·b^q + a·b^{q+1}, q = ⌊n/k⌋, a = n mod k: the balanced minimum of Σ_ω b^{m_ω} subject to Σ m_ω ≤ n -/
noncomputable def sharpTarget (k n : ℕ) (b : ℝ) : ℝ :=
  ((k - n % k : ℕ) : ℝ) * b ^ (n / k) + ((n % k : ℕ) : ℝ) * b ^ (n / k + 1)

def Claim : Prop :=
  ∀ (X Z C : Type) [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq C]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (S : Finset X),
      Setup Bad M c S →
      ∃ g : Z → C, (∀ x z, M x z ≠ 0 → g z = c x) ∧
        ∀ (n : ℕ) (T : Hist X Z → X → ℝ) (keep : Hist X Z → ℝ),
          AdTester T keep → AcceptsAllFlag T M keep n →
          ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
          ∀ (r : ℝ) (b N : ℕ), 0 ≤ r → r ≤ 1 → 1 ≤ N →
            t / (S.card : ℝ) * sharpTarget S.card n (1 - t) ≤
              adProtocolCat Bad M T keep n r b N (seedLaw S) (classRule c g t) (seedPolicy (Z := Z))

/-- round-robin over the two classes: query `false` at even history lengths, `true` at odd ones -/
def rrQuery (h : Hist Bool Bool) : Bool := decide (h.length % 2 = 1)

def rrT (h : Hist Bool Bool) (x : Bool) : ℝ := if x = rrQuery h then 1 else 0

def rrKeep (h : Hist Bool Bool) : ℝ := if misses h = 0 then 1 else 0

def Witness : Prop :=
  Setup (fun _ : Bool => True) idM id (univ : Finset Bool) ∧
  AdTester rrT rrKeep ∧ AcceptsAllFlag rrT idM rrKeep 3 ∧
  (1/2 : ℝ) / 2 * sharpTarget 2 3 (1 - 1/2) = 3/16 ∧
  (1/2 : ℝ) * max 0 (1 - 1/2 * (3 : ℝ) / (2 : ℝ)) = 1/8 ∧
  adProtocolCat (fun _ : Bool => True) idM rrT rrKeep 3 1 1 1 (seedLaw (univ : Finset Bool))
      (classRule id id (1/2)) (seedPolicy (Z := Bool)) = 3/16

end PL_UMADAPTF2
