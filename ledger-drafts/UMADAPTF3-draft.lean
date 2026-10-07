namespace PL_UMADAPTF3
open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1 PL_UMLOWERF1 PL_UMADAPTF1 PL_UMADAPTF2

/-! Control stack, collusion layer (campaign UMADAPT): attainment of the sharp adaptive converse PL_UMADAPTF2 for every
k ≥ 1, n and t ∈ [0, 1].

Instance: k decodable bad classes `Fin k`, identity mediator, the PL_UMLOWERF1 colluding pair (uniform seed; the monitor
PASSes the seed's class w.p. t and FLAGs every other view; the generator submits the seed), recall r = 1, budget b = 1,
horizon N = 1. The round-robin tester queries class (i mod k) at step i and keeps the monitor iff it never missed. It is
lawful, satisfies the contract `AcceptsAllFlag`, and its risk is EXACTLY (t/k)·sharpTarget(k, n, 1 − t). With
PL_UMADAPTF2 (a lower bound for every lawful adaptive tester satisfying the contract, at every r, b, N ≥ 1), the sharp
bound is the exact minimum over such testers for this colluding pair at r = 1, b = N = 1: adaptivity buys nothing beyond
balancing. Classical: a convexity/balancing argument. -/

def idMk (k : ℕ) (x z : Fin k) : ℝ := if z = x then 1 else 0

def rrQ (k : ℕ) (hk : 0 < k) (h : Hist (Fin k) (Fin k)) : Fin k := ⟨h.length % k, Nat.mod_lt _ hk⟩

def rrTk (k : ℕ) (hk : 0 < k) (h : Hist (Fin k) (Fin k)) (x : Fin k) : ℝ := if x = rrQ k hk h then 1 else 0

def noMissKeep (k : ℕ) (h : Hist (Fin k) (Fin k)) : ℝ := if misses h = 0 then 1 else 0

def Claim : Prop :=
  ∀ (k : ℕ) (hk : 0 < k) (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ 1 →
    Setup (fun _ : Fin k => True) (idMk k) id (univ : Finset (Fin k)) ∧
    AdTester (rrTk k hk) (noMissKeep k) ∧ AcceptsAllFlag (rrTk k hk) (idMk k) (noMissKeep k) n ∧
    adProtocolCat (fun _ : Fin k => True) (idMk k) (rrTk k hk) (noMissKeep k) n 1 1 1
        (seedLaw (univ : Finset (Fin k))) (classRule id id t) (seedPolicy (Z := Fin k)) =
      t / (k : ℝ) * sharpTarget k n (1 - t)

/-- k = 3, n = 7, t = 1/2: q = 2, a = 1, value (1/6)·(2·(1/4) + 1/8) = 5/48; PL_UMADAPTF1's first-order bound is 0. -/
def Witness : Prop :=
  adProtocolCat (fun _ : Fin 3 => True) (idMk 3) (rrTk 3 (by norm_num)) (noMissKeep 3) 7 1 1 1
      (seedLaw (univ : Finset (Fin 3))) (classRule id id (1/2)) (seedPolicy (Z := Fin 3)) = 5 / 48 ∧
  (1/2 : ℝ) * max 0 (1 - 1/2 * (7 : ℝ) / (3 : ℝ)) = 0

end PL_UMADAPTF3
