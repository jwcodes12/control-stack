/-
Negative result: a sampled (population-average) trusted-monitor certificate does not yield the per-submission miss bound
τ that `ComposeGame.composedEndToEnd` needs against a content-adaptive Red.

Bad submissions `Fin 2`. The trusted monitor always catches submission 0 and always misses submission 1 (a blind spot).
The evaluated attack population puts mass 999/1000 on 0, so its average trusted miss is τ̄ = 1/1000 and the
population-model bound (`ComposeAvg.composedPop_end`) is tiny. But a Red that chooses CONTENT submits 1 every time; with
no honeypots and an always-PASS untrusted monitor (L = 1, n_h = n_s = 0), it causes catastrophe with probability 1,
equal to the untrusted-only worst case: the trusted monitor contributes nothing. Data about the population cannot
exclude this; a coverage assumption about Red's reachable attacks is required.
-/
import ControlStack.ComposeAvg

open OracleComp

namespace ControlStack.ComposeBlindSpot
open ControlStack.Refine ControlStack.Compose ControlStack.ComposeAvg

/-- trusted PASS: catch submission 0, miss submission 1 -/
def blindT (x : Fin 2) : ProbComp Bool := pure (decide (x = 1))

/-- the evaluated attack population: 999/1000 on submission 0 -/
def popA : ProbComp (Fin 2) := (fun k : Fin 1000 => if k.val = 0 then (1 : Fin 2) else 0) <$> $[0..999]

theorem pop_avg_miss : Pr[= true | popA >>= blindT] = 1 / 1000 := by
  have e : (popA >>= blindT) = (fun k : Fin 1000 => decide (k.val = 0)) <$> $[0..999] := by
    simp only [popA, blindT, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
    congr 1; funext k
    by_cases hk : k.val = 0
    · have : k = 0 := Fin.ext hk
      simp [hk, this]
    · have : k ≠ 0 := fun h => hk (by simp [h])
      simp [hk, this]
  rw [e, probOutput_map_eq_sum_fintype_ite]
  simp
  norm_num

/-- content-adaptive Red always submits the blind-spot attack 1: catastrophe with probability 1 -/
theorem blind_spot_risk :
    Pr[= true | composedGame (fun _ : Fin 2 => True) (pure ()) (pure (1 : Fin 2)) (fun x => pure x) blindT
      (fun _ _ => pure true) (fun _ _ => pure (1 : Fin 2)) (fun _ _ _ => pure true) 0 0 1 1] = 1 := by
  simp [composedGame, Bridge.honeypotPasses, deploy, jointView, jointPass, blindT]

#print axioms pop_avg_miss
#print axioms blind_spot_risk

end ControlStack.ComposeBlindSpot
