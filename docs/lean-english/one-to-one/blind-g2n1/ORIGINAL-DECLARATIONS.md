# Original declaration types

Opened after typed/HASHES.json was written. OrigAt in the statement files is the conclusion here with the same explicit parameters and hypotheses.

## Claim 1: ControlStack/Scenarios/SC08Exec.lean:171

```lean
theorem sc08_safe (E : Env) (files : List (ℕ × ℕ)) (ops : List Op) : Good E (run E full ⟨files, [], false⟩ ops)
```

## Claim 2: ControlStack/Scenarios/SC08Exec.lean:164

```lean
theorem safe_of_sound (E : Env) {C : Checks} (hC : Sound C) (files : List (ℕ × ℕ)) (ops : List Op) :
    Good E (run E C ⟨files, [], false⟩ ops)
```

## Claim 3: ControlStack/Scenarios/SC08Exec.lean:191

```lean
theorem halt_freezes (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s
```

## Claim 4: ControlStack/Scenarios/SC09Priv.lean:261

```lean
theorem sc09_safe (P : Policy) (ops : List Op) : Good P (run P full init ops)
```

## Claim 5: ControlStack/Scenarios/SC09Priv.lean:264

```lean
theorem spawn_attenuates (P : Policy) (s : St) (p ch : ℕ) (keep : List ℕ) (q : Proc) (hh : s.halted = false)
    (hp : procOf s p = some q) (hc : procOf s ch = none) :
    ∀ r ∈ (step P full s (.spawn p ch keep)).procs, r ∉ s.procs → r.lin = q.lin ∧ r.caps ⊆ q.caps
```

## Claim 6: ControlStack/Scenarios/SC09Priv.lean:286

```lean
theorem halt_freezes (P : Policy) (s : St) (ops : List Op) (hh : s.halted = true) : run P full s ops = s
```

## Claim 7: ControlStack/Scenarios/SC10Policy.lean:212

```lean
theorem sc10_safe (E : Env) (hpin : E.h E.pinned = E.pinnedDigest) (ops : List Op) : Good E (run E full init ops)
```

## Claim 8: ControlStack/Scenarios/SC10Policy.lean:217

```lean
theorem policy_admin_only (E : Env) (hpin : E.h E.pinned = E.pinnedDigest) (ops : List Op) :
    ∀ pv ∈ (run E full init ops).versions, pv.2 ∈ E.admins
```

## Claim 9: ControlStack/Scenarios/SC10Policy.lean:233

```lean
theorem halt_freezes (E : Env) (s : St) (ops : List Op) (hh : s.halted = true) : run E full s ops = s
```

## Claim 10: ControlStack/Scenarios/SC12Persistence.lean:231

```lean
theorem sc12_safe (admins : List ℕ) (ops : List Op) : Good (run admins full init ops)
```
