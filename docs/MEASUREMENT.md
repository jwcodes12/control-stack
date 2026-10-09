# Measured premises: from recorded evidence to certificate terms

Some premises in `ASSURANCE-LEDGER.md` are **measurements**, not facts about code: `honest_usefulness`,
`semantic_judgement`, `deterministic_reexecution`, `honeypot_indistinguishable`, `observation_complete` and
`statistical_independence`. Here is how a recorded rate becomes a term that a Lean certificate can use, and what it
still does not say.

## 1. The rule (`ControlStack/Core/Measured.lean`)

A measurement is itself random. A certificate that relies on it therefore holds jointly over the measurement and the
deployment:

- **Measured premise.** The good measurement event G holds except with probability ≤ δ over the measurement's own
  sampling.
- **Certificate on G.** On every good outcome, the deployment's bad event has probability ≤ b.
- **Conclusion** (`measured_prod`, packaged as `ProbCert.ofMeasured`). P(bad) ≤ b + δ over the product space.

The ledger then records the premise as `measuredWithConfidence <procedure> δ`, plus a separate correspondence
premise: *the procedure samples i.i.d. from the deployment's law, independently of the deployment.*

For a success rate, G is "the true rate p is at least the reported lower bound". The exact one-sided Clopper–Pearson
bound makes G fail with probability ≤ δ for every p:

    r_low(k, n, δ) = the largest r with P_r(S ≥ k) ≤ δ,   S ~ Bin(n, r)

The Lean results behind this:
- `cp_valid` covers any rule built this way.
- `cp_threshold` covers the preregistered form "report r₀ iff S ≥ s₀".
- `tail_200_190` is a worked instance: 190/200 caught gives r₀ = 9/10 at δ = 0.01.

## 2. The tool (`tools/measured.py`)

```sh
python3 tools/measured.py                      # table at δ = 0.05
python3 tools/measured.py --delta 0.01 --json  # machine-readable
python3 tools/measured.py --measurement-only   # only premises of kind `measurement`
python3 tools/measured.py --lean out.lean      # one cp_threshold instance per row
```

**What it reads.** Only recorded evidence, through a curated source table:
- `verdicts.json` usefulness hypotheses of the runtime harnesses (per each prereg's §4);
- the SC-26 `receipt.json` usefulness phases;
- the SC-26 LLM agent and approver receipts;
- the SC-22 replication trials;
- the SC-21 sampling raw counts;
- the SC-24 collusion receipts, once those runs have finished.

**Every row shows:**
- the premise and its ledger kind;
- whether the scenario is a ledger member of that premise;
- the good event and k/n;
- the point estimate and r_low at δ;
- the source path and its SHA-256;
- the **caveat**.

Failure counts are flipped so that every bound is a lower bound on a good rate. For example, 0/74 unauthorized
approvals becomes 74/74 correct rejections.

**How the number is computed.**
1. r_low is found by bisection on the regularized incomplete beta, reusing `scenarios/SC-21/harness/stats.py`.
2. It is rounded down to a 6-digit rational r₀.
3. P_{r₀}(S ≥ k) ≤ δ is then re-checked exactly in integer arithmetic.

So the reported r₀ is valid, not just approximately valid.

**The Lean snippet.** `--lean` emits theorems of the form

    theorem m.. (htail : tailP n k (r₀ : ℝ) ≤ (δ : ℝ)) (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) :
        ∑ x : Fin n → Bool, (if p < (if k ≤ cnt x then r₀ else 0) then wB p x else 0) ≤ δ :=
      cp_threshold n k r₀ δ … htail p hp

The tail inequality `htail` is a **hypothesis**, discharged by the tool's exact check, not by Lean. Proving it in
Lean, as `tail_200_190` does, is feasible only for small n. The snippet is skipped, with a message, if
`Measured.lean` or the names `tailP`, `cnt`, `wB` and `cp_threshold` are absent.

## 3. The per-history pitfall

The adaptive theorems (`ReservedRecall.adaptive_recall_bound` and friends) need recall ≥ r **on every history** the
attacker can steer into. A measurement estimates a **population** rate: the catch rate on items drawn like the
evidence's items. These are different quantities.

`Measured.population_not_per_history` gives the minimal counterexample. Recall 1 on 95% of histories and 0 on 5% has
population recall 0.95, yet an attacker who reaches the 5% stratum always escapes. That is why
`measured_recall_example` carries an explicit premise `homogeneous`: per-history recall ≥ the measured population
rate.

To use a measured rate soundly in a per-history theorem, do one of two things:

1. **Measure each stratum separately** (by attack type, task family, history class) and use the minimum. The union of
   the stratum failures costs Σ δ_s (`strata_union`).
2. **Keep `homogeneous` as a stated premise**, with its own evidence or argument, in the certificate's premise list.
   Do not fold it into the measurement.

## 4. Reading the caveat column

| caveat | meaning |
|---|---|
| scripted repetition | n counts repetitions of a deterministic scripted workload. The bound is nominal: the reps are not independent draws from a task population, and 5/5 only gives r_low ≈ 0.55 at δ = 0.05. |
| toy task; one model | An LLM rate on a preregistered toy task set, one model, CLI-default sampling. It does not transfer to other tasks or models. |
| adaptive red team | Red-team requests are chosen adaptively, so they are not i.i.d. The binomial bound describes these requests, not attackers in general. |
| simulated / one code path | Trials share one implementation, so a systematic bug would fail every trial at once. Large n bounds sampling noise, not design error. |
| detector-restricted | Signal removal is measured only through the stated detectors and fixed families. It says nothing about adaptive encodings (SC-24 V2 §7). |
| single host | One machine, one kernel, one load profile. |
| population, not per-history | See §3. |

**Clustering.** Several rows pool items that share structure: SC-24 V2 items share a base solution, and SC-22 trials
share a protocol run. The binomial treats them as independent. Prefer the conservative companion statistics in the
corresponding prereg when they exist.

## 5. What this does not do

- It does not run anything, call any model, or change the ledger. It only reads evidence and computes bounds.
- It does not decide which premise a measurement discharges. The mapping is the curated source table in
  `measured.py`, marked with `member = yes/no` against the ledger. A `no` row is reported, not counted toward that
  premise.
- A bound at δ is per row. Using several rows in one certificate costs the sum of their δs.
