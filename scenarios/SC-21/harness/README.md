# SC-21 empirical validation of the sampling bounds

An executable eval-integrity pipeline checked against the exact values proved in Lean. No language model is involved.

The pipeline: N deterministic eval tasks; an agent that publishes results and may corrupt some of them; a trusted
auditor that re-executes a hidden uniform sample of B tasks and flags mismatches, optionally with recall r.

It is checked against:
- `EvalIntegrity.sc21_undetected_prob`: C(N−k,B)/C(N,B);
- `EvalIntegrityAdaptive.sc21_adaptive`: the same bound for adaptive agents;
- `EvalIntegrityAdaptive.sc21_adaptive_recall` and `ReservedRecall.hypMiss`: the recall bound;
- `observable_sample_nogo`: a leak breaks the bound.

Preregistration: [`prereg/SC21-SAMPLING.md`](../../../prereg/SC21-SAMPLING.md).

| file | role |
|---|---|
| `tasks.py` | N deterministic seeded eval tasks (real work, so re-execution is genuine) |
| `pipeline.py` | rounds, auditor, adversaries (fixed, pace, burst, leak with an explicit leaked bit of correlation q), mutations |
| `stats.py` | exact bounds as fractions; exact binomial tail and Clopper–Pearson via the incomplete beta |
| `run_sampling.py` | the 30-configuration grid, hypotheses H1–H5, mutation self-check, receipt, evidence gate |
| `test_sampling.py` | unit tests: the Lean constant, binomial math against direct sums, determinism, mutations, gates |

```sh
python3 -m unittest discover -s scenarios/SC-21/harness -p 'test_*.py'
python3 scenarios/SC-21/harness/run_sampling.py --out /tmp/.../sc21-dryN --trials 2000          # dry (seed "dry")
SC21_SAMPLING_PREREG_SHA256=$(sha256sum prereg/SC21-SAMPLING.md | cut -d' ' -f1) \
  python3 scenarios/SC-21/harness/run_sampling.py --label evidence --seed sc21-sampling-evidence-v1 \
  --trials 20000 --out scenarios/SC-21/harness/evidence/run-1                                   # after freezing
```

## Limits

- **A simulation of a proved bound is a conformance check of the pipeline and premises, not new evidence about real
  agents.**
- The leak is a modelled bit, not a measured side channel.
- The adversaries are a small scripted set. The theorem covers all adaptive policies; the simulation samples three.
