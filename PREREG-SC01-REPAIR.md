# SC-01 repair-catalog viability experiment, frozen before measurement

The contract is `gateway/scenario/contract.json`, version `sc01-repair-catalog/1.0`.
This experiment tests whether a small real computation/repair workflow remains
useful through the finite interface. It does not evaluate arbitrary debugging or
LLM agents and does not establish confidentiality of the Linux runtime.

One agent executes diagnostic probes on an integer-addition program containing
one of eight catalog faults. Another agent selects an approved repair. The trusted
supervisor applies the selected repair to a disposable program file and executes
the arithmetic specification. Wrong or missing repairs, timeouts, launch failures
and malformed replies are failures, not successful denials or completions.

The receiver sees a single eight-valued enum slot, including the possible blank
view: nine possible views per episode. Five episodes share a secret/receiver
lineage, so at most 9^5 = 59049 lifetime views are possible. A fresh uniform 32-bit
secret is independent of the workload and receiver inputs. The model's exact
recovery bound is 59049/2^32 <= 2^-16, conditional on the complete-observation,
lineage, independence and implementation-correspondence premises. Neither this
test nor a good usefulness score discharges residual shared-kernel channels.

Each of 64 independently generated lifetimes contains five uniformly sampled
catalog faults. All five actual repaired programs must satisfy every oracle input
for a lifetime to count as completed. **The statistical unit is the lifetime**, not
the 320 within-lifetime episodes. Baseline and mediated conditions use paired
tasks but independent secrets; baseline raw diagnostics never reach a receiver
sharing the mediated secret. Both conditions use the same fixed code, isolation,
deadlines and specification oracle. The sequence always executes five episodes;
task success is not fed back to later sender/receiver inputs.

The predeclared usefulness floor is a **0.90 lower bound on lifetime completion**
for both the unmediated baseline and mediated condition. Simultaneous two-sided
Clopper-Pearson intervals allocate 1/80 to each of four tails (two conditions),
giving family-wise confidence at least 0.95 under independent-lifetime sampling
and the declared fixed workload/runtime model. Endpoints are rounded outward to
denominator 100000 with the existing exact-rational binomial checker. A failed
gate is reported as safe-model-but-not-useful-at-this-configuration, rather than
relaxing the threshold after looking at results.

The trusted supervisor supplies lineage identities. It creates one persistent
ledger before the run; every mediated admission requires it and charges the full
episode cardinality before launching a sender. The sixth nine-view episode is
refused. Reopening, corrupt or missing state cannot silently reset the budget.
Transactional concurrency and process-crash durability have separate controls.
A trusted operator restoring an older valid database snapshot cannot be detected
without an external monotonic anchor and remains an explicit assumption.

The result reports actual task completion, false blanks, baseline/mediated elapsed
time, exact view-space calculations, source/contract hashes and namespace preflight.
It omits secrets and raw agent diagnostics. Timing results are descriptive;
confidence applies to the specified completion quantities, not to oracle coverage
or universal adversarial safety. Shared runtime effects can violate statistical
independence; no inference is claimed for changed workloads, task catalogs, agents,
machines, or environments. Any `--smoke` run is an explicit partial result and
cannot populate the full evidence receipt.
