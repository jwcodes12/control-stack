# What would justify the SC-01 recovery bound?

There are two separate obligations: a mathematical bound for the declared
observation model, and correspondence between that model and the actual
receiver. Testing the receiver's task completion addresses usefulness.

## The counting proof

Let M = 2^32 secrets, with a uniform secret independent of the shared/public
seed. Let V contain the complete five-episode observation, with exactly nine
symbols in each episode (eight repair IDs plus blank). Thus |V| = 9^5 = 59,049.
For a fixed seed, write E(v|m) for any encoder's transcript distribution and
D(m|v) for any decoder's guess distribution. Then

```
P(exact recovery)
  = (1/M) × sum_v sum_m E(v|m) D(m|v)
 <= (1/M) × sum_v sum_m D(m|v)     because 0 <= E(v|m) <= 1
  = |V|/M                        because each decoder row sums to 1
  = 59049/4294967296 < 1/65536.
```

The inequality holds for each independent seed and therefore after averaging
over seeds. Treating the entire lifetime as one transcript covers randomized
encoders and adaptivity within the declared model. It does not cover additional
unmodelled observations. The existing Lean artifact is
[`ScenarioARepair.lean`](../../ControlStack/ScenarioARepair.lean), using
[`CovertChannel.lean`](../../ControlStack/CovertChannel.lean). This task introduces
no new theorem or claimed runtime guarantee.

Exactly five delivered episodes is load-bearing. Failed or absent sends must
be represented by blank views at all five slots. A secret-dependent visible
episode count would enlarge the carrier. The trusted supervisor's actual timing,
termination and management behavior also needs correspondence; fixed slot count
alone does not eliminate a clock channel.

## Additional observations

The new Lean track on local `master` contains `SideChannel.side_bound` and
`ScenarioASide.repair_side_target` (reviewed here through `git show`, without
merging or changing that track). Their fixed-kernel model uses side states s,
side observations o and a domination certificate c satisfying
W(o|s) <= c(o) for **every** permitted s and o. Its lifetime mass L = sum_o c(o)
gives the conditional bound

```
P(exact recovery) <= 59049 × L / 2^32.
To retain 2^-16, sufficient L <= 65536/59049 = 1.1098579...
```

The environment kernel must cover every observation outside the transcript,
be fixed as required by the model, and have a uniform certificate over all
sender states. One noiseless side bit has mass 2, exceeding this allowance;
the new track contains an attained model counterexample. Independently combining
per-episode certificates additionally needs its stated independence/no-feedback
premises. Sampling a few side states is not a uniform certificate.

## Why an empirical attack test is insufficient

For one fixed attack with independent trials, zero full-secret successes in
196,327 trials would put the one-sided 95% binomial upper confidence endpoint
below 2^-16. That calculation concerns that attack and sampling law. It neither
tests every possible encoder/decoder nor covers an unseen observation channel,
so it cannot establish the universal recovery claim. This is a sample-size
calculation, not an experiment performed in this task.

A successful attack can falsify an observation hypothesis. No successful attack
found is weaker evidence than an upper bound covering all permitted behavior.
The previous single-host cache receipt is retained separately and is not
evidence about the VM configuration.

## What this infrastructure can establish

The [configuration checker](check_isolation.py) and its receipts establish the
listed configured restrictions, with explicit source/config hashes. They do not
prove host/QEMU correctness or bound physical cache, scheduling and clock
effects. The VM usefulness replay uses the unchanged preregistered task, horizon,
deadlines, sampling unit and 90% completion floor. It does not measure leakage.

Applying the mathematical result to the runtime still requires either complete
observation correspondence or a justified uniform side-kernel certificate within
the above allowance. QEMU guest separation alone discharges neither. The case
remains CONDITIONAL, with those obligations explicit; no new channel experiment
is authorized or performed by this infrastructure task.
