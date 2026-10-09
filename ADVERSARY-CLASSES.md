# Adversary classes and valid composition

These labels classify **quantification in a specific theorem**, not the capabilities of a real agent.
A theorem that names a class is valid only under its other premises. The default is
UNKNOWN; classification must be explicitly reviewed before using two theorems together.

| ID | Meaning | Common excluded ability / risk |
|---|---|---|
| NON_ADAPTIVE | Strategy fixed before monitor/testing feedback | Test feedback may change later choices |
| ADAPTIVE_FEEDBACK | Strategy chooses next move from history of observable feedback | Unmodeled side observations may change the history |
| SHARED_SEED | Parties may coordinate with a correlated initial seed | Does not entail global lifetime accounting |
| SIDE_OBSERVING | Receiver can use a specified side-observation kernel in addition to mediated outputs | Kernel domination/observation completeness remain premises |
| CONTENT_ADAPTIVE | Attacker chooses bad content in response to the monitoring protocol/history | Population-average detection rates are not worst-case |
| TRACE_ARBITRARY | Any finite sequence of actions admitted by the specified transition system | Real privileged actions may bypass the modeled transition system |
| UNKNOWN | Not yet classified / formally audited | **No composition claim permitted** |

Do not infer an implication solely from labels: a shared-seed nonadaptive model and
an adaptive trace model may refer to different observables and different random
coins. Record strategy space, quantifier order, side information, kernel laws,
feedback schedule, authority boundary and horizon in the theorem's premises.
Example: a population-average miss rate cannot silently become a worst-case
per-history bound; an egress immediate-peer invariant does not bound the bytes
delivered through allowed CONNECT tunnels.

A composed result needs an explicit coupling/refinement lemma showing that the
same concrete traces map into both theorem models, including shared state,
concurrency, crash/restart and cumulative resource budgets.
