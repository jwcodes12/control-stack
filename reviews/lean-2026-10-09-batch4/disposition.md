# Disposition: Gemini 3.1 Pro review of EscrowBudget and MonitorEnsemble

| File | Finding | Disposition |
|---|---|---|
| EscrowBudget | Settlement reads the host's spend instantaneously (shared memory) when the host is reachable. | **Valid modelling simplification.** A message-passing v2 is in progress (`EscrowBudgetMsg`): hosts send settlement messages, and the coordinator settles only on what it has received, conservatively at the full allocation otherwise. |
| EscrowBudget | `crash` is a no-op, and a crashed host is still reachable. | **Valid.** In v2 a crash makes the host unreachable until restart, and its durable counter is readable only after it restarts. |
| EscrowBudget | `datacenter_example`'s 64 ticks is arithmetic. | **Agreed.** The header says the figure is arithmetic on top of `reclaim_frees`; the trace-level part is `reclaim_frees`/`reconcile_frees`. |
| EscrowBudget | Host clocks may lead time arbitrarily or jump backwards. | **Safety is unaffected,** because a leading clock only stops spending earlier. Realism is a fair point; v2 adds monotone host clocks. |
| MonitorEnsemble | `indepW` defines independence as a product law. | **This is the standard finite definition of a product distribution.** The premise is that the deployed monitors' joint miss law is this product (named, measurement). No change. |
| MonitorEnsemble | `ensemble_adaptive` takes a black-box kernel. | **Already closed** by `EnsembleKernel.lean` (`ensK_premises`, `ensK_adaptive`), which builds the kernel from the `mixture` law and derives the premise. |
| MonitorEnsemble | `ensemble_example` is arithmetic. | **Agreed;** it is a numeric instance. The trace-level statement is `ensK_adaptive`. |
| MonitorEnsemble | Missing [0,1] bounds on q, r, b. | **Partly.** `EnsembleKernel.Params` carries them. The algebraic lemmas in MonitorEnsemble hold for any reals where stated, and the bounds matter only for probabilistic readings. No change. |
