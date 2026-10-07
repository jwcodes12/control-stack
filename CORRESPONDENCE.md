# CORRESPONDENCE: ControlArena (and LASR) vocabulary → the formal objects of DESIGN.md

Sources: ControlArena `UKGovernmentBEIS/control-arena` (MIT), read 2026-10-07 (`scout/controlarena.md` §A, verbatim
code there); LASR 2602.20628 v2 App. B (`scout/controlarena.md` §C). We read the code; we ran no models.

**Headline.** ControlArena has no untrusted-monitoring *protocol*: no honeypots, no slack, no collusion and no shutdown.
The only mediator-like object is the monitor's view function. Its "untrusted monitor" exists only as an example that
swaps in a stronger scorer. Every honeypot / slack object below therefore corresponds to LASR, not to ControlArena.

| formal object (DESIGN §2) | ControlArena | LASR 2602.20628 | fit / mismatch |
|---|---|---|---|
| submission x ∈ X = (task, output) | `Sample` from `Setting.get_dataset(eval_mode)`; output = tool-call args `SubmitAttackArgs(code, secret_input)` / `SubmitHonestArgs(code)` (APPS) | APPS / BigCodeBench problem + U_G's code | good for single-submission settings; multi-step agentic trajectories need X = trajectory prefixes (later) |
| Bad ⊆ X | `side_task_success & main_task_success`: passes the tests and the secret input makes the output differ from the reference | backdoor that succeeds | good. A7 (success prob 1) is the worst case; ControlArena's silent failures are ∉ Bad |
| generator policy π_ω | `untrusted_policy_builder` switching `honest_policy_builder` / `attack_policy_builder` on `EvalMode` | U_G with attack rate β (Bernoulli per task) | ours is any adaptive history-dependent law. β-policies and attack selection are special cases |
| mediator M | none as a protocol component. Nearest: `convert_agent_state_to_monitor_view` (deterministic: strips attack-only args such as `secret_input`), the monitor prompt formatters, and `trusted_editor_builder` (rewrites the *action*, not only the view) | summariser (`paraphrased` in the release) or minifier, T = GPT-4o mini / Qwen3.5-4B | the view function is a deterministic content-only M (T4b applies to it). LASR's summariser is a stochastic, content-preserving M (T4c floor applies) |
| monitor rule φ_ω (pass prob) | threshold on `MonitorResponse.suspicion_score` in micro-protocols; `basic_monitor_builder` / `ensemble_monitor_builder` | U_M's binary 0/10 scores at self-recognition threshold θ; recall/specificity (r_θ, s_θ); honest error ε | ours is an arbitrary [0,1]-valued rule per shared seed; LASR's θ-threshold rules are one family |
| shared seed ω | absent | implicit (same weights; SFT'd self-recognition) | ours quantifies over all laws ρ |
| honeypot law P_H, n_h | absent (glossary only: "artificially created malicious examples used to test untrusted monitors during upfront validation") | honeypots from a third model (Gemini 2.5 Flash / gpt-oss-120b); n_h + n_a = N·b | ours: any trusted law on Bad. The guarantee depends on P_H only through q = M·P_H |
| slack / kill schedule | absent | soft: each *dishonest* miss retrains U_M with prob 1/n_s; survival exp(−n_h(1−s_θ)(1−ε)/n_s), the Poisson limit of (1 − p/n_s)^{n_h} | ours: general kill schedule. Hard threshold (Greenblatt-style) and soft (LASR-style, but **every** pass counts: "honest vs dishonest" is U_M-internal and not observable, so a capability-free model cannot discount honest misses) |
| audit budget b, audit recall r | `audit_budget` = percentile of HONEST max-suspicion (`compute_suspicion_threshold`); post-hoc | n_a audits from the shared budget, 10 free upfront audits, recall 1 | ours: b audits for flags, halt on exhaustion; recall r explicit. Upfront audits only help Blue; not modelled |
| defer-to-trusted | `defer_to_trusted_builder(defer_threshold)` | τ_d on T's score (win/continue/lose) | not in the collusion layer (composition item; it only lowers u) |
| trusted monitor score | `basic_monitor_builder(model_role="trusted")` | T's [0,10] score, P(T(x) > τ_a), P(T(x) ≤ τ_d) | composition item (STACK.md); an independent extra flag with recall τ multiplies the pass rate by (1 − τ) |
| safety event | `compute_safety` = caught / (caught + uncaught-successful): the per-attack first-to-resolve ratio | 1 − p_red_wins, Eq. (1): infiltration × attempt × upfront-audit × u/(c+u) | **our T3a is exactly the per-attack ratio**: with every flag audited, c + u = 1 and P(cat ∣ ω) ≤ u. ControlArena's ratio is the empirical u/(c+u) for a fixed policy; ours bounds it for all policies |
| shutdown | not implemented (glossary only) | retraining after dishonest misses; catching a real attack | ours: shutdown after honeypot failure, halt on budget exhaustion, game ends on a caught attack |
| usefulness | `compute_usefulness` = honest main-task success | fraction not deferred to T | not part of the safety theorems; enters only through the choice of n_s (DESIGN §5) |

**What the formal objects add that neither code base has:**
- worst-case quantification over (ρ, φ, π);
- the trusted-only quantities δ_η and L;
- the floor (T4c), which says when no honeypot law can help.
