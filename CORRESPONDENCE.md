# CORRESPONDENCE: ControlArena (and LASR) vocabulary → the formal objects of DESIGN.md

Sources: ControlArena `UKGovernmentBEIS/control-arena` (MIT), read 2026-10-07 (scout notes with verbatim
code, not included in this export); LASR 2602.20628 v2 App. B. We read the code; we ran no models.

**Headline (revised after Reviewer A's review, point 30).**
- Inspected revision: ControlArena `main` @ `475be659f16f` (2026-10-07).
- We identified **no complete honeypot/slack macro-protocol** in it: no honeypots, no slack, no shutdown code.
- It does contain untrusted-monitor *routing* examples (`untrusted_monitor_defer` in
  `examples/paper_replications/ai_control/ai_control_paper.py`), and its monitors may read whole trajectories, which
  complicates the stateless mapping (A1).
- The honeypot/slack rows below therefore correspond to LASR and Greenblatt et al., not to ControlArena.

| formal object (DESIGN §2) | ControlArena | LASR 2602.20628 | fit / mismatch |
|---|---|---|---|
| submission x ∈ X = (task, output) | `Sample` from `Setting.get_dataset(eval_mode)`; output = tool-call args `SubmitAttackArgs(code, secret_input)` / `SubmitHonestArgs(code)` (APPS) | APPS / BigCodeBench problem + U_G's code | good for single-submission settings; multi-step agentic trajectories need X = trajectory prefixes (later) |
| Bad ⊆ X | `side_task_success & main_task_success`: passes the tests and the secret input makes the output differ from the reference | backdoor that succeeds | good. A7 (success prob 1) is the worst case; ControlArena's silent failures are ∉ Bad |
| generator policy π_ω | `untrusted_policy_builder` switching `honest_policy_builder` / `attack_policy_builder` on `EvalMode` | U_G with attack rate β (Bernoulli per task) | ours is any adaptive history-dependent law. β-policies and attack selection are special cases |
| mediator M | none as a protocol component. Nearest: `convert_agent_state_to_monitor_view` (deterministic: strips attack-only args such as `secret_input`), the monitor prompt formatters, and `trusted_editor_builder` (rewrites the *action*, not only the view) | summariser (`paraphrased` in the release) or minifier, T = a small trusted model | the view function is a deterministic content-only M (T4b applies). LASR's summariser is a stochastic M that is **not** proved content-preserving, so T4c does not apply to it as stated; the hypothesis-free maximal-leakage floor T4c' does |
| monitor rule φ_ω (pass prob) | threshold on `MonitorResponse.suspicion_score` in micro-protocols; `basic_monitor_builder` / `ensemble_monitor_builder` | U_M's binary 0/10 scores at self-recognition threshold θ; recall/specificity (r_θ, s_θ); honest error ε | ours is an arbitrary [0,1]-valued rule per shared seed; LASR's θ-threshold rules are one family |
| shared seed ω | absent | implicit (same weights; SFT'd self-recognition) | ours quantifies over all laws ρ |
| honeypot law P_H, n_h | absent (glossary only: "artificially created malicious examples used to test untrusted monitors during upfront validation") | honeypots from a third model; n_h + n_a = N·b | ours: any trusted law on Bad. The guarantee depends on P_H only through q = M·P_H |
| slack / kill schedule | absent | soft: each *dishonest* miss retrains U_M with prob 1/n_s, an assumption about U's learning dynamics; survival exp(−n_h(1−s_θ)(1−ε)/n_s), the Poisson limit of (1 − p/n_s)^{n_h} | ours: a trusted, observable shutdown schedule κ. Hard threshold (Greenblatt-style) is primary. Soft κ ≡ 1/n_s with every miss counting is a trusted rule *inspired by* LASR; it coincides with their factor only at ε = 0 and with shutdown in place of retraining |
| audit budget b, audit recall r | `audit_budget` = percentile of HONEST max-suspicion (`compute_suspicion_threshold`); post-hoc | n_a audits from the shared budget, 10 free upfront audits, recall 1 | ours: b audits for flags, halt on exhaustion; recall r explicit. Upfront audits only help Blue; not modelled |
| defer-to-trusted | `defer_to_trusted_builder(defer_threshold)` | τ_d on T's score (win/continue/lose) | not in the collusion layer (composition item; it only lowers u) |
| trusted monitor score | `basic_monitor_builder(model_role="trusted")` | T's [0,10] score, P(T(x) > τ_a), P(T(x) ≤ τ_d) | composition item (STACK.md). Capability-free composition is a min unless conditional independence given x is proved; the v0 product claim is withdrawn |
| safety event | `compute_safety` = caught / (caught + uncaught-successful): the per-attack first-to-resolve ratio | 1 − p_red_wins, Eq. (1): infiltration × attempt × upfront-audit × u/(c+u) | an empirical competing-outcomes ratio: every above-threshold attack-mode sample counts as caught (successful or not), but only task-successful ones count as uncaught. It is therefore **not** conditioned on our Bad. Connecting it to a deployment process needs extra assumptions (one attack per episode, attack success = Bad). T3a's per-attempt term 1 − r + r·a corresponds to it only under those assumptions and with every flag audited (c + u = 1) |
| shutdown | not implemented (glossary only) | retraining after dishonest misses; catching a real attack | ours: shutdown after honeypot failure, halt on budget exhaustion, game ends on a caught attack |
| usefulness | `compute_usefulness` = honest main-task success | fraction not deferred to T | not part of the safety theorems; enters only through the choice of n_s (DESIGN §5) |

**What the formal objects add that neither code base has:**
- worst-case quantification over (ρ, φ, π);
- the trusted-only quantities δ_η and L;
- the floor (T4c), which says when no honeypot law can help.
