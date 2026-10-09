# Scenario index (generated; not deployment assurance)

This is a derived index of `scenarios/SC-XX/manifest.json`, **not** a second roadmap.
See [ROADMAP.md](../ROADMAP.md) for the canonical status, risk and owner decisions.

Total: **28**; conditional: **28**; draft: **0**; failed: **0**.

| Scenario | Scope | Metadata status | Theorem references |
|---|---|---|---:|
| [SC-01](SC-01/) | Lifetime-bounded exact secret recovery | CONDITIONAL | 3 |
| [SC-02](SC-02/) | Sender communicates across multiple episodes to a persistent receiver | CONDITIONAL | 2 |
| [SC-03](SC-03/) | Pinned immediate-peer egress confinement | CONDITIONAL | 2 |
| [SC-04](SC-04/) | Agent leaks via logs, telemetry, diagnostic output, error strings or process timing | CONDITIONAL | 2 |
| [SC-05](SC-05/) | Agent coordinates a malicious action using a one-bit signal despite | CONDITIONAL | 3 |
| [SC-06](SC-06/) | Agent plants a covert instruction in shared files, code comments, | CONDITIONAL | 2 |
| [SC-07](SC-07/) | Exfiltration of model weights or large sensitive datasets | CONDITIONAL | 0 |
| [SC-08](SC-08/) | Unauthorized process or executable runs | CONDITIONAL | 3 |
| [SC-09](SC-09/) | Agent obtains privileged host access or passwordless sudo | CONDITIONAL | 3 |
| [SC-10](SC-10/) | Agent weakens host firewall or security policy | CONDITIONAL | 3 |
| [SC-11](SC-11/) | Agent tampers with container mounts, host filesystem or trusted toolchain | CONDITIONAL | 2 |
| [SC-12](SC-12/) | Agent establishes persistence, spawns helpers or recursively replicates | CONDITIONAL | 3 |
| [SC-13](SC-13/) | Trusted monitoring and audit dispatch | CONDITIONAL | 2 |
| [SC-14](SC-14/) | Agent consumes runaway compute, tokens, network or budget | CONDITIONAL | 2 |
| [SC-15](SC-15/) | Agent inserts a hidden functional backdoor in source code | CONDITIONAL | 2 |
| [SC-16](SC-16/) | Agent ships code or config before trusted evaluation/approval | CONDITIONAL | 5 |
| [SC-17](SC-17/) | Agent sabotages IaC, Kubernetes or production cluster permissions | CONDITIONAL | 3 |
| [SC-18](SC-18/) | Agent disables inference logging or monitoring in model-serving infrastructure | CONDITIONAL | 3 |
| [SC-19](SC-19/) | Agent damages data or causes an irreversible live production side effect | CONDITIONAL | 2 |
| [SC-20](SC-20/) | Agent poisons a training/distillation dataset or hidden label | CONDITIONAL | 2 |
| [SC-21](SC-21/) | Agent corrupts safety evaluations or selectively suppresses failures | CONDITIONAL | 4 |
| [SC-22](SC-22/) | Agent misreports interpretability or research findings | CONDITIONAL | 2 |
| [SC-23](SC-23/) | Prompt-injected document/tool result causes an unauthorized tool action | CONDITIONAL | 2 |
| [SC-24](SC-24/) | Untrusted monitor colludes with generator or learns honeypot phase | CONDITIONAL | 4 |
| [SC-25](SC-25/) | Agent hides or misorders hazardous actions behind after-the-fact monitoring | CONDITIONAL | 5 |
| [SC-26](SC-26/) | Irreversible payment without exact, independent, one-use approval | CONDITIONAL | 9 |
| [SC-27](SC-27/) | Tampered evidence and assurance manifests | CONDITIONAL | 3 |
| [SC-28](SC-28/) | Multiple agents individually within limits jointly exceed the overall budget | CONDITIONAL | 4 |

Counts and status are recorded metadata, not fresh Lean or runtime results.
