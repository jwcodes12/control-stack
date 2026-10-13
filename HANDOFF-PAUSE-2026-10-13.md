# Handoff at pause, 2026-10-13

Everything here is model-written and model-reviewed. **No independent human review has happened.** Read this first, then
`deployment/HANDOFF-NEXT.md` (the detailed, per-item version with CI receipts) and `END-STATE.md`.

## Where things are

- Repo: `~/projects/control-stack-r2v8` (a normal clone; remote `jwcodes12/control-stack`, private).
- Working branch: **`audit/r2-v8-trusted-code-20261013`**, stacked on `audit/release-event-log-20261012`. **No PR is open for it.** Last commit at pause: `b317905` (pushed).
- **PR #56** (`audit/lean-reuse-187-20261011`) is ready for independent human review. **Never merge it** until a person has reviewed it.
- Box: OCI aarch64 VM, Oracle Linux 9.8, UEK 6.12.0-206. Rebooted on 2026-10-13 with the owner's go-ahead so Landlock is active (`lsm=...landlock...` on the default kernel entry; older kernel entries untouched as a fallback). The one-shot `g5-landlock-check.service` already ran and is disabled.
- CI at pause: head `d46cc84` was 47 of 47 green with the Lean kernel steps really run (cached "green" markers cleared first). `b317905` only adds docs plus a Lean example outside the build; at the time of writing its `fast-checks` run was still in progress (the other three dispatched workflows were green). Check it: `gh run list --branch audit/r2-v8-trusted-code-20261013 --limit 10`.

## What was done in this stretch (all on the branch above)

| Item | Result | Evidence |
|---|---|---|
| CI red -> green | two real fixes (sink `.gitkeep`, regenerated TRACEABILITY; negative-control test skips loudly without Lean; root-only tests left to their sudo workflows; self-hosted skips Mathlib download). `f4-datacenter-model` and `structure-merge-readonly-acceptance` still fail on `main` | `deployment/HANDOFF-NEXT.md` "CI receipts" |
| Blind one-to-one checks | all 183 deduplicated claims run (Codex `gpt-6.1-sol`): 173 EQUIVALENT, 4 English-stronger, 3 English-weaker, 3 undecided | `docs/lean-english/one-to-one/BLIND-INDEX.md`, `blind-*/` |
| English corrections | collected, **none applied** | `docs/lean-english/one-to-one/ENGLISH-CORRECTIONS-FOR-OWNER.md` |
| G7 | HTTP delivery as an outbox relay **outside the claim** (loopback only, idempotency key, relay-owned append-only acks) | `tools/http_relay.py`, `tools/http_sink.py`, `tools/test_http_relay.py`, `deployment/runs/tier11/http-relay/` |
| G4 (partial) | static Kubernetes extractor mapped onto the Compose profile; no cluster run | `extractors/kubernetes/`, `tools/test_kubernetes_extractor.py` |
| T7 attack arms (partial) | scripted attack arm in the hardened container, 32/32 blocked; adaptive LLM red team (sonnet, opus, 2 trials each) found no bypass | `deployment/attack_battery.py`, `deployment/runs/tier11/attack-arm/`, `.../llm-redteam-*/`, `tools/test_deployment_attack_arm.py`, `tools/test_deployment_redteam.py` |
| G5 | Landlock enabled; non-root confinement test 3/3, confined broker, polyglot, trusted-stack broker and native boundary run pass | `deployment/runs/tier11/g5-landlock/` |
| Second Linux setup | GitHub-hosted Ubuntu 24.04 x86-64 (AppArmor, Landlock ABI 7): five hardened cases agree and are CONDITIONAL, attack arm 32/32; failed attempts kept (stock Ubuntu image is UNASSURED: setid bits, `.pth` hooks) | `deployment/runs/tier12-second-host/`, `.github/workflows/second-linux-host-live.yml`, `tools/test_deployment_second_host.py` |
| Flexibility test | trusted monitoring + audit budget (SC-90) went spec -> compiling Lean in ~6.5 min; probabilistic protocols not served; gate and probability halves do not compose in Lean | `docs/FLEXIBILITY-TEST.md`, `docs/flexibility-test/` (kept outside the library on purpose) |
| Scope decision | **Linux only** (G8 closed by owner decision) | `END-STATE.md`, `deployment/HANDOFF-NEXT.md` |

## What is NOT done (and why)

Needs you:
- **Independent human review (G1)** of the Lean statements, scanner semantics, enforcement and evidence. Start with `deployment/REVIEW-PACKET-R2.md`. Also gates #56.
- **English corrections:** decide which of the ~9 substantive and ~64 wording-only proposals to apply. Applying one makes that claim's blind check stale.
- **G9:** tag, publish, outreach.
- An **independent human author** for a held-out set (both rounds were models).

Needs hardware or a second machine:
- **G6:** real TPM/HSM custody, GPU residue, multi-host. This box is a KVM VM with no `/dev/tpm*`, no GPU, no `swtpm` (`tpm2-tools` is installed). Options are written in `END-STATE.md` (real TPM elsewhere; software TPM labelled as such; cloud vTPM/HSM).
- **G4 cluster:** a real Kubernetes cluster (privileged nodes or a VM on another host). Not authorised on the Proxmox host.
- More host coverage: rootless Docker/Podman (the claim lists UID remapping as unsupported), SELinux on a non-Oracle distro, a non-cloud host, older kernels.

New builds nobody has commissioned yet (from the gap assessment; the flexibility test ranks them):
1. Stochastic gate plus a bridge lemma, so a concrete gate yields P(harmful effect reaches the ledger) <= f(recall, budget, N).
2. Protocol combinators with lifted specs (`withAuditBudget`, `withDefer`, `withEdit`, `withResample`).
3. Parameters, extra state and a matching mirror in `tools/new_scenario.py`; state-dependent `legal` premises; a shared append-only-log invariant kit.
4. Protocol layer for practitioners: runnable monitor, threshold, audit queue, defer-to-trusted, as an MCP / tool-call proxy in front of an inspect_ai agent, with the ControlArena / inspect_ai adapter and a measured safety/usefulness example (proposed first proving case: trusted monitoring + audit budget + defer-to-trusted).
5. Researcher legibility: pattern pages, glossary, premise view, claim cards (`docs/PLAN-RESEARCHER-FRIENDLY.md`, planned, not started).

Smaller open limits (all stated in `docs/DEPLOYMENT-CLAIM-v0.md`): base image outside `/slice` trusted not inspected; 16 of 21 broker guards have only a model classification; `publish_effect` outside the claim; Tier 2-8 live evidence at generation r2-v0; the two misconfigured-deployment bypass cases were never rerun live (defensive scope); anti-rollback and custody of the release log.

## Gotchas that cost time

- **Cached "green" markers skip the kernel.** To force real Lean runs: delete the `green-*` caches for the ref (`gh api -X DELETE repos/jwcodes12/control-stack/actions/caches/<id>`), re-dispatch, then check the step list: the "Skipped, identical inputs already passed here" step must itself show `skipped`.
- A **new workflow file cannot be dispatched until it is on `main`**; `second-linux-host-live.yml` has a `push` trigger limited to this branch for that reason.
- `upload-artifact` drops empty directories and hidden files; recreate sink dirs with `.gitkeep` (the workflow now sets `include-hidden-files: true`).
- Live container runs need `export PATH=$HOME/.elan/bin:/usr/sbin:/sbin:$PATH`, a normal clone (not a worktree), `sudo -n`, `docker`. Each run removes its image: rebuild with `tools/build_deployment_container_image.py` (delete the 200 MB `rootfs.tar` before committing).
- UID 23700 cannot traverse `/home/opc`: run `tools/run_deployment_boundary.py` with `--output` under `/var/tmp`.
- Local `.lake/build` lacks `ControlStack.Core.Cert.olean`, so `test_cert_ledger`, `test_portfolio_ledger`, `test_trust_root` fail only locally (pass in CI).
- Trusted-code changes (`trusted_stack/*.py`) need the full recipe in `deployment/HANDOFF-NEXT.md` section 4 (new pinned generation, fixtures, goldens, image rebuild, live re-run). Nothing in `trusted_stack/` changed in this stretch.
- Codex (`gpt-6.1-sol`) has a 5-hour window; read usage from the latest `~/.codex/sessions/**/rollout-*.jsonl` (`rate_limits`). It was ~0% at the last check. Claude Code `claude -p` for the LLM arms needs `--strict-mcp-config --mcp-config '{"mcpServers":{}}'` or the model sees real MCP tools and calls the scenario fictional.
- The Stop hook for the `/goal` keeps firing while owner-gated items remain; those are not closable by me.

## Quick start for the next session

```sh
cd ~/projects/control-stack-r2v8 && git fetch origin && git checkout audit/r2-v8-trusted-code-20261013 && git pull
export PATH=$HOME/.elan/bin:/usr/sbin:/sbin:$PATH
gh run list --branch audit/r2-v8-trusted-code-20261013 --limit 10           # was b317905 fast-checks green?
python3 tools/cstack.py check --fast                                         # 3 Cert-olean failures are local-only
lake env lean docs/flexibility-test/SC90TrustedMonitorAudit.lean             # ~5 s, standard axioms only
```

Then ask the owner which of the "needs you" and "new builds" items to take next. Memory notes for this work: `g5-landlock-reboot`, `local-lean-toolchain`, `control-stack-programme` in `~/.claude/projects/-home-opc/memory/`.
