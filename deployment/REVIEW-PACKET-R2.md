# Review packet — scoped R2 deployment assurance case (T8.6)

For an independent reviewer (gate G1, which has not happened). Everything here was built
and self-reviewed by AI coding agents (Sol = GPT via Codex for Tiers 1–7, Claude Opus 5.5 for
Tier 8) under one owner. Please treat every "PASS" as a claim to check, not a result.

Start with: `docs/DEPLOYMENT-CLAIM-v0.md` (claim), `docs/DEPLOYMENT-QUICKSTART.md`
(how to run), `deployment/RELEASE-GATES.md` (gate table), then this file.

## 1. Statements to check

**English claim.** For the local-file receiver deployment class (two agent UIDs, separate
reviewer/approver, broker+receiver owner, one shared budget), if `cstack verify --lean`
returns CONDITIONAL on a freshly scanned deployment, then every sink file is attributable
to a reviewed, exactly approved, once-consumed release within the shared budget, and no
agent or alternate deputy has bypass authority — **provided** faithful extraction and
protocol refinement hold (section 2).

**Lean statements** (toolchain `leanprover/lean4:v4.34.0`, standard axioms only):

| Name | File | Check that… |
|---|---|---|
| `Accepted` (decidable) + per-IR `facts_checked` | `ControlStack/Deployment/Contracts.lean`, `tools/check_deployment_lean.py` | the projection from the JSON IR loses nothing the Python verifier uses; `decide` is over the real IR, not a simplified copy |
| `runtime_exclusive` | Contracts.lean:128 | exclusive sink authority is derived from IR facts, not assumed as CompleteMediation |
| `protocol_safe`, `one_use` | Contracts.lean:151,155 | reuse of SC26 gate/one-use/budget contracts is faithful to the deployed broker's operations |
| `deployment_safe` | Contracts.lean:192 | the residual hypotheses are exactly `ExtractionFaithful` and `ProtocolRefinement` and are not vacuous |
| `deployment_broker_safe` | `ControlStack/Deployment/R2Contracts.lean:101` | `BrokerProtocolRefinement` (reverse-admission-order publication sublist) is a fair abstraction of `trusted_stack/controller.py` + `outbox_receiver.py` |
| `accepted_no_avoided_path` | R2Contracts.lean:20 | the closure certificate really covers transitive reachability |
| `accepted_path_safety_monotone` | R2Contracts.lean:38 | (safety-only monotonicity; full `Accepted` monotonicity is **false** — see failures) |
| `runtime_trace`, `final_safe`, `final_counts`, omission examples | `ControlStack/Deployment/TranscriptReplay.lean` (generated) | the recorded Tier 2 clean transcript really is a chain of `TrustedBroker.Step`s (check the numeric roles and the 21-conjunct `Allowed` obligations), and that the omission examples say what `deployment/TIER4-TRANSCRIPT.md` says |
| witnesses / falsifying controls | `ControlStack/Deployment/Witnesses.lean`, `deployment/contract-witnesses.json` | non-vacuity: useful deployments are accepted and disabling a check breaks a theorem |

**Empirical statements:** 51 fixtures (the frozen legacy corpus of 44 — 1 clean CONDITIONAL, 43
UNASSURED with the bypass named — plus 7 of the hardened profile: 1 clean, 6 UNASSURED); Python/Lean differential 26 fixtures + 250 seeded mutations, zero differences;
520 seeded strict additions, zero false improvements; 7 Tier 2 real-container cases;
2 Tier 5 repaired configurations; 25-case sealed held-out corpus; 9 archived episodes; and, on the
hardened profile and the hardened source generation (T9), 5 live non-bypass cases plus the 2
repaired configurations.

## 2. Remaining premises (unproved)

1. **Faithful extraction** — the finite IR exhausts actual effective authority: mounts and
   aliases, processes, UID bindings, inherited descriptors, image/source correspondence.
2. **Protocol refinement** — the implementation executes the model transitions with
   authentic caller binding, exact hashes, unit costs, trusted clock, no rollback, and
   matching durable publication (`sinkEffects = model.bank` in the SC26 form; the weaker
   sublist form in `BrokerProtocolRefinement`).
3. **TCB** (quickstart list): kernel, Docker daemon and its reports, SQLite, Python, the
   trusted broker/receiver code, the collector/scanner/verifier/serializer, Lean kernel.
4. **Docker inventory is truthful.** Captures are hashed but unauthenticated.

## 3. Scanner gaps

Full table: `docs/DEPLOYMENT-EXTRACTOR-GAPS.md`. Not detected (only their *reported* forms
produce UNKNOWN/DRIFT): covert host symlink/hardlink changes, inherited descriptors,
`docker exec` injection, runtime code tampering, daemon UID remapping, storage rollback,
changes after capture, a malicious daemon. Over-rejection is deliberate for many Compose
features (ports, depends_on, read_only, tmpfs, …) — they become UNKNOWN.

## 4. Every recorded failure and dead end

| Where | What happened | Disposition / evidence |
|---|---|---|
| PR #45 review | Agent mounts of `docker.sock` and trusted source returned **false CONDITIONAL** (extractor only flagged sink/DB overlaps) | Fixed T1: allowlist binds, explicit `escape` edges, fixtures `runtime-socket-mount`, `trusted-source-mount`, `unlisted-host-mount` |
| PR #45 review | `verify` without `--lean` could return CONDITIONAL; Lean `Accepted` weaker than Python | Fixed T1.6/T1.7: skipped Lean ⇒ UNASSURED; strengthened `Accepted`, differential |
| T1 CI 64498eb | source-fidelity guard matched new `/evidence/` logs | Logs relocated to `deployment/runs`; `deployment/runs/tier1/ci-source-fidelity-failure*` |
| T2.1 | first image build argument error | corrected; `deployment/runs/tier2/build` |
| T2 CI | pre-existing SC-01 cache probe failed to execute (unrelated); rerun passed | `deployment/runs/tier2/ci-viability-attempt*` |
| T3 | first replay after principal-policy guard: UID-collision IR differed | retained; recollected |
| **T4.2** | requested full-`Accepted` monotonicity is **false** — 3 kernel-checked countermodels (removing DB writers breaks usefulness) | BLOCKED; `deployment/TIER4-MONOTONICITY.md`; safety-only monotonicity proved instead |
| **T4.4** | concrete Lean replay of the Tier 2 clean transcript failed 3 compile attempts (unsolved `s0.halted = false`, lease/cap guards) | Cause was `by try simp only [R]; all_goals decide` parsing as `try (…; …)`. Finished in Tier 9: `deployment/TIER4-TRANSCRIPT.md`; the failed attempts stay in `deployment/runs/tier4/transcript-prototype-attempt*.txt` |
| T5 CI f1fbf63 | planner inferred an absolute archived path missing on CI | fixed with hash-pinned source-label normalization; raw failure kept |
| T5 fresh checkout | remediated archive replay failed on relocated source labels | same normalization in checker; both results kept |
| T5.1 (Sol session) | OpenAI `cyber_policy` flag ended a turn; owner has no cyber-permissive access | scope changed to defensive-only; new attack policies and four-arm evaluation GATED |
| T6.1 | blinded author failed to start twice (read-only Codex state; bwrap symlink) | third attempt succeeded; raw errors kept |
| **T6.2** | raw held-out score: 25/25 UNKNOWN, 5/5 supported rejected (interface omitted source-hash fields); after hypothesis instantiation 2/5 supported rejected (mount-order bug) | order fix made **after** seeing held-out results — see section 5 |
| T7 CI 455feb3 | shallow checkout changed `eval.created` in the Inspect export | full-history checkout; guard rejects shallow prereg addition; fixed at 575aad1 |
| Sol session end | OpenAI usage limit reached mid-Tier 7 push | Claude pushed 575aad1 and continued Tier 8 |
| T8 | `cstack demo` first call: `ModuleNotFoundError: deployment` | fixed via `_import`; not in archived runs |
| T9.6 attempt 1 | hardened live `clean` case: fresh scan UNASSURED, DRIFT on broker/receiver/reviewer/approver. `declared_hardening` said `cap_drop: None` for a service with no `cap_drop`; the daemon reports `[]`. The fixture builder used the same function on both sides, so no unit test saw it | fixed (absent = `[]`), fixtures/goldens regenerated; raw run kept in `deployment/runs/tier9/attempt1-*`. Lesson: only the real daemon disagreed with the shared helper |
| T9 | `tools/run_deployment_boundary.py` and `tools/test_confined_effect_broker.py` need Landlock (host has none): not re-run here | unchanged skip; the CI `linux-boundary` job covers them where available |
| T9.3 | `UID 0` was still accepted by `Principals` (review L5, second half) | fixed in Tier 10: refused; the root-run broker tests use a disposable non-root admin UID |
| T10 live attempt 1 | the hardened `clean` case came back UNASSURED: the new whole-`/slice` check found `README.md`/`STATUS.md` in the image's import tree | scanner correct, image builder fixed to ship only reference files; raw attempt in `deployment/runs/tier10/gen-r2-v6/attempt1-*` |
| **T10 held-out round 2** | pre-fix: **1 false CONDITIONAL / 26 negatives** (`agent-role-impersonation`: `SLICE_ROLE=broker` on an agent; the fresh scan already marked it UNKNOWN, `collect` did not read the value) | extractor checks `SLICE_ROLE`/`PYTHONPATH` under fresh rules; post-fix figures are contaminated; pre-fix result in `deployment/runs/tier10/heldout/before-fix-*.json` |

## 5. Weak points a reviewer should weigh (self-identified)

- **English versions of the Lean claims (Tier 10).** `docs/LEAN-CLAIMS-IN-PLAIN-ENGLISH.md` states 187 headline Lean claims
  in plain English (blocks in `docs/lean-english/part-g*.md`, written by Sonnet from the Lean source). They are *claims under test*,
  not results: a one-to-one check (blind back-translation to Lean plus a gate-checked equivalence proof, by Sol with the
  proofledger gate; `docs/lean-english/ONE-TO-ONE.md`) was in progress when this was written. The translators' own list of the
  claims most likely to say less than their scenario's harm (for example `deployment_broker_safe`, which concludes only that each
  published nonce has a *used* approval, not who signed it or that a reviewer saw the digest) is at the top of that file. The claim
  of record in `docs/DEPLOYMENT-CLAIM-v0.md` ("reviewed, exactly approved, once-consumed release") is therefore stronger than the
  Lean conclusion until the provenance invariant is proved; the reviewed/exact-approval parts are guards of the model's `approve` and
  `release` steps, plus tested correspondence, not reachable-state theorems.

- **Held-out round 2 (hardened profile, 34 cases).** Before any fix the static evaluation produced one false
  CONDITIONAL (see section 4); the post-fix 0/26 is contaminated. 22/34 cases are UNKNOWN. The author was
  again a blind `codex exec`, not a person. Round 1's 2/5 figure stays the round-1 number.

- **Held-out contamination.** The headline "zero over-rejections" on the 25 sealed cases is
  measured *after* a mount-order fix prompted by those same cases. The uncontaminated
  scores are the pre-fix ones: 2/5 supported rejected (40%) with the known-code hypothesis,
  5/5 raw. Zero false acceptances held in every phase.
- **Held-out author independence.** The author was a separate, sandboxed Codex instance —
  same model family as the builder, not an independent person.
- **Checker independence.** Sink-side checkers are separate programs but written by the
  same agents; they share `deployment/reconcile.py`-style assumptions.
- **Only two live bypasses were ever observed**, both on deliberately misconfigured
  deployments (writable sink with 0777 DAC; UID collision giving admin HALT). The clean
  deployment's denials cover replay, concurrent overspend and one TCP probe — not a broad
  attack campaign. No LLM agent was ever run against it.
- **Monotonicity and differential are finite experiments**, not universal theorems,
  except the safety-only `accepted_path_safety_monotone`.
- **Trusted-path code review** (`deployment/reviews/trusted-path-code-review-opus.md`) is a
  model review.
- **The T9 fixes have had no independent review at all.** The broker is now multithreaded
  (new concurrency paths; the Lean model and the refinement premise were not re-examined
  for them), the frame deadline and connection caps are constants chosen by the author, and
  the hardened profile's UNKNOWN-edge rule lives in the extractor (TCB), not in Lean. A
  reviewer should read `trusted_stack/server.py`, `trusted_stack/outbox_receiver.py`
  (`_reap_unlinked_pending`) and the `inventory_v2` rule in `extractors/compose/__init__.py`
  first.
- **Evidence generations.** Tier 2–8 live evidence was produced by source generation `r2-v0`
  (delegation always on, single-threaded broker, unhardened agents). It still replays, and its
  premises are the ones stated in the claim. Only the Tier 9 runs
  (`deployment/runs/tier9/`) exercise the fixed code.

## 6. Reproduction

```
# one command (supported host; needs Docker, passwordless sudo, offline rootfs)
python3 tools/cstack.py demo --output /tmp/cstack-demo           # exit 0 = all PASS, 3 = something SKIPPED

# static only (any Linux with Python 3.12+ and the pinned Lean toolchain)
python3 tools/cstack.py demo --output /tmp/cstack-demo --static-only
python3 tools/test_deployment_slice.py && python3 tools/test_deployment_release.py
python3 tools/check_deployment_monotonicity.py
python3 tools/check_deployment_subset_differential.py              # Lean differential
python3 tools/check_deployment_contract_witnesses.py
python3 tools/check_deployment_transcript.py                          # T4.4: regenerate, build, axioms, 3 mutants rejected
python3 tools/check_deployment_heldout.py --output /tmp/raw.json   # raw, fails closed
python3 tools/check_deployment_heldout.py --instantiate-known-code --output /tmp/model.json

# replay archived real-container evidence without launching anything
python3 deployment/check_container_run.py deployment/runs/tier2/containers-final
python3 deployment/check_remediated.py deployment/runs/tier5/remediated
python3 deployment/check_container_run.py deployment/runs/tier9/containers-hardened   # hardened generation
python3 deployment/check_remediated.py deployment/runs/tier9/demo-dev-clone/remediated
python3 tools/test_deployment_pins.py && python3 tools/test_deployment_hardening.py
python3 tools/build_deployment_fixtures.py --check && python3 tools/build_deployment_golden.py --check
python3 deployment/attribute_archives.py --output /tmp/attribution
```

PR chain (merge in order, owner's decision): #45 → #46 → #47 → #48 → #49 → #50 → #51 → #52 (Tier 8) → Tier 9.
