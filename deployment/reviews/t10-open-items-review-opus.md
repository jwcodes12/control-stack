# Tier 10 open-items review (origin/main..eng/close-open-items, code only)

Reviewer: Claude Opus 5.5, a model review of another agent's work. No independent human has reviewed this.
Scope: `git diff origin/main..HEAD` restricted to code and docs (runs, pinned sources, fixtures, goldens and the theorem registry are excluded).
I read the docs/DEPLOYMENT-CLAIM-v0.md sections "Trusted-path review dispositions" and "Tier 10" first.

**Method.**
- I edited no repo file except this one. I made no commits, started no containers and did not use docker, sudo or the network.
- Throwaway probes are in `/tmp/t10-review/`: `latch_open_fail.py`, `slice_probe.py`, `mix_probe.py` and `hooks/`.
- I ran these test suites, and all passed:
  - `python3 -m unittest discover -s trusted_stack -p 'test_*.py'` (71 tests, 2 skipped)
  - `tools/test_deployment_pins.py` (10)
  - `tools/test_deployment_hardening.py` (34)
  - `tools/test_deployment_heldout.py` (6)
  - `tools/test_deployment_plan.py` (7)
  - `tools/test_deployment_release.py` (7)
- I did not run these suites:
  - `tools/test_deployment_scanner.py`, because its setUp calls `sudo -n chown`.
  - The four root-run broker tests, because they need root, and `test_confined_effect_broker.py` also needs Landlock.

**Verdict: no HIGH finding.**
- I found no path where this change makes the verifier return CONDITIONAL or MODEL_ACCEPTED for something it refused before.
- I found no path where an agent UID gains authority.
- Every new runtime mechanism (UID-0 refusal, staging quota, delegated-release refusal, HALT latch, socket lock) can only refuse more.
- There is one MEDIUM finding: the "one source generation" fix is incomplete, while the claim says the T9 limits are closed.
- The LOW findings are mostly cases where the docs say more than the code does.

---

## MEDIUM

### M1: generation binding is incomplete, but the claim calls T9-L4 closed
**Where:**
- `tools/check_deployment_evidence.py:11,15-16` still checks each file separately with `require`.
- `extractors/compose/__init__.py:59-66` (`archived()`) still accepts each claim pin against any vaulted generation separately.
- `deployment/check_container_run.py:20` and `deployment/check_remediated.py:22` throw away the generation name that `require_generation` returns.
- The over-claims are at `docs/DEPLOYMENT-CLAIM-v0.md:190` ("The other limits found by that review are closed in Tier 10") and `:202-204` ("Evidence checkers bind one source generation ... a mixture no deployment ran is rejected").

**Scenario (reproduced, `mix_probe.py`).**
- **Per-file check accepts a mixture.** `pins.require` accepts `{trusted_stack/controller.py: <r2-v0 digest>, trusted_stack/server.py: <current digest>}` one entry at a time. That is exactly the loop `check_deployment_evidence.check` runs before `cstack verify --boundary-evidence` adds the `TESTED_BOUNDARY` obligation. `require_generation` rejects the same mixture.
- **Replay collection accepts a mixture.** A hardened clean compose that pins `broker_sha256` to r2-v0's controller and `receiver_sha256` to r2-v5's receiver gives `configuration_accepted = True` under `collect(replay=True)`. It gives False under `replay=False`. The T9 review named this third bullet of T9-L4 explicitly.
- **No minimum generation for the hardened profile.** T9-L4's second fix ("for the hardened profile, require a generation that includes T9.2 and T9.3") was not implemented. `require_generation` returns `r2-v0` … `r2-v5` for the matching full vaulted file sets (I ran it for every generation), and `check_container_run` accepts all of them for a `profile: hardened` archive.
  - That includes r2-v0, whose broker always allowed delegation. Replay with the vaulted r2-v0 entry also reports no delegation UNKNOWN (T9-M2, scenario 2).
  - `check_container_run` does not run `deployment/sink_audit.py`, which the claim names as the only evidence for r2-v0.
  - A hardened archive whose host observations lack `slice_tree` is replayed without the new slice-tree rule (`scan.py:180`), because rule selection depends on which keys are present, not on the recorded generation.

**Who gains what.**
- No deployment becomes CONDITIONAL. The gain goes to whoever produces evidence. An archive that mixes source files no deployment ran together, or hardened-profile evidence from a generation that predates the T9 or T10 fixes, passes these checkers as if it were current-generation evidence.
- The tier10 archives themselves resolve to `current`, which equals r2-v6. I checked every `deployment/runs/tier10/**/image-pin.json`, so the published evidence is not affected.

**Fix.**
1. In `check_deployment_evidence`, check a whole generation. Extend `generation_sources` (or add a variant) to cover the `BOUNDARY` files.
2. In `collect(replay=True)`, require both claim pins to come from one generation.
3. For `profile: hardened`, require that the returned generation is r2-v6 (or the current tree), or at least one that includes the fixes the profile depends on.
4. Until then, reword `:190` and `:202`.

---

## LOW

### L1: a HALT that fails in `Controller._open` is not retried, despite the claim
**Where:** `trusted_stack/server.py:154-157` and `trusted_stack/controller.py:121-132`. The claim is at `docs/DEPLOYMENT-CLAIM-v0.md:217-218` ("a HALT the caller gave up on is retried in the background until it persists").

**Scenario (reproduced, `latch_open_fail.py`).**
1. A second connection holds `BEGIN EXCLUSIVE` on the database.
2. An admin calls `halt_with_retry(..., latch=latch)`. `Controller.halt`'s `_open` (`SELECT COUNT(*) FROM meta`) waits out the 15 s busy timeout and raises `Denied("controller state unavailable")`.
3. That message does not contain "persistence unavailable". So there is no second attempt, `keep_trying` is never called, and `latch._retrying` stays False.
4. After the lock is released and 3 s pass: `persisted=False` and the database still has `halted=0`.
5. In-process, every mutating request is still refused, so the latch itself fails closed. But a broker restart, which creates a fresh latch, accepts `stage` again. The separate receiver keeps delivering already-admitted releases, because it reads only `meta.halted`.

The common case is a `RESERVED` lock held by the receiver: `_open` succeeds there and the retry path does work. This is not a regression, because before the change the same HALT simply failed.

**Fix.** Start `keep_trying` on any failure of an admin HALT, not only on the "persistence unavailable" text. Say in the claim that the latch and the background retry last only as long as the broker process.

### L2: the staging quota does not stop an agent from filling the disk
**Where:** `trusted_stack/controller.py:194-197` and `docs/DEPLOYMENT-CLAIM-v0.md:218-219`.

**Scenario (not reproduced; reasoned from the profile, since I started no containers).**
- The quota limits only how much `artifacts` adds to the database.
- The hardened profile does not make agent containers' root filesystems read-only. `read_only` and `tmpfs` are not supported keys.
- So an agent can still fill the host filesystem through its own container's writable layer if that filesystem holds Docker's data root and the database bind-mount source.
- The gain is availability only (HALT cannot persist, and L1 then applies). There is no safety gain.

**Fix.** Reword the claim to "staging cannot fill it", or make a separate filesystem for the database a stated premise.

### L3: start-up hook detection matches file names only
**Where:** `deployment/scan.py:65,72-74`.

**Scenario (reproduced, `hooks/` and `slice_probe.py`).**
- Python 3.14 runs a `sitecustomize/__init__.py` package and a sourceless `sitecustomize.pyc` at start-up when they are on `sys.path`. An extension module `sitecustomize*.so` is also importable (I reasoned this, not ran it).
- `startup_hooks` flags only the basenames `sitecustomize.py` and `usercustomize.py` and the `*.pth` suffix. It returned `[]` for `usr/lib/python3/dist-packages/sitecustomize/__init__.py`, `usr/lib/python3.11/sitecustomize.pyc` and `.../usercustomize.cpython-311-aarch64-linux-gnu.so`.
- Under `/slice` these files are caught anyway, because `slice_tree_problems` flags any unexpected name.

**Who gains.** Only whoever builds the base image, which the claim already says is trusted and not inspected (`:212`). The wording "inventories ... the interpreter start-up hooks" says more than the code does.

**Fix.** Match the module name `sitecustomize` or `usercustomize` in any form (package directory, `.py`, `.pyc`, any extension suffix), or narrow the claim.

### L4: `require_generation(complete=False)` accepts keys with a null digest
**Where:** `deployment/pins.py:73` (`files.get(k)==v`).

**Scenario (reproduced).** `require_generation({'trusted_stack/controller.py': <r2-v0 digest>, 'trusted_stack/nonexistent.py': None}, complete=False)` returns `r2-v0`, because a key missing from the generation gives `None == None`. Keys that are never normalised, such as `tools/deployment_container_entry.py` or the `BOUNDARY` paths, fail closed unless their value is null.

**Who gains.** Effectively no one: the only `complete=False` caller reads the repo-committed `deployment/legacy-image-pin.json`.

**Fix.** Require `k in files` and `isinstance(v, str)`.

### L5: one negative in `test_local_receiver_os_boundaries.py` passes for a reason other than the one it states
**Where:** `tools/test_local_receiver_os_boundaries.py:63-70`. Not run (needs root); confirmed by reading.

**What happens.**
- `forged[-1] = str(agent)` makes `--admins` equal `--agents` (65534).
- `Principals` therefore raises `ValueError("agent and trusted roles must be disjoint")` before `deliver_cli` checks the euid.
- The new assertion `stderr == "DENIED"` is satisfied by that `ValueError` path, so the comment "the receiver's own refusal" is too strong.
- The second negative (genuine admin listed, run as the agent UID) does test the kernel-UID check.
- The disjointness short-circuit predates this change.

**Fix.** Forge with a UID that is in no role, for example `--admins <agent>` with a different `--agents`, so that only the euid check can refuse it.

### L6: the confined-delegate forbidden-file check passes on ordinary file permissions alone (predates the change; not run)
**Where:** `tools/test_confined_effect_broker.py:50-61` and the `forbidden` probe.

`root` is mode 0755 and now owned by ADMIN; before the change it was owned by root. Either way the delegate UID cannot create `root/forbidden-effect`, so the `EACCES` this probe sees does not show that Landlock was in force. The edit does not make this worse.

**Fix.** Put the forbidden path in a directory the delegate UID can write to.

---

## Checked and found sound

**`Principals` UID 0** (`controller.py:36`).
- `x >= 1` with `type(x) is int` excludes 0, negative values and booleans in every role.
- Root callers become strangers, and `deliver_cli._uids` lets 0 through only for `Principals` to refuse it (DENIED).
- No production path used admin 0 (grep).
- The scanner's `reference_policy` already refused UIDs ≤ 0.

**Staging quota.**
- It is checked inside the same `BEGIN IMMEDIATE` transaction, so two concurrent stages cannot both pass.
- Re-staging identical bytes stays free.
- A digest collision is still refused first.
- It only ever refuses more.

**Receiver delegation refusal** (`outbox_receiver.py:200-201`).
- The refusal sits after the approval binding check and before any grant logic.
- It also refuses a revoked grant and an orphan `delegated_releases` row.
- The default is off in the library and in the CLI (`allow_abbrev=False`, so `--allow` cannot abbreviate to it). Every harness path (`run_containers.py`, `run_deployment_boundary.py`) uses the default.
- The delegated-model tests now pass `allow_delegation=True`, so their revocation, HALT and tamper negatives still test grant logic and are not satisfied by the new blanket refusal. A new test covers the default refusal of a live grant.

**HaltLatch.**
- Only an admin can set it: `principals.allows(uid, 'admins')` uses the SO_PEERCRED uid, and the latch is set before the first attempt but only after that role test.
- Non-admin `halt` requests do not latch (tested for agent, reviewer, approver and stranger).
- The latch only refuses, `state` and `halt` stay allowed, and it never needs to clear because HALT is terminal in the controller.
- `_retrying` is guarded by a lock, and repeated or concurrent HALTs are idempotent.
- A request that passed the latch before HALT can still commit. This matches the claim's "starts no other mutating request".

**Socket lock.**
- The lock file is opened with `O_NOFOLLOW` (a symlink gives ELOOP, which is tested) and `O_CLOEXEC`. The process checks that it owns the file, that the file is regular and that the mode is 0600, then takes a non-blocking exclusive flock.
- The lock is taken before `clear_stale_socket`. The socket is unlinked before the lock is released, and the kernel releases the lock on crash or SIGKILL.
- The broker never forks.
- In the reference profile the lock sits in `/channel`. Agents mount `/channel` read-only, because a writable agent mount is an UNKNOWN edge, and channel custody requires a broker-owned 0755 directory. So agents can neither pre-create, replace, open nor flock the lock file.
- On other launchers, a lock directory that agents can write gives them only denial of service, just as pre-creating the socket already did (T9-L8, second bullet, still open).

**`slice_tree` / `slice_tree_problems`** (`slice_probe.py`).
- The expected names come from the repo's `current_sources()`, or from a vaulted generation that `known_generation` matched exactly. They are never derived from the image tree being compared.
- `./` prefixes and trailing `/` are normalised.
- Fail-closed cases:
  - A hard link (type `1`), an old-style regular file (`\0`), a symlink or a device node is flagged as an unexpected name or a wrong type.
  - A duplicate entry with a bad mode is still flagged.
  - A `..` path is flagged as unexpected.
- POSIX ACL write grants show up in the group bits (the mask), so `mode & 0o022` catches them.
- Absolute member names (`/slice/x`) and a uid stored as a string would escape the inventory. Neither can come from `docker export`, and the export is a daemon observation that the claim already trusts.
- Agents cannot change the broker container's `/slice`: the mount allowlist permits only `/channel`, `/private` and `/output` as targets.
- `python -m` uses WORKDIR `/slice` as `sys.path[0]`, and `working_dir` is an unsupported key.

**`cstack plan` with two rule sets.**
- In both `scan` and `collect`, the fresh rules emit a superset of the replay rules' UNKNOWN reasons, and fresh `collect` additionally requires the current pins. Accepting either set therefore admits nothing new.
- An exact `portable_observation_ir` equality is still required.
- The swallowed exceptions are raised by checks that do not depend on the rule set. Replay writes nothing, because every write is guarded by `observed_snapshot is None`, so the first attempt cannot affect the second.
- A plan is not a verdict.

**Extractor environment rule.** It only adds UNKNOWN, and only under fresh rules. It requires `PYTHONPATH == '/slice'` for every service, and `SLICE_ROLE == 'broker'` exactly when the role is broker. A list-syntax environment is already UNKNOWN. (Runtime environment values are not observed, only names. That premise predates this change.)

**`require_generation` where it is used.** It is strictly stricter than the old per-file `require` in `check_container_run`, `check_remediated` and `check_deployment_container_evidence`. The entry digest is now bound to the same generation. `PinMismatch` is an explicit raise, so it survives `-O`.

**`-O` refusal.** Every `tools/check_deployment_*.py` script and the `deployment` package refuse to run under `-O`. Running `deployment/*.py` directly also imports the package and refuses. `pins.py` has no assertions left.

**Template vault.**
- `vaulted_templates` checks both the hash and the label, and ignores a copy whose bytes no longer match its digest name (tested).
- An attacker who can write into `deployment/pinned-templates/` can add any template. Like the source vault, it is part of the TCB, though the Tier 10 text does not say so.
- Its effect is limited: `check_remediated` still independently replays the run's fresh IR, requires CONDITIONAL with a Lean acceptance and no sorryAx, and reconciles the sink.
- (Predates the change: `check_remediated` never compares `dest/compose.json` with the patched template.)

**Image builder.**
- It ships only `.py` files, owned by root (uid and gid 0).
- Subdirectories and symlinks would still be added, and host modes are kept. Both of those make the slice scan fail closed rather than silently pass.

**Transcript clock.** `now = max(releases.created)` makes every expiry check at least as strict as it was at issue time. The expiry+1 mutant is rejected.

**Root-run test edits** (read, not run). Moving the broker and admin calls to a non-root admin UID is correct. The chowns cover each directory the broker writes. Receiver calls run as the owner. The added stderr==DENIED assertions do rule out import failures (except as noted in L5). Post-HALT refusals over the socket may now come from the latch, but each test also confirms the persisted HALT (`halt` reply ok, `state.halted == True`).

---

## Disposition (author, after the review)

| Finding | Disposition |
|---|---|
| M1 | Fixed. `pins.generation_holding` (partial records, any tracked path) is used by `check_deployment_evidence`; the two claim pins of a replayed `collect` must come from one generation; hardened-profile archives need `current` or `r2-v3`+ (`pins.require_hardened_generation`, numeric ordering). The "rule set follows the recorded keys, not the generation" point is stated in the claim rather than changed. Tests: `test_replay_pins_must_come_from_one_generation`, `test_hardened_evidence_needs_a_generation_with_the_fixes`. |
| L1 | Fixed: any failure of an admin HALT starts the background retry; the claim says it lasts as long as the broker process. Test: `test_halt_that_cannot_even_open_the_database_is_still_retried`. |
| L2 | Claim reworded; a separate filesystem for the database is a stated premise. |
| L3 | Fixed: any `sitecustomize`/`usercustomize` module form (directory, `.py`, `.pyc`, extension suffix) anywhere in the image. |
| L4 | Fixed: a key must exist in the generation and the digest must be a string. |
| L5 | Fixed: the forged `--admins` overlaps no other role, so only the real-UID check can refuse it. Not run here (needs root in CI; it ran under sudo locally and passed). |
| L6 | Changed: the forbidden path is in a directory the delegate could write by permissions alone. Cannot be run on this host (no Landlock). |

The L1 fix changed `trusted_stack/server.py`, so a new source generation (`r2-v7`) was snapshotted and the live suite was re-run on it.
