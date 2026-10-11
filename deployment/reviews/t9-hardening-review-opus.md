# T9 hardening review (062b558..a3d4363, branch sol/r2-tier9)

The reviewer's local experiment scripts are not committed (defensive scope); findings are described in prose only.

This is a read-only model review by Claude Opus 5.5. It is not an independent human review.

- **Repository state.** I made no edits, commits or checkouts in the repo, and I started no containers.
- **Tests.**
  - `tools/test_deployment_hardening.py`: 23 tests OK.
  - `tools/test_deployment_pins.py`: 6 tests OK.
  - `tools/build_deployment_fixtures.py --check`: consistent.
- **Experiments.** I ran local experiments in `scratchpad/t9/` (local Unix sockets and SQLite files only): `hotjournal.py`, `abbrev.py`, `gate_test.py`, `v1bypass.py`, `sinkaudit.py`, `tamper.py` and `nest_thread.py`.
- **Untracked directory.** `deployment/runs/tier9/demo-fresh-clone/` appeared as untracked while I was reviewing (mtime 04:22:38). It is not mine: its `COMMANDS.txt` shows a concurrent fresh-clone demo by another agent.

**Verdict.** I found no HIGH finding. The core effect path is unchanged, and the new code does not create a way for a sink `<id>.body` to exist without an approved, once-consumed, in-budget release. Three MEDIUM findings show that parts of the T9 claims hold only under unstated assumptions:
- the hardening rule depends on the inventory reporting it;
- the delegation detector is purely syntactic;
- the file-to-release sink audit can be satisfied by aliased file names.

## MEDIUM

### T9-M1: the extractor's agent-hardening rule applies only when the inventory reports hardening
- **Where:** `extractors/compose/__init__.py:111` (`inventory_v2`) and `:137-139`.
- **Scenario.** `collect()` applies the rule `agent-no-new-privileges-and-cap-drop-ALL-not-established` only if at least one runtime service carries a `hardening` key. A v1-shaped inventory leaves that key out of every service, and the rule is then skipped entirely, including when `replay=False` and the pins are the current generation.
- **Confirmed by running (`v1bypass.py`).** I took the hardened clean compose, removed `security_opt`/`cap_drop` from both agents and removed `hardening` from every runtime service. The fresh `collect()` produced no UNKNOWN edge, and `configuration_accepted` returned True, the same as the hardened clean case. A compose that *declares* hardening paired with a silent inventory is also accepted.
- **Why the claim is weaker.** Only `deployment/scan.py:118` refuses v1 inventories. Other paths reach `collect()` without that refusal:
  - `tools/run_deployment_containers.py:78`;
  - `cstack verify` applied to a v0 IR from `collect()`;
  - any caller using `normalize()` at its default `hardening=False`.

  The claim text says "the extractor makes an agent that lacks either ... an UNKNOWN edge". The verifier cannot tell which path produced an IR. The claim therefore holds only if every IR comes from `deployment/scan.py` with the v2 collector, and that assumption is unstated.
- **Fix.**
  - Gate the rule on `not replay or inventory_v2`, so that only archived replays may omit `hardening`.
  - Default `normalize(..., hardening=True)`.
  - Add a hardened-corpus negative: hardened compose with a v1 inventory, expected UNASSURED.

### T9-M2: the delegation detector is syntactic and can be evaded; replay ignores generations whose server always delegates
- **Where:** `deployment/scan.py:35-38` and `:129-136`; `trusted_stack/server.py:220` (argparse with `allow_abbrev` on by default).
- **Scenario 1: abbreviated flag (confirmed, `abbrev.py`).** The broker's argparse accepts unambiguous prefixes. `--allow-deleg`, `--allow` and `--al` all set `allow_delegation=True`, but `delegation_enabled()` only matches the literal constant `--allow-delegation` and returns False for each. The detector also misses the flag when it is built by concatenation, comes from a variable, or appears as any non-constant element of the execv list. `reference_policy` does not reject unknown elements in that list.
- **Scenario 2: replay of r2-v0 images (confirmed by reading).** For an r2-v0 image, replay reads the vaulted r2-v0 entry, which has no flag, so it reports no `broker-delegation-enabled-outside-claim-UNKNOWN`. Yet the r2-v0 `server.py` always exposed `delegate`. The disposition says r2-v0 evidence relies on the sink audit instead (see T9-M3).
- **Impact.** The entry is trusted code, so this is not attacker-driven. However, it is the only guard that turns a delegation-enabled deployment into UNKNOWN, and its correctness assumes the flag is spelled literally.
- **Fix.**
  - `ArgumentParser(allow_abbrev=False)`.
  - In `reference_policy`, require every execv argument to be a string constant from an exact allowlist of flags and values. Anything else makes the policy None, which is UNKNOWN.
  - Make the rule generation-aware: delegation is enabled if the server generation lacks the T9.2 gate, or if the flag is present.

### T9-M3: the sink audit's file-to-release direction accepts aliased names and never checks content
- **Where:** `deployment/sink_audit.py:16-20`.
- **Scope note.** This file is outside the listed diff, but the claim's T9 dispositions (M1 for r2-v0, L3 and L7) rest on it.
- **Scenario (confirmed, `sinkaudit.py`).** Take a final directory with release 1 and the files `1.body`, `01.body` and `١.body` (ARABIC-INDIC DIGIT ONE). The audit returns `unattributed_files: []` and `clean() == True`. The reasons:
  - `str.isdecimal()` accepts non-ASCII digits;
  - `int()` folds leading zeros;
  - `reconcile.py` only opens the canonical `str(rid)+'.body'`;
  - no step compares an aliased file's bytes with any release digest.

  A writer who bypasses the receiver can therefore leave unreviewed bytes in the sink that both evidence checks report as attributed. Detecting exactly that bypass is the audit's purpose. The `.body` suffix test also gives no protection here.
- **Fix.** Accept only `re.fullmatch(r'[1-9][0-9]*\.body', name)` with `name == f'{int(stem)}.body'`, and require `sha256(file) == releases.digest` for every file. Add the two alias names as negative controls in `test_sink_audit_over_archives`.

## LOW

### T9-L1: restart after a crash mid-transaction cannot start the broker (hot journal opened read-only)
- **Where:** `trusted_stack/server.py:229-249` (`stored_cap`, `delegation_rows`).
- **Scenario (confirmed, `hotjournal.py`).**
  1. A process is SIGKILLed inside a write transaction, which leaves a hot `gate.db-journal`.
  2. The container entry always passes `--bootstrap-cap`. On an existing DB, `main()` calls `stored_cap()` before any read-write open.
  3. SQLite cannot roll back a hot journal on a `mode=ro` connection. The call fails with `OperationalError: attempt to write a readonly database`, and the CLI exits with rc 1. `delegation_rows()` fails the same way.
- **Impact.** Restarting a killed broker is the case T9.3 claims to handle, so that claim is not met here. The result fails closed: the broker stays down until some read-write opener (the receiver's `deliver_record` or a direct `Controller`) rolls the journal back. Meanwhile socket HALT is unavailable. If `stage` crashes on an uninitialised file, bootstrap is likewise never retried.
- **Fix.** Construct `Controller(a.db, principals)` first. Its `_open` is read-write, applies the ownership checks and rolls back the journal. Read the cap and delegation count afterwards over that connection, and turn errors into a clean SystemExit. Add a restart test that kills the broker inside a transaction.

### T9-L2: a gate test that cannot fail
- **Where:** `tools/test_deployment_hardening.py:79-85`.
- **Problem (confirmed, `gate_test.py`).** `test_over_a_real_socket` sends `delegate` for a nonexistent nonce to a `delegate_uid` that is a reviewer. With `serve(..., allow_delegation=True)` the reply is the same `DENIED`, because the controller denies it on its own.
- **Fix.** Set up a real approved nonce and an agent delegate. Assert that delegation succeeds with the gate on and is DENIED with it off, and that no `delegations` row appears.

### T9-L3: the tampered-hardening test passes for a different reason
- **Where:** `tools/test_deployment_hardening.py:284-290`.
- **Problem (confirmed, `tamper.py`).** The tampered `runtime.json` is rejected at `check_container_run.py:33`, the raw re-normalization comparison. It never reaches the hardening assertion at `:36` or the extractor rule.
- **Untested.** No test exercises an unhardened agent that is reported consistently, meaning raw rows, `raw_sha256` and `runtime.json` all agree.
- **Fix.** Add a test that tampers the raw inspect rows consistently, recomputes `raw_sha256`, and expects the line-36 assertion or the extractor's UNKNOWN edge.

### T9-L4: the evidence checkers do not bind the source generation
- **Where:** `deployment/pins.py:44-49` and `deployment/check_container_run.py:20-23`.
- **Confirmed by reading.**
  - `require()` accepts each file independently against any vaulted generation, so a pin that mixes generations passes.
  - The set of keys in `pin['source_sha256']` is never required to equal `tracked()`, so an archive that omits `server.py` passes vacuously.
  - `collect(replay=True)` likewise accepts a controller pin from one generation and a receiver pin from another.
  - A `profile: hardened` archive built from an r2-v0 image (single-threaded broker, delegation always on) would pass the checker. The actual tier9 archive pins `server.py` at the r2-v2/v3 hash, which I verified.
  - All checks are `assert`s and vanish under `python -O`.
- **Fix.**
  - Require a pin's source map to be exactly one generation (`known_generation`).
  - For the hardened profile, require a generation that includes T9.2 and T9.3.
  - Replace the asserts with explicit raises.

### T9-L5: replay is not a faithful re-run of the fresh rules
- **Where:** `deployment/scan.py:118` and `:129`.
- **Problem (confirmed by reading; not run, because it needs the Compose CLI).** Some UNKNOWN reasons are emitted only on fresh scans: `runtime-inventory-lacks-hardening-facts-UNKNOWN`, and the source mismatch for an older generation. Replay skips both.
- **Consequence.** `cstack plan` replays a fresh 0.1 IR that contains either reason. It then raises "plan inputs differ from the scanned IR" instead of producing the remediation that `plan.py` was written to emit for v1 inventories. This affects availability only; the result fails closed.
- **Fix.** Record in host-observations whether the scan was fresh, and have replay apply the same rule set that the recorded scan applied.

### T9-L6: HALT liveness under the new broker is weaker than documented
- **Where:** `trusted_stack/server.py:21-24` and `:102-109`.
- **Confirmed by reading.**
  - The comment says `MAX_CONNECTIONS=12` leaves "room for trusted roles", but `claim_slot` reserves nothing. Six UIDs outside any role that can reach the socket would fill every slot and hold them indefinitely by reconnecting, and admin HALT would then be refused. The socket is 0666 in a host directory with mode 0755. Under the claim's two agent UIDs (4 slots) the property holds, but that premise is unstated.
  - `halt_with_retry` makes 4 attempts, about 60 s. The claim says "retried until it commits".
- **Unconfirmed.** SQLite's busy handler is not FIFO. Four agent workers continuously staging distinct 1 MiB bodies might starve HALT's `BEGIN IMMEDIATE` across all retries. The same staging has no storage quota, so it can also fill the disk, after which HALT cannot commit at all.
- **Fix.** Reserve slots for the trusted UIDs. Add an in-process HALT latch that refuses agent operations before they touch the DB once a HALT is received. Correct the wording in the claim.

### T9-L7: two accept-loop failure paths still end the service
- **Where:** `trusted_stack/server.py:165-177`.
- **Confirmed by reading.**
  - If `threading.Thread(...).start()` raises (thread or pids limit), the slot claimed just before is never released and the exception exits `serve()`, which unlinks the socket.
  - `accept()` or `getsockopt` raising `OSError` (EMFILE, ECONNABORTED) also exits `serve()`. This path predates T9.
- **Fix.** Wrap the per-connection setup in try/except. On failure, release the slot, close the connection and continue.

### T9-L8: `clear_stale_socket` edge cases
- **Where:** `trusted_stack/server.py:183-198`.
- **Confirmed by reading.**
  - `ECONNREFUSED` is also returned for a socket that is bound but not yet listening. Two concurrent starts can therefore unlink each other's fresh socket and orphan one broker. Both brokers would use the same DB, so safety is unaffected.
  - `serve()` checks only `parent.is_dir()`, not who owns the socket directory or its mode. The scanner checks this for Compose deployments, but not for other launchers.
- **Fix.** Take an exclusive `flock` on a broker-owned lock file next to the socket before probing and unlinking. Require the parent directory to be owned by the euid and not group- or world-writable.

### T9-L9: DB URIs are built by string interpolation and read before the ownership checks
- **Where:** `trusted_stack/server.py:155` and `:231`.
- **Problem.** `f"file:{db}?mode=ro"` does not escape `?`, `#` or `%`, so an unusual operator-chosen path can open a different file than `Controller` opens (it uses `as_uri()`). These reads also happen before `_open`'s owner and mode checks.
- **Fix.** Use `Path(db).resolve().as_uri() + '?mode=ro'` after constructing `Controller`.

### T9-L10: the receiver delivers delegated releases whatever the broker profile
- **Where:** `trusted_stack/outbox_receiver.py:191-204`.
- **Scenario.** A DB used once with `--allow-delegation` keeps admitted delegated `effect_records`. The broker then refuses to start, but `deliver_record` still publishes them. The sink audit would report this.
- **Fix.** Give the receiver an equivalent profile switch that rejects releases with a delegation row.

### T9-L11: the vault is effectively part of the TCB
- **Where:** `deployment/pins.py:1-8`.
- **Problem.** "Never trusted by name: only its bytes' hash counts" is misleading. Any file placed under a generation directory makes its hash acceptable in replay. No test binds the generations to commits. I checked by hand that r2-v0, v1, v2 and v3 equal 062b558, 3ad3205, 7acc2aa and bdd0f05 exactly.
- **Related.** Every T9 commit is `[skip ci]`, so the CI-only `build_deployment_fixtures.py --check` never ran on them. It passes locally.
- **Fix.** Add a test that compares each generation with `git show <commit>:<path>` for a recorded commit. Add the vault to the TCB list in the claim.

### T9-L12: image source correspondence covers only the expected `*.py` names
- **Where:** `deployment/scan.py:64-65`.
- **Status.** Predates T9 and is unconfirmed for the image.
- **Problem.** A stale or crafted `slice/trusted_stack/__pycache__/*.pyc` whose header records matching source mtime and size, or an extra module on `PYTHONPATH=/slice` such as `sitecustomize.py`, would execute while every hashed `.py` still matches.
- **Fix.** Hash the whole `slice/` subtree, or require that it contains no other entries.

## Checked and found sound
- **Delegation gate.** Op matching is exact dict lookup, so case or Unicode variants and duplicate JSON keys end in shape denial or the gate. Shapes are exact, so no `uid` or `cost` injection is possible. `release` grants only through `delegations` rows, and the startup refusal when such rows exist closes the DB route. No other op reaches `controller.delegate`.
- **Threading.**
  - The `Controller` is immutable after init, and every operation opens its own SQLite connection, so no connection is shared across threads.
  - All mutations are `BEGIN IMMEDIATE` and serialized across threads and processes.
  - Slot claim and release happen under one lock, and `release_slot` runs in `finally`.
  - Every worker is time-bounded: read deadline 3 s, SQLite busy 15 s (HALT about 60 s), send 5 s.
- **Frame deadline.** A total monotonic deadline covers the whole frame, and a first byte other than `{` is rejected immediately. The catch-all turns `RecursionError` and `sqlite3.Error` into DENIED. With the image's own musl Python 3.14.8 (`nest_thread.py`), nested JSON inside a worker thread raises `RecursionError` rather than overflowing the 128 KiB musl thread stack.
- **Role checks.** HALT, approve, issue_lease and revoke are role-checked against the `SO_PEERCRED` UID (now unpacked unsigned). The broker refuses an agent or non-admin euid before touching the DB.
- **`clear_stale_socket`.** It unlinks only a `lstat` socket owned by the euid when the probe gets `ECONNREFUSED`. A live, busy or full-backlog listener yields an error, so the file is not removed.
- **Reaper.** `_publish` is called only from `deliver_record` while that call holds `BEGIN IMMEDIATE` on the controller DB, and the reaper runs under the same lock after the HALT check. A single-link `.pending-<32hex>` file therefore cannot be in flight for the same DB. Two-link post-link states are left to reconciliation. If the reaper unlinks a temp file that a concurrent *other-DB* deliverer is using (outside the claim), the result is only a failed `link`.
- **Fresh versus replay paths.** A fresh `scan()` never takes the vaulted-generation branch (`observed_snapshot is None`). A fresh `collect(replay=False)` ignores vaulted pins and reports hash drift. `known_generation` requires an exact full source-map match. `vaulted_file` is per path, so a digest vaulted for one path cannot satisfy another.
- **Collector `normalize(hardening=True)`.**
  - It allows only the no-new-privileges values. Anything else in `SecurityOpt`, a `CapAdd`, or a `CapDrop` other than exactly `["ALL"]` fails closed (unsupported, DRIFT or UNKNOWN).
  - Stripping `hardening` from an archived v2 inventory is caught, because v1 normalization of a container with `SecurityOpt` set marks it unsupported.
  - The extractor accepts `security_opt`/`cap_drop` only at the exact hardened values.
- **Fresh-scan hardening path.** With a v2 inventory, both agents must declare and report `no_new_privileges` together with `cap_drop: [ALL]`. The file-capability inventory must be a list, and a non-empty list is UNKNOWN.

## Disposition (Claude, same session)

The review ran at a3d4363 (source generations `r2-v0`..`r2-v3`). Fixes below are in the commit that adds this file; every
fix has a regression test that was checked to fail without it where noted.

| Finding | Disposition |
|---|---|
| T9-M1 hardening rule only if the inventory reports it | **Fixed.** `collect()` now requires agent hardening unless `replay=True` (silence is not hardening); `normalize()` defaults to `hardening=True`; the sealed held-out evaluation, which is a frozen v1-profile corpus, uses replay mode and reproduces its archived figures (22 plans accepted, 0 over-rejections). New negative: hardened compose with a silent inventory is UNKNOWN. |
| T9-M2 delegation check evadable | **Fixed for the entry.** The broker parser has `allow_abbrev=False`; `delegation_enabled()` now returns True unless the execv list is exactly `-m trusted_stack.server` plus allowlisted flags with constant values (and `str(<name>)` for the cap). Tests cover exact flag, abbreviations, assembled strings, variables, unknown flags, flag-as-value, computed cap. **Not changed:** replay of `r2-v0` images still reports no delegation edge although that server always exposed `delegate`; the claim states that evidence from `r2-v0` rests on the sink audit. |
| T9-M3 sink audit aliases | **Fixed.** Only canonical ASCII `[1-9][0-9]*\.body` names count, and a file is attributed only if its bytes hash to its release digest and it is a regular file; aliases are `non_body_files`. Tests: `01.body`, Arabic-Indic digit, `.bak`, `+1.body`, wrong bytes, symlink. |
| L1 restart after a kill mid-transaction | **Fixed.** `Controller` (read-write) is opened before the read-only cap/delegation reads, so a hot journal is rolled back. The test leaves a real hot journal and fails with the old order. |
| L2 gate test could not fail | **Fixed.** The test builds a state where `delegate` is valid and shows the same request is DENIED with the gate shut and accepted with it open. |
| L3 tamper test hit the wrong check | **Fixed.** The new test rewrites the raw inspect, its hash and the derived runtime consistently, so only the hardening assertion rejects it. |
| L4 checkers do not bind one generation; asserts vanish under `python -O` | **Open, stated.** Mixed-generation pins can pass; a "hardened" archive is recognised by its recorded profile and by the daemon-reported hardening, not by a single generation. Checkers must be run without `-O`. |
| L5 replay omits fresh-only rules; `cstack plan` on such an IR errors | **Open (availability only).** |
| L6 HALT availability | **Partly fixed.** 4 of 12 slots are reserved for reviewer/approver/admin UIDs. Retries are four, about 60 s; the claim now says so. Not done: an in-process HALT latch, disk quota for staging, lock fairness. |
| L7 accept loop / thread start failures | **Fixed** (slot released, connection dropped, loop continues); tested with an injected thread-start failure. |
| L8 stale-socket edge cases | **Open.** Two simultaneous starts could remove each other's socket; no safety impact. |
| L9 DB path interpolation | **Fixed** (`Path.as_uri()`). |
| L10 receiver publishes delegated releases | **Open, stated.** The broker refuses to start on delegation rows; the receiver is unchanged. |
| L11 the vault is trusted code | **Wording fixed** in `deployment/pins.py`: the vault is part of the TCB; only bytes' hashes are checked against archive claims. Generations were checked by hand against commits 062b558, 3ad3205, 7acc2aa, bdd0f05; no test ties them to commits. |
| L12 image scan hashes only listed `.py` files | **Open (pre-T9).** A stale `.pyc` or extra module on `PYTHONPATH=/slice` would not be seen. |
