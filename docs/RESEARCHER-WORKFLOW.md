# Researcher workflow: from a threat to a preregistered receipt

This is the day-to-day loop, with exact commands. SC-26 is the reference: its model, harness, preregistration, review
and evidence are a complete example (model `ControlStack/Scenarios/SC26Transaction.lean`, harness
`scenarios/SC-26/harness/`, preregistration `prereg/SC26-TRANSACTION-GATE-v2.md`, review
`reviews/sc26-2026-10-09/`, evidence `scenarios/SC-26/evidence/run-1/`, rechecker `tools/check_sc26_case.py`).
[STACK-MAP.md](../STACK-MAP.md) places scenarios in a real compute stack, and
[LAB-DEPLOYMENT-MAPPING.md](LAB-DEPLOYMENT-MAPPING.md) proposes (untested) lab realisations of each trusted component.
[ROADMAP.md](../ROADMAP.md) is the canonical status.

Nothing in this loop produces deployment assurance. Its output is a conditional claim with named premises, firing
negative controls and a preserved receipt, whether the run passes or fails.

## 0. Pick the component and the gap

```sh
python3 tools/stackmap.py --gaps                       # open premises, cheapest widely-blocking first
python3 tools/stackmap.py --researcher cloud_control_plane   # trusted role, premises, evidence, what to run
```

Choose ONE effect and ONE trusted component; state the Bad event on a log the gate does not write (SC-26: bank).

## 1. Write the spec and generate the skeleton

```sh
python3 tools/new_scenario.py --example-spec > /tmp/sc29.json          # edit: bad_event, roles, ops, checks, effect
python3 tools/new_scenario.py SC-29 /tmp/sc29.json --dry-run           # shows the five files; writes nothing
python3 tools/new_scenario.py SC-29 /tmp/sc29.json                     # writes them; never overwrites
```

**Spec rules (validated, fail-closed):** every check names its OWN control finding (`c<n>`); extra reconciliation
rules go in `rules`; `roles` must include `admins` (a `halt` op is added automatically); identifiers are lowerCamel and
must not collide with Lean or Python keywords or skeleton names.

**Generated files:**

| file | what it holds |
|---|---|
| `ControlStack/Scenarios/SC29<Name>.lean` | It compiles, and `step` is the identity. The TODOs are commented out. |
| `scenarios/SC-29/harness/model.py` | A mirror of the Lean model. |
| `scenarios/SC-29/harness/check_trace.py` | A c-rule registry. Its verdict is INCOMPLETE until the rules are written. |
| `scenarios/SC-29/harness/run_sc29.py` | The receipt conventions and the evidence gate. |
| `prereg/SC29-DRAFT.md` | The SC-26 v2 sections plus the review-lessons checklist. |

The generator does **not** create the scenario bundle. Until `scenarios/SC-29/` has `manifest.json`, `threat.md`,
`claim.lean`, `policy.json`, `correspondence.md`, `result.md` and `tests/README.md` (see
[scenarios/README.md](../scenarios/README.md)), `python3 tools/check_scenarios.py` fails. Copy the shape of a DRAFT
bundle such as `scenarios/SC-28/` and keep every status at UNRESOLVED or NOT_RUN.

## 2. Model in Lean first

```sh
lake env lean ControlStack/Scenarios/SC29Name.lean        # must compile before and after every edit
lake build ControlStack.Scenarios.SC29Name                # once real; add it to ControlStack.lean then
```

Replace the placeholders in this order: `step` (every `Checks` field consulted somewhere), `legal` (credential
separation), `Inv` and `Good`, `sc29_safe` for every legal trace from `init`, HALT modelled as send vs arrive
(`halt_freezes`, `inflight_after_halt`), `spec`, a non-vacuity theorem, and **one necessity witness per check**
(`no_<check>_breaks`, a concrete trace reaching the bad event).

State every premise in the docstrings. Record `#print axioms` for the headline theorems: standard axioms only, and no
`sorry`.

## 3. Mirror the model in Python and link it to Lean

Edit `model.py` line by line against the Lean: `step`, `guard`, `inv`, `good` and `legal`. Unwritten parts raise
`NotImplementedError` on purpose.

- **Differential test:** add `lean_difftest.py` on the pattern of `scenarios/SC-26/harness/lean_difftest.py`. It
  renders random traces with `model.to_lean`, `#eval`s them in Lean, and compares canonical states. It also needs a
  coverage rule: every constructor accepted N times, and effects actually occur.
- **Unit tests:** add `test_model.py` on the pattern of `scenarios/SC-26/harness/test_model.py`, with one test per
  Lean witness.

```sh
python3 -m unittest discover -s scenarios/SC-29/harness -p 'test_*.py'
python3 scenarios/SC-29/harness/lean_difftest.py
```

## 4. Build the harness

**`run_sc29.py`:** fill in `attacks` (expected outcomes plus `check_trace`), `controls` (one check off per run under
`SC29_NEGATIVE_CONTROL=1`, each producing `check_trace.CONTROL_RULE[check]`), `usefulness` (an honest task with every
crash window injected) and `baseline` (no gate). Principals run under distinct numeric UIDs: set `REQUIRE_ROOT = True`.

**`check_trace.py`:** write each `rule_c<n>` from records the gate does not control (the external log; the approver's
own log keyed by file owner), and add `MUTATIONS`. The self-test refuses until every rule has a mutation that fires.

**Development runs** are dry runs to scratch directories. They are never cited:

```sh
sudo -n /bin/python3 scenarios/SC-29/harness/run_sc29.py --out /tmp/sc29-dry-1
python3 scenarios/SC-29/harness/check_trace.py /tmp/sc29-dry-1/attacks --self-test
```

## 5. Freeze the preregistration

1. Fill every TODO in `prereg/SC29-DRAFT.md` and tick the review-lessons checklist.
2. Commit the model, harness and checker.
3. Rename the file to its final ID (`git mv prereg/SC29-DRAFT.md prereg/SC29-NAME-v1.md`), and update `PREREG` in
   `run_sc29.py`.
4. Fill §7 with real hashes:

   ```sh
   sha256sum ControlStack/Scenarios/SC29Name.lean ControlStack/Core/Gate.lean scenarios/SC-29/harness/*.py
   ```

5. Commit the prereg. A `PENDING` row, a hash mismatch or an uncommitted pinned file makes the runner refuse the
   evidence label.

## 6. Run the evidence, exactly once

```sh
H=$(sha256sum prereg/SC29-NAME-v1.md | cut -d' ' -f1)
sudo -n env SC29_PREREG_SHA256=$H /bin/python3 scenarios/SC-29/harness/run_sc29.py \
    --label evidence --out scenarios/SC-29/evidence/run-1
```

The runner refuses a DRAFT prereg, a wrong hash, an `--out` outside `scenarios/SC-29/evidence/` or already existing,
mismatched pins, and dirty pinned files.

A failed hypothesis is final for that preregistration ID. Keep the receipt, and record OBSERVED_FAILURE. A fix needs
a new ID. Re-runs are allowed only for the infrastructure errors the prereg names, and every run is kept.

## 7. Review, then record

1. **Recheck and review.** Write a rechecker that recomputes verdicts from raw evidence and pins (pattern:
   `tools/check_sc26_case.py`). Get a foreign-family review if possible (say so when not); file findings and a
   disposition in `reviews/sc29-<date>/`, as in `reviews/sc26-2026-10-09/`.
2. **Manifest:** update `scenarios/SC-29/manifest.json` only from grounded evidence. Each assumption gets its four
   axes, and the six `scope_axes` are required.
3. **Stack map:** cite the new evidence in `stack/components.json`. The tool rejects a status the cited evidence does
   not support.

```sh
python3 tools/check_scenarios.py
python3 tools/stackmap.py --validate && python3 tools/stackmap.py --researcher <component>
python3 -m unittest tools/test_stackmap.py tools/test_new_scenario.py tools/test_check_scenarios.py
```

## Rules that came from real mistakes (SC-26 review)

- Freeze the prereg only after the artifacts it governs are committed, and pin their hashes inside it.
- Each negative control must produce its specific finding. Every reconciliation rule must be able to fire.
- Claim "no effect initiated after HALT", not "no effect after HALT", unless the model rules out in-flight effects.
- Say which mechanism gives exactly-once. In SC-26 it was the receiver's idempotency, not the gate's nonce.
- Usefulness fails on any double effect, not only on missed ones.
- Dev runs are labelled dry, and there is one evidence run.
- Claim no novelty without an independent reviewer.

## One front door: `tools/cstack.py`

`python3 tools/cstack.py <subcommand>` dispatches to the tools above and adds no logic of its own. It reads recorded
metadata and re-runs nothing, except under `check`. An unknown scenario id fails closed with exit 2.

| Command | What it shows | Built on |
|---|---|---|
| `status [SC-XX]` | Portfolio table, or one scenario: manifest status, theorems with docstring one-liners, evidence runs and their verdicts, open premises with their normalised id, and the done-criteria rows | `build_results`, `portfolio_ledger` |
| `check [--fast\|--full] [--list] [--only TEXT]` | Pass/fail table of the local suite; exits nonzero on any failure | the tools named in the table below |
| `ledger [--portfolio\|--stack\|--lab]` | Normalised premise table (by default, no Lean), or the stack or lab ledger from Lean | `portfolio_ledger`, `cert_ledger` |
| `new SC-XX spec.json [--dry-run]` | New scenario skeleton; refuses an id that already exists | `new_scenario` |
| `evidence SC-XX` | Pin verification for each run, plus preregs with their declared freeze status, and the recheck commands (details below) | `git show`, as in `check_sc26_case` |
| `map [--gaps\|--researcher C]` | Stack map views | `stackmap` |

What each suite runs:

- `--fast`:
  - every generated file in `--check` mode;
  - `stackmap --validate`;
  - `check_scenarios`;
  - every `tools/test_*.py`, except the root-only broker test, which CI runs;
  - `check_sc26_case --skip-lean`.

  `--fast` never compiles proofs. It does assume a built `.lake`, though: `test_cert_ledger`, `test_new_scenario`
  and `test_portfolio_ledger` each make small `lake env lean` calls. In a fresh clone, run `lake exe cache get` and
  `lake build ControlStack` first.
- `--full`: everything in `--fast`, plus:
  - the ledger check with Lean;
  - `lake build ControlStack`;
  - every `scenarios/SC-*/claim.lean`, with the same axiom scan as CI;
  - `check_sc26_case` with Lean.

What `evidence SC-XX` reports:

- **Pin verification.** Each run's recorded SHA-256 values are checked against its pinned commit with `git show`. The sources are:
  - the commit and hashes in `meta.json`, or
  - those in a `receipt.json`, plus the prereg's own pin table.
- **Failures.** Exit 1 if any pin fails: a hash that does not match, a path missing at the commit, a commit missing from the clone, or a run with no pins.
- **Working tree.** Whether a file has since changed is shown, but it is informational only. The run is judged against its commit, not against today's tree.
- **Preregs.** Each related prereg is listed with its declared freeze status, and whether it is unchanged since the run that recorded it.
- **Recheck commands.** The exact commands to recheck the run.

```sh
python3 tools/cstack.py check --fast          # before pushing
python3 tools/cstack.py status SC-26
python3 tools/cstack.py evidence SC-26
python3 tools/test_cstack.py                   # CSTACK_FULL=1 adds one Lean smoke test
```
