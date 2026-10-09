# SC-16 harness: deploy admission

This is a defensive reference test on one Linux host (STACK-MAP §4 item 6, without a real OCI registry, webhook or
HSM). A benign agent stages artifacts into a content-addressed store and points a mutable tag at them. A separate
reviewer reviews **by digest** and signs (digest, target) with its own Ed25519 key. A separate approver verifies that
signature and issues a signed one-use approval.

The admission controller is the only writer of the disposable target directories. It deploys only bytes fetched
**by digest** whose digest is reviewed and approved for exactly that target, once. Signatures use the system
`/usr/bin/openssl`.

The preregistration is [`prereg/SC16-DEPLOY-ADMISSION.md`](../../../prereg/SC16-DEPLOY-ADMISSION.md)
(`PREREG-SC16-ADMIT-v1`). It holds the decision rules, the calibration, the re-run policy and the mapping to
`SC16Deploy.lean`, `SC16Disjoint.lean` and `AuthInstancesA.sc16_safe_authenticated`.

## Files

| file | role |
|---|---|
| `registry.py` | The CAS, with files named by SHA-256 and the first stager recorded in an index. It also holds the mutable tag table, which any client may write. The stager is the principal of the connecting pid (SO_PEERCRED). |
| `signer.py` | `--role reviewer`: fetches by digest, refuses content it staged itself, applies its policy and signs "sc16-review\|digest\|target". `--role approver`: verifies the review signature, mints a nonce and signs "sc16-approval\|nonce\|digest\|target\|tag". Each role keeps its own key (mode 0700 directory) and its own fsync'd log. `--no-distinct-check` is a control. |
| `admission.py` | The admission controller. It checks, in order: the approval signature, an unused nonce, the target binding, the review signature, then fetches by digest and verifies SHA-256. It writes the file (fsync) and records the deploy. It handles HALT. Controls: `--by-tag`, `--no-target-binding`, `--no-nonce`. |
| `reconcile.py` | Independent reconciliation. It starts from the files on disk and checks them against the principals' own logs, re-verifying signatures. It also has mutation self-tests. It can be run on its own: `python3 reconcile.py <stack dir> <reviewer pub> <approver pub>`. |
| `run_sc16.py` | The agent flows, the H1–H6 checks and the receipt. |

## Hypotheses

Short form; the preregistration is authoritative.

| | condition | pass | Lean |
|---|---|---|---|
| H1 | 8 honest flows, plus five refusals: failed review, wrong target, self-review, forged review signature, forged approval signature | exactly the honest files deploy; each refusal gives its stated reason; reconciliation holds | `sc16_safe`, `sc16_reviewed_content`, `sc16_safe_disjoint`, `sc16_safe_authenticated`, `distinct_blocks_self_review` |
| H2 | the tag is moved to new content after approval | the approved digest deploys, never the new content | `verify_blocks_toctou` |
| H3 | an approval is replayed | refused | `no_nonce_redeploys` (deployed half) |
| H4 | 30 honest flows | all deploy within L_DEP | usefulness |
| H5 | admin HALT | approved deploys after the halt are refused | `halt_freezes`, `no_halt_check_breaks` |
| H6 | **NEGATIVE_CONTROL**: by-tag, no target binding, self-review, no nonce | reconciliation flags every file each one deploys | `toctou_slot_breaks`, `no_target_binding_breaks`, `self_review_without_distinct_check`, `no_nonce_redeploys` |

## Run

No root is needed, and the runner refuses to run as root.

```
/bin/python3 -B scenarios/SC-16/harness/run_sc16.py --kind dry --reps 5 --out /path/to/new-dir

# the single evidence run (committed, unmodified harness and prereg; CALIBRATION-STATUS: FIXED)
/bin/python3 -B scenarios/SC-16/harness/run_sc16.py --kind evidence --reps 5 --out /path/to/new-dir
```

Each stack's directory in `logs/<rep-hyp>/` holds:
- the reviewer, approver, registry and deploy logs;
- both public keys (never the private keys);
- a manifest of every deployed file with its SHA-256;
- every client call.

## Host safety

- **Privileges and network:** unprivileged, with no accounts, no sudo and no TCP. Only Unix sockets (mode 0600) are
  used, in a fresh `/var/tmp/sc16-run-*` directory (mode 0700).
- **Removal at the end:** that directory holds the keys and the target directories, and it is removed at the end.
- **Self-exit and wall limit:** every child exits by itself after 30 s, and the run has a 115 s limit. A full run
  takes about 45 s.
- **Cleanup:** children are killed in `finally` blocks. After every repetition, an independent `/proc` scan must find
  nothing, or the run aborts.
