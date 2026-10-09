# Datacenter root ledger + F4 nonce-ownership hardening (2026-10-09)

## Datacenter root accounting

`tools/portfolio_ledger.py` now asks Lean for the typed
`ControlStack.DatacenterRoots.layerRootLedger`, using `tools/cert_ledger.py`.
Its output is appended to `ASSURANCE-LEDGER.md`. This tracks the five
datacenter-theory files and every root each depends on. It does **not** reclassify
those theory files as runtime-tested scenarios or add their roots to the 28-scenario
leverage counts. In `--no-lean` mode, the existing portable portfolio section
remains usable.

## F4: availability flaw and restricted model

`ControlStack/Families/F4/AttestedKeyRelease.lean` has a global `issue`
operation. Even with signature, freshness, allowlist and report-to-key binding
checks, a second genuine allowlisted session can quote and spend an honest
session's nonce. The preexisting safety theorems remain correct for their model;
the uninterrupted `honest_liveness` theorem does not establish liveness against
this interleaving.

The new `ControlStack/Families/F4/SessionBoundNonce.lean` is an alternative,
hardened protocol **model**. It:
- issues a nonce for one live session key via `issueFor`;
- checks that exact `(nonce, sessionKey)` pair at `requestFor`, in addition
  to all existing F4 `full` checks;
- rejects use of the original raw `issue` and `request` operations;
- contains kernel-checked examples showing that the old globally issued nonce
  can be consumed by a competitor, whereas the session-bound version rejects
  that particular competing request and lets the intended session finish;
- includes a general Lean example establishing that a request with no matching
  ownership pair leaves *all* broker state unchanged.

The original F4 module remains intact for statement-fidelity comparison and
backward compatibility. **Deployments must switch to the bound issuance and
release API**; importing the new Lean module alone does not change a deployed
broker, establish authentication of the issuer or recipient, imply atomic
transactional storage, prevent expiry under delayed scheduling, or establish
arbitrary-interleaving progress.

## Verification / stop conditions

```sh
lake exe cache get && lake build
lake build ControlStack.Families.F4.SessionBoundNonce
python3 tools/cstack.py check --fast
python3 tools/cstack.py check --full
python3 tools/portfolio_ledger.py --check
```

No preregistered evidence was rerun. The code above is not a statement that
these commands were run locally; require GitHub CI confirmation and a separate
statement-fidelity review before adoption.

## Assurance graph name check

Full CI also exposed a real SC-07 theorem-name edge mismatch: `refName 7` was emitting `SC7Refinement` rather than `SC07Refinement`. The shared helper now zero-pads single-digit scenario numbers and the TrustRoot registry blob pins were refreshed. This is a theorem-link/registry correction, not a new runtime proof.
