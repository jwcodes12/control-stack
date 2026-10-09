# SC-06 one-use consent: pre-ingestion counterexample and repair obligation

Scope: source-only fidelity review of [PR #27](https://github.com/jwcodes12/control-stack/pull/27) at `cc1e027f488b13c471781af16477b04a5b9af22a`. This note is **not** a Lean proof or deployment certificate.

## Counterexample trace in the proposed model

With `R0 = ⟨[5], [9], [7]⟩` and initial state `init`, consider:

```lean
run R0 init [
  .confirm 5 3 2 7 0 42,
  .ingest 2 1 42,
  .act 2 7 0 3
]
```

The `confirm` transition checks only that issuer 5 is in `R.users` and confirmation ID 3 is unused. It does not check that entry ID 0 exists yet. `ingest` then creates entry 0 with reader 2, writer 1, value 42. The later `act` matches all `allowed` predicates and appends `⟨3, 2, 7, 0, 42⟩`. Thus the advertised exact-entry binding is not temporal authorization of an already-present context object.

This is a *source-derived* counterexample; add a `by decide` negative control on the model branch and run the pinned kernel to confirm it.

## Minimum repair

- Reject confirmations unless the exact entry already exists and the issuer is an authorized user, or explicitly redefine the consent policy to allow prospective approvals and narrow the English claim.
- Prefer immutable, nonreusable entry identifiers; the current length-based allocation can reuse an ID for arbitrary initial states supplied to `run`, even though `init` traces append monotonically.
- Add positive and negative controls for confirmation-before-ingestion, wrong entry, same value with different provenance, repeated confirmation, and distinct valid approvals.
- Re-run pinned Lean kernel and `#print axioms` on all modified theorems; require no `sorryAx`.
- Regenerate `THEOREM-REGISTRY.json`, `THEOREM-REGISTRY.md`, and `LEAN-STATEMENTS-NORMAL-FORM.md` from source, then pass both generated-index and statement-catalog CI at the exact PR head.
- Obtain independent statement-fidelity review. A green Lean build does not establish the Python harness or live runtime implements this model.

No preregistrations, frozen evidence, v1 harnesses, or `ControlStack/EgressGate.lean` were changed.
