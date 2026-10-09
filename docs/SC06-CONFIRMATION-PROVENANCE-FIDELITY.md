# SC-06: confirmation reuse and value-aliasing fidelity review

This is a **counterexample and review packet**, not a new assurance theorem or
a modification of the preregistered runtime experiment.

Source under review: `ControlStack/Scenarios/SC06Artifacts.lean`. The
independent reproduction candidates are in
`ControlStack/Scenarios/SC06ConfirmationReuse.lean`.

## Finding 1: confirmation is existential, not one-use

`SC06.ActOk` requires that there **exists** a matching confirmation for a
sensitive action whose selected context entry is from another agent. It does
not require a distinct, unconsumed approval for each action or a cumulative
spending/transfer cap.

The `same_confirmation_can_authorize_two_effects` witness constructs a trace
in `SC06.full` with **one** user confirmation and **two** executed sensitive
actions, each referencing the same confirmation identifier. The
`missing_confirmation_blocks_both` control confirms the pair is blocked
without that approval.

This does not falsify the exact formal theorem; it falsifies a stronger
English interpretation in which every irreversible action must have a
fresh, one-use confirmation.

## Finding 2: provenance is keyed by (agent, numeric value)

`SC06.ctxOf s r v` returns the **first** matching context entry by
`(agent, value)`. Two different artifacts may carry the same value but have
different provenance. The `same_value_different_provenance_is_ambiguous`
witness puts a locally written 42 and another agent's 42 into the context,
then calls `act 2 7 42` without a confirmation. The model attributes the
action to its first (local) entry, recording `fromOther = false`.

Thus `sc06_safe` is a property of **the entry selected by ctxOf**, not a
general theorem that every real-world derivation or use of that numeric
value carries its original source. The *runtime* agent and store use
`ctx_id`, which is more precise in this respect; the witness does not
demonstrate an observed runtime bypass.

## Remediation acceptance criteria

1. Give actions an explicit context-entry identity or provenance-tagged
   handle instead of an unqualified value. Prove that every action
   uses the very context entry whose source is tested; reject ambiguous
   aliases and substitutions.
2. If the safety goal requires one-use consent, add a consumed/issued
   confirmation state and prove injected or repeated actions cannot spend
   one confirmation twice. State the intended authorization multiplicity
   precisely.
3. Keep the cross-agent read and action-effect boundary mandatory. An
   agent-controlled filesystem path, cached unlabeled value, or alternate
   action adapter invalidates the model/runtime correspondence.
4. Require a successfully executed Lean kernel check and inspect
   `#print axioms`; CI runs are currently blocked (issue #25).
5. Review the elaborated theorem statement against the English bad-event
   claim before changing manifests, TrustRoot edges, or scenario status.
6. Do not edit or reclassify frozen SC-06 experiment evidence. A changed
   runtime protocol needs separate preregistration and its own results.

**Status:** candidate negative witnesses, NOT kernel-verified during this
work session; no runtime-protection guarantee or new model assurance claimed.
