# SC-26 correspondence: model premise → enforcement → evidence → residual assumption

Model: `ControlStack/Scenarios/SC26Transaction.lean`. Implementation: `scenarios/SC-26/harness/`. Preregistration:
`prereg/SC26-TRANSACTION-GATE.md`. Each premise of the model is listed with the mechanism that enforces it on the
reference host, the evidence for it, and what remains assumed.

| Model element / premise | Runtime enforcement | Evidence | Residual assumption |
|---|---|---|---|
| Caller identity in `request`/`approve`/`execute`/`halt` is the OS identity | Gate reads the UID with `SO_PEERCRED`; JSON identity fields ignored | Attack A3; controls | Kernel integrity |
| `legal`: no untrusted operation carries the gate's credential | Gate runs as its own UID; bank accepts only that UID; agents cannot signal or inspect the gate | Attacks A1, A13, A14; `gate_credential_leak_breaks` shows necessity | Root and kernel are not compromised; no other process runs as GATE |
| Only the gate reaches the bank (`bankAuth`) | Bank checks `SO_PEERCRED` = GATE | A1; `auth` control | Bank code integrity; no alternate bank interface |
| Exact payload (`payload`) | Approve compares the full payload with the stored request; `execute` pays the stored request | A8; `payload` control; `payload_unchecked_breaks` | The approver reads the payload it approves (no UI deception) |
| Approver ≠ requester (`distinct`) | Role UID sets are disjoint and checked; approve also requires approver ≠ requester | A4; `distinct` control; `self_approval_without_distinct_check` | Role assignment by the root launcher is correct; approver credentials are not shared |
| One use per approval (`nonce`) and exactly-once delivery (`bankDedup`) | Reservation keyed by request id in one `BEGIN IMMEDIATE` transaction; bank `UNIQUE(key)`; recovery redelivers with the same key | A6, A7, A11; `nonce`/`dedup` controls; `no_dedup_retry_duplicates`, `nonce_protects_budget_only` | SQLite durability on this filesystem; no privileged rollback of either database |
| Global cap (`cap`) | Cap checked and spent updated in the reservation transaction | A9; `cap` control; `no_cap_breaks` | Amounts are what the bank executes (the bank pays the stored payload) |
| Absorbing HALT (`haltCheck`, `halt_freezes`) | `halted` flag checked in every operation and before every delivery, including recovery; no un-halt operation | A10; `halt` control; `no_halt_check_breaks`, `halt_check_blocks` | HALT is delivered to the gate (the model assumes delivery; `HaltLiveness.lean`) |
| Crash or retry = any number of `deliver` ops in any order | Fault injection after reservation and after the bank's acknowledgement, then restart | A11; usefulness phase (16 crashes) | Crash points beyond the two injected ones are covered by the model only |
| Runtime trace ↔ model | `check_trace.py` replays the gate's trace through `model.py` (a transliteration of `step`) and checks `Inv` at every step and equality of the final bank | H2a/H2b | The trace is complete (written before each reply; deliveries logged after the bank's acknowledgement and reconciled at recovery) |
| `model.py` ↔ Lean `step` | `lean_difftest.py`: random legal traces, Python result = Lean `#eval` | H3 | The difftest's sampling covers the interesting branches (coverage is reported) |
| Consent is independent of the gate | The approver's own log, not the gate's database, is the reference for reconciliation | H2c | The approver process is honest; its log directory is not writable by agents (A2) |

**Not established by this table:**
- human-approver comprehension;
- multi-host or multi-gate deployment;
- cryptographic approval (F7 signatures and key custody);
- privileged rollback;
- generality beyond the payment-like effect;
- independent human review of the statement (done-criterion 5).
