# SC-26 adversarial review disposition

Reviewers:
- Gemini 3.1 Pro (via agy): a foreign-family model, reviewing the first version of
  `ControlStack/Scenarios/SC26Transaction.lean`;
- Opus 5.5 (Claude Code subagent): same family as the author, so it is NOT a foreign-family red team.
  Its review is in `opus-review.md` when complete.

| # | Finding (Gemini) | Disposition |
|---|---|---|
| G1 | Delivery was modelled as atomic, so `halt_freezes` ("no legal trace changes the bank") overclaims: a message in flight at HALT still reaches the real bank. | **Fixed.** Delivery is now split into `deliver` (the gate sends: halt-checked, logged to `net`) and `arrive` (the bank processes a message: not halt-checked, can repeat). `halt_freezes` now says only that after a HALT the gate sends nothing new and the bank gains only messages already in flight. New `inflight_after_halt` shows such a message completes; `halt_freezes_quiescent` gives the exact freeze when nothing is in flight. The harness halt rule follows: a bank entry after the HALT needs a `deliver` logged before the HALT. |
| G2 | `legal` restricts only `bankCall`; an `approve` carrying an approver's identity is accepted as genuine. The model does not authenticate. | **Documented as a premise.** The model reads caller identity as authenticated, and the runtime provides this through SO_PEERCRED. "Approved by an approver" means consent only under credential separation for approvers and admins. Now stated in the Lean header and `scenarios/SC-26/correspondence.md`; tested by attacks A2, A3, A13 and A14. |
| G3 | The cap bounds the amount, not the count; zero-amount payments are unbounded in number. | **Documented.** Each such payment still needs its own exact approval, so this is not an unauthorized effect. A count cap is out of scope (stated in the header). |
| — | Missing premises: multiple gates sharing a bank credential need disjoint id spaces; rolling back the `next` counter makes new requests collide with old keys (dropped silently by bank deduplication); approver UI binding. | **Documented** in the correspondence and threat files as residual assumptions. Privileged rollback is explicitly out of scope. |
| — | Prose said `withHalt` is not used. | Correct: SC-26 implements its own halt with a role check, because the runtime halt is an operation on the gate. No change. |
| — | Novelty: none; it is an induction over a state machine. | Agreed. |
