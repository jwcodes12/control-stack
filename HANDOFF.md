# Research track handoff: Milestone 1 flagship (2026-10-13)

Read first: [ROADMAP.md](ROADMAP.md) (revision 2), then the record
[docs/records/budgeted-audit-vs-adaptive-attacker.md](docs/records/budgeted-audit-vs-adaptive-attacker.md).
Branch `research/m1-flagship-20261013`, base `main` at `e7b4b25`. One pull request; **not to be merged without
independent human review**.

**What changed.**

- `ControlStack/Families/F6/FlagBudget.lean` (new): potential bounds for `val`/`cval`; flag-triggered auditing with a
  hard first-come budget: `flag_pre_bound`, `flag_exhaust_bound`, `flag_total_bound`.
- `ControlStack/Families/F6/SplitAudit.lean` (new): one kernel for hidden random audits, flag audits and their split:
  `split_hidden_bound`, `split_flag_bound`, `split_min_bound`, `split_product_pre`, `split_product_bound`; kernel
  witnesses `exhaustion_witness`, `average_recall_witness`, `dependence_witness`; `hidden_one_step`, `split_example`.
- `numerics/budgeted_audit.py`, `numerics/test_budgeted_audit.py`, `numerics/budgeted_audit/results.json` (new):
  exact executable model, 12 consistency checks, frozen tables.
- `docs/records/` (new) with the record; `tools/check_records.py` (new) validates its declaration references.
- `.github/workflows/m1-budgeted-audit.yml` (new): record check, banned-token grep on the two modules, model checks.
- `ROADMAP.md` rewritten as revision 2. `ControlStack.lean` imports the two modules. `registry/annotations.json`
  gains eight entries; `THEOREM-REGISTRY.*` and `LEAN-STATEMENTS-NORMAL-FORM.md` regenerated.
- No existing Lean file, frozen evidence, pinned artifact or `ControlStack/EgressGate.lean` was modified.

**Verification report.** VERIFICATION_PLACEHOLDER

**Not met, and what is needed to continue** (same list as ROADMAP section 4, M1).

1. Truncation lemma (prefix event). Next step: M2 step 1.
2. Imperfect reserved recall with visible flags. Needs `ReservedRecall`'s discount lemmas generalised from
   `AOut Unit`; that edits an existing file, so it waits for M2's refactor decision.
3. A usefulness quantity that distinguishes protocols. Needs a defer or block action: M2.
4. Honest against attacker-induced false positives in the exhaustion premise. Open modelling question.
5. Two papers read as abstracts only; two through an automated fetch. A person should spot-check the quotations in
   the record's section 7 before they are cited elsewhere.
6. External human review: the packet is the record's section 8. **No reviewer has been asked.** Model reviews
   (three, summarised in ROADMAP section 3) are not a substitute.

**Status words used here.** Completed: the files above exist. Verified: Lean-checked or test-checked as listed in
the verification report. Empirically supported: nothing in this milestone. Speculative: the measurement recipe for ρ
and the "constant-rate red teams understate risk" reading of the model values. Externally reviewed: nothing.

---

# SC-01 VM publication handoff — 2026-10-08

John requested publication onto private GitHub main and a linkable status file.
Canonical VM status: [gateway/vm/STATUS.md](gateway/vm/STATUS.md). Imported only
VM sources/receipts and their workflow from `sc01-vm-host-check-20261008` at
`9d4d785`, preserving remote main's existing Lean track. Codex infrastructure
ends at `9a43ae8`; Claude's `cda2b10` repairs the listener/connect race and
`9d4d785` records the complete frozen replay. These receipts verify in the
publication checkout. Config H is
`56a4dfa192003deaddf483ad008383ade9c0a2ca8d7eea0829fc401db7ff02a1`.

The link-bound configuration check and 10 resource controls pass. The usefulness
receipt is valid but its gate FAILED: baseline and mediated each complete 0/64
lifetimes, 0/320 episodes; every sender/receiver times out at the preserved
0.25-second deadline. Transport is no longer the blocker. Stop at failed step 4;
step 5 remains pending and the existing case stays CONDITIONAL. No results pooled,
no new channel experiment, no safety claim, no auditgate/ACL/IAM changes.

Next: usable hardware virtualization/separate hosts under existing permitted
access, or an owner-decided separately preregistered deadline amendment. MXC's
Linux MicroVM requires KVM and Hyperlight requires x86_64/KVM, so it does not
resolve this ARM64 host's limitation. Complete-observation proof remains separate.

Checks: saved isolation receipt, 10 unittest cases, frozen usefulness receipt
verifier, and whitespace checks; see publication verification receipt in STATUS.
Push uses `[skip ci]` to avoid the existing automatic cache experiment; dispatch
only the VM configuration/archived-receipt workflow. [VM verification CI](https://github.com/jwcodes12/control-stack/actions/runs/37851767586)
passed on publication commit `ef26633`. The saved CI receipt and canonical status
record its exact revision. No push-triggered workflows ran for the publication.
