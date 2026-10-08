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
only the VM configuration/archived-receipt workflow. Remote CI pending.
