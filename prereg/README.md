# Canonical location for future preregistration drafts

This `prereg/` directory is the **only editable location for new experiment preregistration drafts and templates**. The three original B drafts have been moved here byte-for-byte as `SC01-*-DRAFT.md` and C's three preparatory templates remain here. These are not approved experiment protocols.

**Frozen historical preregistrations** named `PREREG-*.md` at repository root are immutable archival records. They were not edited or relocated; do not mistake this archival exception for permission to update them.

Before authorizing an experiment, choose one candidate draft, specify the exact host/environment, horizon, independent reviewer, falsification threshold, statistical rule, expected baseline, date and git hash. Obtain the owner's explicit approval *before* running it. No evidence receipt or existing prereg file may be regenerated to make a prior run pass.

In particular, SC-01's original 0.25 s QEMU TCG run remains a measured failure (0/64 complete lifetimes in each condition). A proposed deadline amendment or two-instance experiment is a **different protocol** and must never retroactively change its verdict. See [ROADMAP](../ROADMAP.md).
