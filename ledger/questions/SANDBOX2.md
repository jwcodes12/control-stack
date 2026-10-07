QUESTION (campaign SANDBOX2: corrected sandbox fix). In the SANDBOXF1 mount-table model (dependency): (a) the
SANDBOXF1 fixed policy places writable state-directory binds AFTER the hiding tmpfs mounts, so declaring a CLI state
directory re-exposes its hidden session-log subdirectory (counterexample; found by Reviewer B's final review); (b) a
corrected policy (state binds BEFORE the hiding tmpfs mounts) confines host writes to scratch and the declared state
directories; (c) the corrected policy hides every hidden directory for EVERY choice of state directories (revealed
host paths inside hidden dirs lie only in the read-only Mathlib re-bind). Statements about modelled pathname
resolution; hard links, symlinks, /proc/<pid>/root and network side channels are outside the model (stated).
