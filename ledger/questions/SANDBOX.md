QUESTION (campaign SANDBOX: the ACTION layer's first theorem, about a REAL policy). Model the proofledger harness's
sandbox `dispatch.sandbox(work)` (bubblewrap) as a reference monitor over a mount table, and prove its intended
properties or refute them. The real code (harness/dispatch.py, 2026-10-07) is:
    args = ["bwrap", "--dev-bind", "/", "/", "--tmpfs", "/var/tmp", "--bind", str(work), "/var/tmp/work"]
    for d in HIDE_DIRS: if d.exists(): args += ["--tmpfs", str(d)]
    for f in HIDE_FILES: if f.exists(): args += ["--bind", str(work / ".empty"), str(f)]
    args += ["--ro-bind", str(MATHLIB_PROJ), str(MATHLIB_PROJ)]
    HIDE_DIRS = [~/research, ~/.claude, /tmp, ~/.codex/{sessions,log,shell_snapshots}, ~/.gemini/tmp,
                 ~/.gemini/antigravity-cli/{brain,conversations,scratch,log}];  HIDE_FILES = [~/.codex/history.jsonl]
    MATHLIB_PROJ = ~/research/alignment-contrib/lean/StabilityDebate ; the docstring claims "writable scratch only".
bwrap semantics modelled: mounts are applied in argument order; for a path, the effective mount is the LAST mount whose
target is a prefix of the path (a later mount on a prefix covers earlier deeper mounts; a later deeper mount shows
through); host-backed binds map target++rest to source++rest; tmpfs is private and ephemeral (writes do not reach the
host). Boundary assumptions (named, not modelled): no /proc/<pid>/root alias (requires --unshare-pid), no network or
other side channels; hidden FILES omitted. Claims: (a) the current policy does not confine host writes to scratch
(~/.elan, executed by the unsandboxed Lean gate, is writable); (b) a fixed read-only-root policy confines host writes to
scratch plus declared state directories; (c) the current policy hides the hidden directories except via the read-only
Mathlib re-bind. Checked by evaluating `effective` on the concrete policy (current: ~/.elan/bin/lake -> rw root bind;
fixed: ro root bind; ~/research -> tmpfs; Mathlib -> ro bind; scratch -> W rw).
