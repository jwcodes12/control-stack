PROGRAMME CONTEXT. We are building a Lean-verified, CAPABILITY-FREE guarantee stack for AI control (Redwood/GDM-style
untrusted monitoring): theorems of the form "for every policy the untrusted model could follow, P(uncaught catastrophe)
<= X" with X a function of explicit parameters of trusted components (mediator kernel M, honeypot law P_H, shutdown
schedule, n_h, audit recall r, catastrophe set Bad). Design document (hostile-reviewed by Reviewer A and
Reviewer B; all core inequalities judged true; v1 incorporates every fix): DESIGN.md.
Model in one paragraph: submissions x in a finite X; a trusted mediator kernel M : X -> Z -> R gives the monitor's whole
view z; the untrusted monitor is a stateless rule phi : Z -> [0,1] (prob. of PASS) depending on a shared seed omega with
the generator; the generator is any history-dependent randomised policy; an upfront test runs n_h iid honeypots from
P_H (a PASS on a honeypot is a miss; the (j+1)-th miss shuts down with prob. kappa_j); then N deployment rounds: PASS on
a bad submission = catastrophe; FLAG uses an audit while u < b (bad caught w.p. r, else executes), FLAG with no audit
left halts (safe).

PROGRAMME OWNER'S OVERRIDE: classical lemmas are WELCOME as infrastructure for the stack. Triviality alone is
NOT a reason to kill these formulations; report novelty honestly in "trivial_tool"/"known_refs" but judge the verdict
on FIDELITY (does the Lean say what the informal claim says, with no excess or missing binders, no wrong-reason truth),
VACUITY (are the hypotheses jointly satisfiable non-trivially; is the Witness meaningful) and FALSITY (is any conjunct
false? try counterexamples, edge cases: empty Bad, zero entries, h=0, n_s >= n_h, r in {0,1}, b=0, N=0, eta<0).
QUESTION (campaign SANDBOX: the ACTION layer's first theorem, about a REAL policy). Model a research harness's
bubblewrap sandbox for untrusted provers, `sandbox(work)`, as a reference monitor over a mount table, and prove its
intended properties or refute them. The policy code (2026-10-07) is:
    args = ["bwrap", "--dev-bind", "/", "/", "--tmpfs", "/var/tmp", "--bind", str(work), "/var/tmp/work"]
    for d in HIDE_DIRS: if d.exists(): args += ["--tmpfs", str(d)]
    for f in HIDE_FILES: if f.exists(): args += ["--bind", str(work / ".empty"), str(f)]
    args += ["--ro-bind", str(MATHLIB_PROJ), str(MATHLIB_PROJ)]
    HIDE_DIRS = [the research tree, /tmp, one CLI config directory, and 8 session-log / snapshot / scratch
                 subdirectories of CLI state directories] (11 entries);  HIDE_FILES = [one CLI history file]
    MATHLIB_PROJ = the shared Mathlib project (inside the research tree); the docstring claims "writable scratch only".
bwrap semantics modelled: mounts are applied in argument order; for a path, the effective mount is the LAST mount whose
target is a prefix of the path (a later mount on a prefix covers earlier deeper mounts; a later deeper mount shows
through); host-backed binds map target++rest to source++rest; tmpfs is private and ephemeral (writes do not reach the
host). Boundary assumptions (named, not modelled): no /proc/<pid>/root alias (requires --unshare-pid), no network or
other side channels; hidden FILES omitted. Claims: (a) the current policy does not confine host writes to scratch
(a toolchain directory, executed later by an unsandboxed checker, is writable); (b) a fixed read-only-root policy confines host writes to
scratch plus declared state directories; (c) the current policy hides the hidden directories except via the read-only
Mathlib re-bind. Checked by evaluating `effective` on the concrete policy (current: the toolchain binary -> rw root bind;
fixed: ro root bind; research tree -> tmpfs; Mathlib -> ro bind; scratch -> W rw).
