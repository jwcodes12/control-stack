# control-stack: Lean-verified, capability-free guarantees for AI control

Machine-checked worst-case bounds for **untrusted monitoring with upfront honeypot tests** (a trusted mediator, a
shutdown rule, audits), stated so that the adversary (a colluding generator and monitor with a shared seed) is
universally quantified. Around that core: usefulness identities, converses for nonadaptive and adaptive testers, an
audit-then-defer variant, certificate forms with Lean-checked rational fixtures, a verified canonicaliser for a toy
language, an operational (VCVio `ProbComp`) game that is proved equal to the recursions, and a first action-layer
step (a bubblewrap mount-table model).

**Status at a glance: [ROADMAP.md](ROADMAP.md)** (completed, in flight, next, open assumptions). **Then [STACK.md](STACK.md)**: one row per guarantee, with its assumptions, the protocols it speaks to and its
status. The model and assumptions A1–A11 are in [DESIGN.md](DESIGN.md) §2.

## Reading guide

- Every result is a **conditional theorem about an idealised finite model**. The adversary is universally quantified
  only within the modelled class (stateless fresh-context monitor, shared seed, single-step Bad). Capability re-enters
  through the trusted-component constants (the domination constant L, the audit recall r, the incrimination floor α),
  the scaffold assumptions and the model class.
- The protocol bounds are **absolute** bounds on the joint event "survives the honeypot test, then causes an uncaught
  catastrophe". A monitor that FLAGs everything also satisfies them; usefulness is treated separately (UMUSEF1).
- **Who must be trusted for what:** the trust/assumption table in STACK.md ("Who must be trusted for what") and the
  labelled assumptions A1–A11 (TRUSTED-COMPONENT / MODELLING / STANDING) in DESIGN.md §2.3.
- **What is NOT claimed:**
  - no assurance about any deployed system, mediator, scaffold or audit process;
  - no claim that any real mediator satisfies the domination hypothesis (L or δ), or that audits reach recall r;
  - the scaffold properties (fresh stateless monitor calls, complete views, test before deployment, absorbing
    shutdown) are assumed, not verified;
  - SANDBOXF1/SANDBOX2F1 are theorems about modelled pathname resolution in a mount table, not tests of any running
    system;
  - the mathematics is classical or modest (counting, binomial moments, Neyman–Pearson, short inductions); nothing
    here is claimed to be "apparently open". No result has had a human expert review yet.
- **Prior-art positioning:** machine-checked worst-case probabilistic bounds for untrusted monitoring with upfront
  honeypots; **no comparable machine-checked artifact was found in this search**. This is not a priority claim and
  not a claim to be the first Lean formalisation of control protocols. Neighbours and informal anticipations are listed
  in STACK.md ("Prior art and positioning") and `reviews/related-work-2026-10-07.md`.

## Layout

| path | contents |
|---|---|
| `STACK.md` | status table and positioning (start here) |
| `DESIGN.md` | the formal model, assumptions A1–A11, theorem plan, disposition of the design reviews |
| `DESIGN-A2.md` | sampled-ROC certificate design and an exploratory kernel-checked LASR interval-game example |
| `COMPOSITION-N1-UMPROT.md` | current scope and assumptions for trusted/untrusted-monitoring composition |
| `CORRESPONDENCE.md` | ControlArena / LASR vocabulary mapped to the formal objects |
| `REUSE.md` | dependency decisions (VCVio, Mathlib, others considered) |
| `LESSONS-section.md`, `HISTORY.md` | process lessons; what was verified when |
| `ledger/<CAMPAIGN>.lean` | frozen statements: `namespace PL_<CID>` with `Claim` and `Witness` |
| `ledger/questions/`, `ledger/q_<CAMPAIGN>.md` | the campaign questions given to formulators (`q_` = preamble + question) |
| `proofs/<CID>.lean` | the gated proofs (`theorem claim`, `theorem witness`), one per CID |
| `fidelity/<CID>.md` | orchestrator fidelity audits (statement vs. informal claim) |
| `reviews/` | hostile design reviews, final reviews, an external critique and a related-work audit |
| `numerics/` | exact brute-force checks and rational ROC/certificate generators |
| `ControlStack/`, `ControlStack.lean`, `lakefile.lean` | the interface-level Lake project (Lean v4.34.0, VCVio) |
| `ledger-check/` | a Mathlib v4.35.0-rc3 Lake project and `check.py`, which re-runs the ledger gate's check |
| `core/UMDefs.lean` | an early encoding draft of the core definitions (not gated) |
| `scout/` | read-only scout notes on VCVio and two related Lean repositories |

Ledger CIDs (all verified): UMHSF1, UMSURVF1, UMPROTF1, UMSTRATF1, UMNOGOF1, UMLOWERF1, UMADAPTF1, UMUSEF1, UMDEFERF1,
UMCERTF1, TMCERTF1, TMGACF1, UMADAPTF2, TMCERTUSF1, CANONF1, SANDBOXF1, SANDBOX2F1 (UMADAPTF2 is in `ledger/UMADAPT2.lean`, TMCERTUSF1 in `ledger/TMCERT_USEQ.lean`). CID `XF1` has its statement in `ledger/X.lean` and its proof in
`proofs/XF1.lean`; dependencies are listed in `ledger-check/check.py`.

## How to check

Both checks need [elan](https://github.com/leanprover/elan). They use two different Lean versions, so they are two
separate Lake projects.

**Ledger proofs** (Lean v4.35.0-rc3, Mathlib v4.35.0-rc3):

```sh
cd ledger-check
lake exe cache get            # downloads the Mathlib build cache (several GB)
python3 check.py --all        # one Lean process at a time
```

For each CID, `check.py` assembles exactly what the ledger gate assembled: `import Mathlib`; the statement and gated
proof of every transitive dependency (each proof inside `namespace PLDep_<dep>` with `open PL_<dep>`); the statement;
the proof inside `namespace PLProof_<CID>` with `open PL_<CID>`; then `theorem gate_claim : PL_<CID>.Claim` and
`theorem gate_witness : PL_<CID>.Witness` with `#print axioms` for both. It runs `lake env lean`, applies the gate's
banned-token scan (no `sorry`, `axiom`, `native_decide`, ...), and passes a CID only if both theorems depend on no
axioms beyond `propext`, `Classical.choice` and `Quot.sound`. `--project DIR` reuses any existing Lake project with
Mathlib v4.35.0-rc3 built; `--emit DIR` only writes the assembled files.

**Interface level** (Lean v4.34.0, VCVio `9146f78c`, Mathlib v4.34.0), from the repository root:

```sh
lake exe cache get            # Mathlib v4.34.0 cache
lake build                    # builds VCVio and ControlStack; prints the axiom reports in ControlStack.lean
```

The download is large: the dependency checkout and builds took about 8.5 GB, plus about 3 GB for the toolchain.
`ControlStack/HoneypotBridge.lean` is the statement file of the bridge; `HoneypotBridgeProof.lean` restates and proves it
(`lake env lean ControlStack/HoneypotBridge.lean` checks the statement alone).

**Numerics:** `python3 numerics/<script>.py` (no third-party packages).

## Provenance notes

- **Statement hashes.** The "frozen <hash>" values in STACK.md and `fidelity/` are SHA-256 prefixes of the statement
  texts in the private ledger. Seven statement files here are byte-identical to the frozen texts (UMHS, UMSURV,
  UMPROT, UMSTRAT, UMNOGO, UMLOWER, CANON). Four differ **only in comments and docstrings**, which were anonymised for
  this export (UMADAPT, UMCERT, UMDEFER, UMUSE), so their hashes no longer match; their Lean code is identical after
  comment stripping. SANDBOX and SANDBOX2 additionally have renamed path literals (see below). All other proof files
  are byte-identical to the gated proofs.
- **Reviewers.** Model identities are anonymised. Reviewer A and Reviewer C are the two foreign model families that
  red-teamed every frozen statement; Reviewers A and B wrote the hostile design and final reviews. Statements were
  proved by isolated prover agents.
- **Sandbox model.** SANDBOXF1/SANDBOX2F1 are stated here as general lessons: in a bubblewrap mount table later binds
  shadow earlier ones; a read-only-root policy must place writable state-directory binds BEFORE the hiding tmpfs
  mounts; a writable host root lets an untrusted process modify toolchain directories that a later, unsandboxed
  process executes. The path literals inside the Lean model (`ledger/SANDBOX*.lean`, `proofs/SANDBOX*.lean`) came
  from one installation; for this export they were renamed to generic placeholders (e.g. `"home","user"`,
  `".agent-a"`, `".toolchain"`), consistently in statements and proofs. So these two statements also differ from the
  frozen texts in string literals, not only in comments; both were re-checked with `ledger-check/check.py` (pass,
  standard axioms).
- **Not included:** the review briefs (prompts), internal session logs, superseded statement drafts, the private
  ledger harness and its tooling, and reviewers' scratch scripts. References to them inside `reviews/` (for example
  `*-prompt.md`, `HANDOFF.md`, `SESSION.md`, `<scratch>/`) are historical.

## License

Apache-2.0; see [LICENSE](LICENSE). Copyright 2026 John Watkins.
