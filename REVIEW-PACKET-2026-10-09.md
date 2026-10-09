# Statement-fidelity review packet — 2026-10-09 headline theorems

**For:** an independent human reviewer, under RUNTIME-VM-HANDOFF.md §9 (done-criterion 5).
**Prepared by:** a Claude Code subagent (Opus 5.5). This is the **same model family as the author**, so this packet is
**not** the independent review. It prepares that review and records an adversarial first pass.

**Source:** commit `aa26511b3f18193132a6a92bb3384a1f598d3cad`, `leanprover/lean4:v4.34.0`; target files unmodified
relative to it (SHA-256 in `reviews/statement-fidelity-2026-10-09/raw/source-sha256.txt`).

**Raw material** (`reviews/statement-fidelity-2026-10-09/raw/`): `01-statements` (elaborated `#check @Name` and
`#print axioms` of every headline theorem and witness, plus `Good`/`legal`/`full`/`Sound`/`init`/roles/state);
`02-definitions` (every `step` and the auxiliary predicates); `03-aux` (remaining auxiliaries and numerical examples);
`04-witnesses.lean` (four compiled reviewer witnesses: traces on which a theorem holds although the scenario prose
would call the outcome a failure). Each `.lean` has its `.out.txt`.

**Reproduce:** `cd /var/tmp/cs-export && lake env lean reviews/statement-fidelity-2026-10-09/raw/0N-*.lean`.
The `.lean` files import the individual modules, not `ControlStack`, because the root `.olean` predates the newest
imports.

**Axioms.** Every listed theorem depends only on `propext`, `Quot.sound` and (for some) `Classical.choice`.
`bridge_breaks_joint` depends only on `propext`. There is no `sorryAx`.

**Notation.** `X.` prefixes are dropped below. "Adversary" means the universally quantified trace `ops`. "Baked in"
means a premise enforced by a definition (`full`, `legal`, `step`, or an argument's type) rather than by a visible
hypothesis.

---

## 0. Top findings (adversarial; ranked by how much the prose overclaims)

1. **Caller identity is never authenticated in any model.** Every `step` accepts an operation carrying a trusted
   role's id as that principal's act; no `legal` premise excludes forged ids except SC-26 (only `bankCall` with the
   gate's id) and SC-18 (an admin-id `setSink` must name the trusted sink). "Approved / granted / confirmed / audited /
   reviewed by X" in the prose means only *an operation with X's id was accepted*. Credential separation is a
   correspondence premise for SC-08/09/10/12/16/17/18/19/23/25/26/28; SC-26 documents it (review D1) and most headers
   list it under "premises outside the model", but **no manifest `bad_event` says it**.
2. **SC-17 manifest overclaims** (witness W2). It says "Live permissions exceed the policy ceiling", but `Good`
   constrains only records written *at applies*: two out-of-band grants put the live state above the ceiling with
   `Good` true. The Lean header is honest ("not claimed: … prevented between reconciles"); the manifest is not.
3. **SC-25 "audit PASS for exactly its content" is digest-level** (witness W3). `sc25_safe` holds for every `h`; with a
   constant `h`, content 7 is audited, amended to 50, and 50 executes with `Good` true. There is no content-level SC-25
   theorem (contrast SC-16's `sc16_reviewed_content` with `Set.InjOn`).
4. **SC-23 provenance is the operation type, and the adversary controls the operation type** (witness W1). `userInput`
   and `derive` take no caller and arbitrary content; injected content re-entered via `derive 1 [] 66` has
   `prov = false` and drives a sensitive tool unconfirmed with `Good` true. "Depends on untrusted data" means "derived
   through label-propagating steps from a `toolResult`"; laundering is excluded only by the header premise that the
   planner never reads untrusted data.
5. **SC-26 manifest bundles a hypothesis-only and a runtime-only property into the Lean claim.** "Non-agent approver"
   needs `sc26_safe_disjoint`'s hypothesis (`sc26_safe` gives only approver ∈ approvers ∧ ≠ requester); "paid twice …
   per invoice" is in no Lean statement (`same_payload_twice_is_good` proves the model allows it; it is runtime rule
   c8); the title's "alters access or another irreversible action" is broader than the payment model.
6. **`full` flags that are really environment premises:** SC-12 `registryOnly` (`bypass` is a no-op), SC-09
   `attenuate` (exec gains nothing), SC-10 `singleEval`/`pinnedPath`, SC-28 `meter` (charge = `max actual 1`), SC-26
   `bankAuth`/`bankDedup` (receiver properties). Whether the platform removes the bypass path is not a gate behaviour;
   read these as hypotheses.
7. **SC-16 has no role-disjointness hypothesis or disjoint variant** (witness W4): agent 2, also a reviewer, "reviews"
   agent 1's content, which deploys with `Good` true. "Non-stager reviewer" is literally true; "trusted review" is not.
8. **F3 `fenced_after_eps` is definitional.** Its only hypothesis is "every event's epoch ≤ e0"; the conclusion follows
   from the sink's acceptance rule. "Independent of delivery" holds because delivery is absent from the statement; all
   content is in correspondence (every effect passes this sink; event epochs are the sender's; timestamps are the
   sink's).
9. **F6 bounds bake the attacker's information into types.** σ sees only attack bits and catch flags — never S,
   monitor flags, timing or audit latency. "Every flag process, even adversarial" is right about the flags' law, but
   flags are invisible to the attacker; if audits are observable (e.g. latency), use the leak-certificate forms
   (`reserved_leak_bound`, `audit_leak_bound`). `damage_bound` puts halt-on-catch into the damage functional (`ucX`),
   not into a modelled HALT.
10. **SC-02/04/24 manifests state the bad event as "probability above the bound"** — tautological framing.
    Applicability rests on premises baked into types (`gpu_bound`: one sender bit per quantum, history-independent
    stationary `W`; `log_channel`: receiver sees only template ids and quantised fields), to be checked against a
    deployment, not the proof.
11. **`Compose.bridgeSpec` is a `def`, not a theorem**; its hypothesis `BridgeAdmissible` ("preserves `Inv₂`, only
    appends") is close to its conclusion. `bridge_breaks_joint` uses toy gates; the scenario instance is
    `Witnesses/DeputyBridge.lean`.

**What is sound.** Every scenario theorem has a named non-vacuity witness and satisfiable hypotheses; the `legal`
premises are mild (SC-26 one constructor, SC-28 no rollback, SC-18 admin sink choice); SC-27Chain's prose ("not
claimed: that anchored evidence is true"; `rewrite_before_anchor_window`) matches its statement exactly — the model of
an honest statement in this set.

---

## 1. SC-26 — `sc26_safe`, `safe_of_sound`, `sc26_safe_disjoint`, `sc26_once`, `halt_freezes`

```
sc26_safe : ∀ (R : Roles) (cap : ℕ) (ops : List Op), (∀ o ∈ ops, legal R o) → Good R cap (run R cap full init ops)
safe_of_sound : ∀ R cap {C : Checks}, Sound C → ∀ ops, (∀ o ∈ ops, legal R o) → Good R cap (run R cap C init ops)
sc26_safe_disjoint : ∀ R cap, (∀ a ∈ R.approvers, a ∉ R.agents) → ∀ ops, (∀ o ∈ ops, legal R o) →
  ∀ e ∈ (run R cap full init ops).bank, ∃ r a, reqOf s e.1 = some r ∧ r.tx = e.2 ∧ (e.1, a, e.2) ∈ s.approvals ∧
    a ∈ R.approvers ∧ a ∉ R.agents ∧ a ≠ r.requester            -- s := run R cap full init ops
sc26_once : ∀ R cap ops, (run R cap full init ops).reserved.Nodup
halt_freezes : ∀ R cap (s : St) ops, (∀ o ∈ ops, legal R o) → s.halted = true →
  (run R cap full s ops).net = s.net ∧ ∀ e ∈ (run R cap full s ops).bank, e ∈ s.bank ∨ e ∈ s.net
```

**Definitions inlined:**
- `Good R cap s := (∀ e ∈ s.bank, ∃ r, reqOf s e.1 = some r ∧ r.tx = e.2 ∧ e.1 ∈ s.reserved ∧ Approved R s e.1 r) ∧
  (s.bank.map fst).Nodup ∧ (s.bank.map amount).sum ≤ cap`;
- `Approved R s k r := ∃ a, (k, a, r.tx) ∈ s.approvals ∧ a ∈ R.approvers ∧ a ≠ r.requester`;
- `legal R (bankCall c _ _) := c ≠ R.gate`, and `True` otherwise;
- `Sound C := distinct ∧ payload ∧ cap ∧ bankDedup ∧ bankAuth`, which excludes `nonce` and `haltCheck`.

**Plain English.** For any role assignment, any cap and any operation sequence that never presents the gate's
credential to the bank directly, every bank entry:
- has a request with exactly that payload;
- was reserved;
- was approved for exactly that payload by an id in the approver list that differs from the requester.

In addition, bank keys are unique and the bank total is ≤ cap. Under disjoint roles, the approver is not an agent.
Reservations are unique. After a HALT, the gate sends nothing new, and the bank gains only messages already in flight.

**Quantifier audit:**

| category | items |
|---|---|
| ∀ (adversary) | `R` (any roles, possibly overlapping), `cap`, `ops`, including `approve` with any caller id, `arrive` any number of times (crash and retry), and `bankCall` by any non-gate id |
| fixed | `init`, and `full` in `sc26_safe` |
| hypotheses | `legal` (credential separation, one constructor only); `Sound C`; role disjointness (`_disjoint` only) |
| baked into `full` / `step` | receiver idempotency (`bankDedup`), receiver authentication (`bankAuth`) |
| baked into the reading of `approve` | approver authenticity |
| non-vacuity | `honest_trace_pays` gives bank = `[(0, tx1)]` after a retry. The `legal` and `Sound` hypotheses are satisfiable. |

**Gap to the manifest** (bad_event: "…without an approval of exactly its payload by a **non-agent approver** distinct
from the requester, or is paid twice per request id **or per invoice**, or exceeds the cap, or is initiated after a
trusted HALT"):
1. "non-agent" requires `sc26_safe_disjoint`'s hypothesis; `sc26_safe` does not give it;
2. "per invoice" is not in Lean (`same_payload_twice_is_good`); it is runtime rule c8 only;
3. "approval" means "an `approve` op with an approver id" (finding 1);
4. "initiated after HALT" is `halt_freezes`, which is stated from an arbitrary halted state, not a reachable one. That
   is stronger, and fine.

**Reviewer checklist:**
- [ ] Is "consent" acceptable as "an op carrying an approver id", given that SO_PEERCRED is the only enforcement?
- [ ] Should the manifest cite `sc26_safe_disjoint` and drop "per invoice" from the Lean-backed claim?
- [ ] Is it acceptable that `Good` does not mention HALT, and that HALT is a separate theorem?
- [ ] Is excluding `nonce` from `Sound` (exactly-once from the receiver) reflected in every prose claim of
      "one-use approval"?

## 2. SC-28 — `sc28_safe`

```
∀ (admins : List ℕ) (G : ℕ) (ops), (∀ o ∈ ops, legal o) → Good G (run admins G full init ops)
```
- `Good G s := usedT s ≤ G ∧ (∀ lid, usedL s lid ≤ (budgetOf s lid).getD 0) ∧ s.usage.length ≤ G`;
- `usedT` sums the actual units recorded in `usage`;
- `legal (rollback _) := False`;
- `charge full a r = max a 1`, i.e. the meter charges actual usage.

**Plain English.** Without storage rollback, total actual usage, per-lease usage and the number of work steps never
exceed the global cap or the lease budgets.

**Quantifier audit:**

| category | items |
|---|---|
| ∀ | admins, G, ops: forks by anyone, `work w a r` with any actual `a` and reported `r`, restarts, and lease `issue` by any admin id |
| hypothesis | no rollback (anti-rollback premise) |
| baked into `full` | trusted meter (`meter = true`: the charge is the actual `a`); descendant attribution (`share`); global counter |
| non-vacuity | `honest_trace_works` gives usage `[(1,0,3),(1,0,4)]`. |

**Gap to the manifest** ("total consumption across agents **and all their descendants** exceeds the global budget,
a lease's lineage exceeds its budget, or work continues after revocation or HALT"):
1. "descendants" holds only for descendants created by the model's `fork`; processes that escape it are outside;
2. per-lease budgets are set by `issue` operations with an admin id. A forged admin id can issue any budget, but the
   global G is a parameter and stays sound;
3. revocation and HALT are separate theorems (`revoked_lease_stops`, `halt_freezes`), both cited in the manifest;
4. "actual usage" is the `a` argument, so the meter's honesty is the whole premise.

**Reviewer checklist:**
- [ ] Is `usage.length ≤ G` (number of work steps) intended, or an artifact of `max a 1`?
- [ ] Does the manifest make clear that the trusted meter is baked into `full`?
- [ ] Should a forged-admin `issue` be excluded by `legal`?

## 3. SC-16 — `sc16_safe`, `sc16_reviewed_content`

```
sc16_safe : ∀ R (h : ℕ → ℕ) ops, Good R h (run R h full init ops)            -- no legal premise
sc16_reviewed_content : ∀ R h ops, Set.InjOn h {c | (∃ e ∈ s.deployed, e.content = c) ∨ ∃ rv ∈ s.reviews, rv.content = c} →
  ∀ e ∈ s.deployed, ∃ rv ∈ s.reviews, rv.content = e.content ∧ rv.reviewer ∈ R.reviewers ∧ rv.reviewer ≠ rv.stager
```

**Definitions inlined:**
- `Good R h s := (∀ e ∈ s.deployed, DepOk R h s e) ∧ (s.deployed.map n).Nodup`;
- `DepOk R h s e := ∃ ap ∈ s.approvals, ap.n = e.n ∧ ap.target = e.target ∧ ap.approver ∈ R.approvers ∧ h e.content = ap.d
  ∧ ∃ rv ∈ s.reviews, rv.d = ap.d ∧ ReviewOk R h rv`;
- `ReviewOk R h rv := h rv.content = rv.d ∧ rv.reviewer ∈ R.reviewers ∧ rv.reviewer ≠ rv.stager`.

**Plain English.** Every deployment consumed a distinct approval for its target, and its content's digest equals the
approved digest. That digest was reviewed by a reviewer id different from the stager id. Under injectivity on the
contents in play, the deployed content IS reviewed content.

**Quantifier audit:**

| category | items |
|---|---|
| ∀ | R (overlapping roles allowed), every hash h, ops: any staging, mutable-slot writes, colliding content at deploy |
| hypotheses | `InjOn` (content version only) |
| baked in | `verify = true` (deploy re-hashes supplied content); the caller ids of `review` and `approve` are trusted |
| non-vacuity | `honest_trace_deploys` gives deployed = `[⟨0, 5, 7⟩]`. |

**Gap to the manifest** ("Content is deployed that was not reviewed by a non-stager reviewer, or to a target not
approved, or twice under one approval, or after HALT"):
1. `sc16_safe` alone is digest-level; content-level needs `sc16_reviewed_content`, and the manifest cites both;
2. "reviewer" may itself be an agent (witness W4); there is no role-disjointness variant;
3. "after HALT" is `halt_freezes`.

**Reviewer checklist:**
- [ ] Should SC-16 get an `sc16_safe_disjoint` analogous to SC-26?
- [ ] Is `InjOn` on the contents in play the right collision premise, rather than computational collision
      resistance?
- [ ] Is "non-stager" the intended independence notion?

## 4. SC-25 — `sc25_safe`

```
∀ R (h : ℕ → ℕ) (cls : ℕ → Bool) ops, Good R h cls (run R h cls full init ops)
```

**Definitions inlined:**
- `Good := (∀ e ∈ s.executed, ExecOk R h cls s e) ∧ (s.executed.map id).Nodup`;
- `ExecOk R h cls s e := (∃ v ∈ s.verdicts.take e.vlen, v.id = e.id ∧ v.pass ∧ v.d = h e.content ∧ ∃ a, v.by_ = some a ∧ a ∈ R.auditors) ∧
  (cls e.content → ∃ ap ∈ s.approvals.take e.alen, ap.id = e.id ∧ ap.d = h e.content ∧ ap.approver ∈ R.approvers ∧ ap.approver ≠ e.submitter)`;
- `full = {digest, atomic, failOpen := false, trustedClass, haltCheck}`. Note that `failOpen = false` is the *safe*
  setting.

**Plain English.** Every executed operation had, at the moment it executed, a passing verdict by an auditor id for
the **digest** of the executed content. If the trusted classifier calls the content irreversible, it also had an
approval of that digest by an approver id other than the submitter. Nothing executes twice.

**Quantifier audit:**

| category | items |
|---|---|
| ∀ | R, **every** `h` (including non-injective), **every** classifier `cls`, ops (amend, crash, timeout, any caller ids) |
| baked in | the classifier is trusted (`trustedClass`); auditor and approver ids are trusted |
| non-vacuity | `honest_reversible` and `honest_irreversible_with_crash`. |

**Gap to the manifest** ("executes before a trusted audit PASS for **exactly its content**…"):
1. The theorem is digest-level for every `h`. Witness W3 (constant `h`) executes content the auditor never saw, and
   `Good` holds. There is no `InjOn` variant;
2. "irreversible" means "irreversible according to `cls`", and `cls` is universally quantified (any classifier,
   right or wrong);
3. "after timeout" is the separate `expired_never_executes`.

**Reviewer checklist:**
- [ ] Should SC-25 add a content-level corollary under `Set.InjOn h …`, as SC-16 has?
- [ ] Is the classifier's correctness stated anywhere a reader of the manifest would see it?

## 5. SC-23 — `sc23_safe`

```
∀ (P : Policy) ops, Good P (run P full init ops)
```

**Definitions inlined:**
- `Good P s := (∀ a ∈ s.executed, ActOk P s a) ∧ (s.executed.filterMap conf).Nodup`;
- `ActOk P s a := a.tool ∈ P.sensitive → a.prov = true → ∃ n, a.conf = some n ∧ ∃ cf ∈ s.confs, cf.n = n ∧
  cf.tool = a.tool ∧ cf.vals = a.vals ∧ cf.by_ ∈ P.users`;
- `prov` is set to `true` only by `toolResult`, and propagated by `derive` from its sources (`derive id [] v` gives
  `false`).

**Plain English.** Every executed sensitive action whose arguments have ghost provenance "from a tool result" was
backed by a confirmation, by a user id, of exactly that tool and those argument values. No confirmation backs two
actions.

**Quantifier audit:**

| category | items |
|---|---|
| ∀ | P, ops, including `userInput` and `derive` with **arbitrary content and no caller** |
| baked in | the meaning of provenance (operation type), confirmation by a user id (not authenticated), the sensitive-tool list `P.sensitive` |
| non-vacuity | `honest_untainted` and `honest_confirmed`. |

**Gap to the manifest** ("arguments depend on untrusted data"):
1. W1: injected content re-entered via `derive` with no sources is "untainted", and runs unconfirmed;
2. the formal adversary may also issue `userInput`, so "user input" is whatever the trace says;
3. only tools listed in `P.sensitive` are covered.

**Reviewer checklist:**
- [ ] Is "provenance = operation type" an acceptable formalisation of "depends on untrusted data"?
- [ ] Should `derive`/`userInput` be restricted by a `legal` premise (trusted planner only)?

## 6. SC-12 — `sc12_safe`

```
∀ (admins : List ℕ) ops, Good (run admins full init ops)
```
- `Good s := ∀ e ∈ s.live, e.reg = true ∧ e.origin ∈ s.active ∧ e.origin ∉ s.ended`.

**Plain English.** Every live entity is registered, and its true lineage's session is active, not ended.

**Quantifier audit:**

| category | items |
|---|---|
| ∀ | admins, ops (spawns with any claimed session, bypass attempts, fires, session start/end with any admin id) |
| baked into `full` | `registryOnly` (`bypass` is a no-op), `lineage`, `revokeLineage` |
| non-vacuity | `honest_session_lifecycle`. |

**Gap to the manifest** ("…still live or a scheduled job of that lineage fires"):
1. "fires" is the separate `no_fire_after_end`, which is cited;
2. "every creation path goes through the registry" is a `full` flag (finding 6), not a visible hypothesis;
3. effects caused while live are not claimed, as the header says.

**Reviewer checklist:**
- [ ] Should `registryOnly` be a hypothesis about the platform rather than a check?
- [ ] Is "live list membership" the right notion of "persistence"?

## 7. SC-18 — `sc18_safe`

```
∀ admins trusted T ops, (∀ o ∈ ops, legal admins trusted o) → Good T (run admins trusted T full (init trusted) ops)
```

**Definitions inlined:**
- `Good T s := (∀ r ∈ s.released, RelOk T s r) ∧ (s.released.map id).Nodup`;
- `RelOk T s r := r.llen ≤ s.logged.length ∧ r.id ∈ s.logged.take r.llen ∧ r.clock ≤ r.lastAck + T`;
- `legal (setSink c v) := c ∈ admins → v = trusted`;
- `full.failOpen = false` is the safe setting.

**Plain English.** Every released response's id was in the trusted log when it was released, the release came
within T ticks of the last sink acknowledgement, and no id is released twice.

**Quantifier audit:**

| category | items |
|---|---|
| ∀ | ops (requests, writes, releases, sink outages, ticks, config writes by any id) |
| hypothesis | `legal` (anything with an admin id points the sink at the trusted sink) |
| baked in | an acknowledgement means durable commitment; `release` is the only release path |
| non-vacuity | `honest_logged_release`. |

**Gap to the manifest.** The manifest's "configuration changed by a non-admin" is `config_untampered`, which is
cited. Otherwise the statement matches the manifest.

**Reviewer checklist:**
- [ ] Is "T ticks since the last acknowledgement" the intended freshness notion (any acknowledgement, not this
      record's)?

## 8. SC-08 / SC-09 / SC-10 — `sc08_safe`, `sc09_safe`, `sc10_safe`

```
sc08_safe : ∀ E files ops, Good E (run E full ⟨files, [], false⟩ ops)
  Good E s := ∀ r ∈ s.ran, E.h r.1 ∈ E.allow ∧ (E.h r.1 ∈ E.interp → ∃ sc, r.2 = some sc ∧ E.h sc ∈ E.scripts)
sc09_safe : ∀ P ops, Good P (run P full init ops)
  Good P s := (∀ q ∈ s.procs, ∀ c ∈ q.caps, (q.lin, c) ∈ s.granted) ∧ ∀ u ∈ s.used, (u.lin, u.cap) ∈ s.granted ∨
              ∃ r ∈ P.elev, u.via = some (r.bin, r.args) ∧ r.cap = u.cap
sc10_safe : ∀ E, E.h E.pinned = E.pinnedDigest → ∀ ops, Good E (run E full init ops)
  Good E s := (∀ d ∈ s.decisions, ∃ i w, d.ver = some i ∧ s.versions[i]? = some (d.val, w) ∧ w ∈ E.admins ∧ i+1 = d.curLen)
              ∧ ∀ b ∈ s.builds, E.h b = E.pinnedDigest
```

**Plain English.** SC-08: everything that ran had an allowlisted *digest*, and interpreters ran only allowlisted
script digests, from any initial file system. SC-09: every capability a process holds was granted to its lineage, and
every use was granted or matches an exact elevation rule. SC-10: every decision used the latest version, written by an
admin id, and every build used the pinned toolchain, given that the pinned path hashes to the pinned digest.\
**Quantifier audit.** ∀ every `h` (SC-08, SC-10) and any ops. SC-08 is digest-level like SC-25, but its manifest
says "digest", so there is no overclaim. SC-09 accepts `grant` from any id in `P.admins` ("granted" = a grant op with
an admin id, finding 1), and under `attenuate` `execBin` is the identity (exec has no modelled effect). SC-10's
"written by an admin" means an admin id; `singleEval`/`pinnedPath` are `full` flags (finding 6).

**Vacuity.** `honest_execs`, `honest_privileged_work`, `honest_enforcement_and_build`.\
**Gap to the manifests.** The wording matches the statements, apart from finding 1 (ids versus principals).

**Reviewer checklist:**
- [ ] Is it acceptable that exec in SC-09 has no modelled effect at all (`execBin` is a no-op under `full`)?
- [ ] Does SC-10's hypothesis `E.h E.pinned = E.pinnedDigest` assume away the toolchain substitution SC-11 is about?

## 9. SC-17 — `sc17_safe`

```
∀ E (g0 : List G) ops, Good E (run E full (init g0) ops)
```

**Definitions inlined:**
- `Good E s := (∀ e ∈ s.applied, AppOk E s e) ∧ (s.applied.map id).Nodup`;
- `AppOk E s e := E.allowed e.live = true ∧ e.live = e.desired ∧ ∃ a ∈ s.approvals, a.id = e.id ∧ a.diff = e.diff ∧
  a.reviewer ∈ E.reviewers ∧ a.reviewer ≠ e.author`.

**Plain English.** At every apply, the resulting live state equals the new desired state and satisfies the ceiling,
and the applied diff is exactly one that a non-author reviewer approved. No proposal applies twice.

**Quantifier audit:**

| category | items |
|---|---|
| ∀ | E (any ceiling predicate), any initial grants, ops including `oob g` (out-of-band live mutation; no caller, not halt-checked) |
| baked into `full` | the `drift` and `resultCheck` flags |
| non-vacuity | `honest_apply`. |

**Gap to the manifest** ("Live permissions exceed the policy ceiling, …"):
1. W2: two `oob` grants make `allowed live = false` with `Good` true. The theorem bounds live state only at applies,
   and `reconcile_restores` only after a reconcile;
2. the manifest's first clause must read "at an apply, or after a reconcile".

**Reviewer checklist:**
- [ ] Should the manifest bad_event be narrowed to apply and reconcile instants?
- [ ] Is the drift-detection premise ("sees the whole live state") visible to readers?

## 10. SC-19 — `sc19_safe`

```
∀ E ops, Good E (run E full init ops)
```
- `DestroyOk E s d := d.actual ≤ E.R ∧ (∃ sn, s.snaps[d.snap]? = some sn ∧ sn.t = d.t ∧ sn.ver = d.ver) ∧
  d.snap ∈ s.verified ∧ ∃ a ∈ s.approvals, a.1 = d.id ∧ a.2.1 ∈ E.approvers ∧ a.2.1 ≠ d.author`.

**Plain English.** Every destructive commit:
- affects ≤ R objects;
- has a snapshot of exactly the destroyed version, verified by a verifier id;
- has an approval by an approver id that is not the author.

No commit happens twice.

**Quantifier audit.** ∀ E and ops: writes and snapshots by anyone, verify and approve by any id. A verifier id
marking a snapshot "verified" is finding 1.

**Vacuity.** `honest_destructive_change`.\
**Gap to the manifest.** The wording matches. "Verified snapshot" means a `verify` operation by a verifier id, not a
restore test.

**Reviewer checklist:**
- [ ] Is "verified" intended to mean "restorable"? If so, that is a runtime premise.

## 11. SC-27 (chain) — `sc27_safe`

```
∀ E ops, Set.InjOn (chainHead E.H E.h0) {l | l ∈ s.accepted ∨ ∃ a ∈ s.anchors, a.2 = some l} →
  ∀ m ∈ s.accepted, ∃ a ∈ s.anchors, a.2 = some m
```

**Plain English.** If the chain head is injective on the lists in play, every accepted manifest is exactly a log the
witness anchored.

**Quantifier audit:**

| category | items |
|---|---|
| ∀ | E, ops: appends, rewrites, writer-published heads, **anchoring times**; the `anchor` operation takes no caller and is in the adversary's alphabet |
| hypothesis | `InjOn` |
| non-vacuity | `honest_accept`. |

**Gap to the manifest.** None found. The manifest and the header both state that evidence rewritten before anchoring
is accepted (`rewrite_before_anchor_window`), and that truth is not claimed.

**Reviewer checklist:**
- [ ] Is anchoring at adversary-chosen times the intended adversary? It makes the result weaker but honest.

## 12. F6 — `reserved_policy_bound`, `adaptive_recall_bound`, `damage_bound`

**Statements** (abridged; see raw for full binders):
```
reserved_policy_bound : ∀ {N} k Bh Bf, Bh ≤ N → ∀ σ, (∀ g, IsDist (σ g)) → ∀ φ, (∀ S h a, IsDist (φ S h a)) →
  ∑ S, pU N Bh S * val (reservedK Bf σ φ S) (successInd k S) N [] ≤ C(N−k, Bh) / C(N, Bh)
adaptive_recall_bound : … ∀ K σ, (∀ g, IsDist (σ g)) → (K ≥ 0) → (∑ K ≤ 1) →
  (∀ S h a, ∑ y, K S h (y, a, (), false) ≤ σ (visible h) a * (if S-round ∧ a then 1 − r else 1)) →
  ∑ S, pU N Bh S * val (K S) (recallSucc k) N [] ≤ hypMiss N Bh k r
damage_bound : … same premises … → ∀ D ≥ 0, ∀ dmg, (∀ t, dmg t ≤ D * ucX N t) →
  ∑ S, pU N Bh S * val (K S) dmg N [] ≤ D * ∑ j < N, hypMiss N Bh (j+1) r
```

**Definitions inlined:**
- `successInd k S t` is 1 iff ≥ k attack rounds, none in S, and no catch flag;
- `recallSucc k t` is 1 iff ≥ k attacks and no catch;
- `ucX N t` is the number of attacks before the first catch;
- `pU` is uniform over the Bh-subsets;
- `hypMiss N B k r = Σ_{j ≤ min k B} C(k,j)·C(N−k,B−j)/C(N,B)·(1−r)^j`.

**Plain English.** Against a hidden uniformly random reserved schedule, an attacker needing k uncaught attacks
succeeds with probability ≤ C(N−k,Bh)/C(N,Bh) (perfect recall), or ≤ hypMiss (recall ≥ r). Expected damage before
the first catch is ≤ D·Σ hypMiss.

**Quantifier audit:**

| category | items |
|---|---|
| ∀ | σ, the attacker's attack-bit law given the **visible history only** (attack bits and catch flags); φ, the flag law (may depend on S and the hidden history) |
| ∀ (`adaptive_recall_bound`, `damage_bound`) | any kernel K with the stated per-round non-catch bound |
| baked into types | the attacker never sees S, flags, timing or audit latency (σ's domain); damage stops at the first catch (`ucX`) |
| non-vacuity | `reserved_example`, `recall_example`, `example_r1`, `example_r_half`; the premises are satisfiable. |

**Gap to the prose** (STACK-MAP and the F6 headers):
1. "adversarially chosen false positives" is true of the flags' law, but the attacker cannot observe the flags;
2. "halt-on-catch" is an accounting convention in `ucX`, not a modelled HALT effect;
3. "per-history recall ≥ r" is the per-round hypothesis on K, which must hold for every history.

**Reviewer checklist:**
- [ ] Is "the attacker's information = attack bits + catch flags" stated wherever these bounds are quoted?
- [ ] Is the per-history recall premise ever claimed to be estimated from population ROC data?

## 13. F3 — `fenced_after_eps`, `landed_after_le`

```
fenced_after_eps : ∀ t0 ε e0 G (evs : List (ℕ × ℕ)), (∀ ev ∈ evs, ev.2 ≤ e0) →
  (sinkRun true t0 ε e0 G evs).countP (fun ev => t0 + ε ≤ ev.1) = 0
  accepts fence t0 ε e0 ev := !fence || ev.1 < t0 + ε || e0 + 1 ≤ ev.2
landed_after_le : ∀ n T t0 ρ Δ L e lat δ, Rate ρ e → HaltAbsorbs t0 δ e → Delivered n Δ δ → Latency L lat →
  landedAfter n T t0 e lat ≤ n * ρ * (L + Δ)
  landedAfter n T t0 e lat := Σ_{i<n} Σ_{t<T} (if t0 ≤ t + lat i t then e i t else 0)
```

**Plain English.** A fencing sink accepts nothing timestamped at or after t0 + ε when every event carries an epoch
≤ e0. Without fencing, the number of effects landing at or after t0 is ≤ n·ρ·(L + Δ).\
**Quantifier audit.** `fenced_after_eps`: ∀ event lists (any order, any timestamps); single hypothesis `HoldsOld`;
**definitional** (finding 8). `landed_after_le`: ∀ emission schedules, latencies and delays within the visible
hypotheses Rate, HaltAbsorbs, Delivered and Latency.

**Vacuity.** `example_fenced` and `example_unfenced` give numbers only. `partition_unbounded` and `token_leak` are
witnesses.\
**Gap to the prose:**
1. "independent of delivery" holds because delivery is absent from `fenced_after_eps`;
2. the timestamps `ev.1` are the sink's; nothing ties them to real time;
3. every effect must route through this one sink.

**Reviewer checklist:**
- [ ] Should `fenced_after_eps` be presented as a definition check rather than a result?
- [ ] Is `Delivered` (only `i < n`) consistent with `HaltAbsorbs` (all `i`)?

## 14. MonitorCollusion — `pass_transfer`, `collusion_uniform`

```
pass_transfer : ∀ Ph Pr β, IsDist Ph → IsDist Pr → (∀ v, 0 ≤ β v ≤ 1) → |passRate Pr β − passRate Ph β| ≤ tv Ph Pr
collusion_uniform : ∀ Ph Pr, IsDist Ph → IsDist Pr → ∀ δ, (∀ v, IsDist (δ v)) →
  Σ_φ ½ Σ_v (if φ then Pr v else Ph v) · Σ_a δ v a · [a = φ] ≤ (1 + tv Pr Ph)/2
```

**Plain English.** A monitor deciding from the view alone has a real-attack pass rate within TV of its honeypot
pass rate, and guesses the phase from one view with probability ≤ (1 + TV)/2.\
**Quantifier audit.** ∀ decision rules β and δ that are **functions of the view only**. Complete mediation of the view
is baked into the types.

**Vacuity.** `stego_fools_honeypots` shows the bound is tight; `phase_example` gives numbers.\
**Gap to the manifest** (SC-24: "with probability above (1+TV)/2, or … differs by more than TV"): this restates the
theorem (finding 10). Whether TV is small is the empirical question.

**Reviewer checklist:**
- [ ] Is "monitor sees only v" true in the deployment, including timestamps, ordering and metadata?

## 15. ChannelInstances — `gpu_bound`, `log_channel`, `sc02_accumulated`

```
gpu_bound : ∀ m ρ enc W dec, IsDist ρ → (∀ ω x h, IsDist (enc ω x h)) → (∀ s o, 0 ≤ W s o) → (∀ ω t, IsDist (dec ω t)) →
  E_ω[ |M|⁻¹ Σ_x val (gpuK enc W ω x) (dec · x) m ] ≤ (Σ_o max (W true o) (W false o))^m / |M|
  gpuK enc W ω m h z := enc ω m h z.1 * W z.1 z.2
log_channel : … K sub-distribution with visible output (Fin Kt × (Fin f → Fin Q)) … ≤ Kt^m · Q^(f·m) / |M|
sc02_accumulated : … ∀ K dominated by c with Σ_o c g o ≤ L |g| … ≤ (Π_{e<E} L e) / 2^k
```

**Plain English.** These bound exact recovery of a uniform secret through a two-state contention channel with a
fixed observation matrix W, through canonicalised log records, and through E rounds with certificate masses L.\
**Quantifier audit.** ∀ adaptive encoders and decoders with a shared seed. Baked into types: one sender bit per
quantum (`Bool`); `W` independent of history and time (no thermal or cache carry-over); `W` only non-negative, so an
estimated W must dominate the true one entrywise; the receiver sees only canonical fields (`log_channel`).

**Vacuity.** `gpu_example`, `log_example` and `sc02_example` are numerical evaluations of the bound, not
instantiations of a channel. The premises are trivially satisfiable (the c ≡ 1 certificate).\
**Gap to the prose.** "GPU channel" here means *this structural model*. Memory bandwidth, L2, power and multi-level
occupancy are excluded, as the header says.

**Reviewer checklist:**
- [ ] Will measured W be used as an upper envelope (entrywise upper confidence bounds), as `prereg/GPU1-*` proposes?

## 16. Core/Compose — `bridgeSpec`, `bridge_breaks_joint`

```
bridgeSpec : (S₁ : Spec G₁) → (S₂ : Spec G₂) → (b : St₁ → St₂ → St₂) → BridgeAdmissible S₁ S₂ b → Spec (withBridge G₁ G₂ b)
  BridgeAdmissible S₁ S₂ b := ∀ s₁ s₂, S₁.Inv s₁ → S₂.Inv s₂ → S₂.Inv (b s₁ s₂) ∧ G₂.effects s₂ <+: G₂.effects (b s₁ s₂)
bridge_breaks_joint : (toy flagGate/inertGate/flagDeputy) log = [inr 0] ∧ ¬ (all tags ok) ∧ ¬ BridgeAdmissible …
```

**Plain English.** A deputy that preserves G₂'s invariant and only appends to its log yields a joint gate spec; a
concrete non-admissible deputy breaks it.\
**Quantifier audit.** `bridgeSpec` is a `def`, so the result is that it type-checks. Its hypothesis is nearly its
conclusion. The negative result uses toy gates; the scenario instance is `DeputyBridge.payment_deputy_breaks_deploy_gate`.

**Reviewer checklist:**
- [ ] Is it clear in the prose that admissibility, which is the whole content, must be proved per deputy (as
      `admissible_of_step` does for gate-issued operations)?

---

## 17. Cross-cutting reviewer checklist (yes/no)

1. For each scenario, is "credential separation for every trusted role" listed in the manifest as an UNRESOLVED or
   ASSUMED premise (finding 1)?
2. Are the `full` flags that encode environment facts (finding 6) listed as premises in the correspondence files?
3. Does every manifest `bad_event` cite only properties that a cited theorem proves, with runtime-only rules (SC-26 c8)
   labelled as such?
4. For every digest-level theorem (SC-08, SC-16, SC-25, SC-27), is the collision premise stated where the prose says
   "exactly its content"?
5. Are role-disjointness hypotheses present wherever the prose says "independent" (SC-16, SC-17, SC-19, SC-25)?
6. Are the F2/F6 information premises baked into argument types (σ's domain, W's history-independence, the canonical
   view type) restated in plain words where the bounds are quoted?
7. Is every "independent of X" claim checked against whether X even appears in the statement (F3)?
8. Has a reviewer outside the author's model family read the elaborated statements in `raw/01-statements.out.txt`?
   (This packet does not count.)

**Suggested manifest edits** (for the owner; nothing changed here): SC-17 "…at an apply or after a reconcile";
SC-25 "…for exactly its content's digest"; SC-26 move "per invoice" to the runtime claim and cite
`sc26_safe_disjoint` for "non-agent"; SC-23 "…depend on a tool result through label-propagating derivations"; SC-16
add "(roles may overlap)" or a disjoint variant.
