# English statements under test

### Claim 1
## `ControlStack.SC18Refinement.concrete_safe`

- **Says (plain English):** There is a concrete machine of the proxy and sink events (arrive, send, commit, ack, timeout, release, tick, ping, sink crash, sink restart) in its "real" setting (fail-open off, the `promptReply` scheduling flag on). For any T and any list of these events from the initial state: every released reply has its request id among the acknowledgements the proxy had read before replying (as seen through the abstraction into the variant model), the reply's clock is at most T past the clock of the last record acknowledgement, and no request id is replied to twice.
- **Under these hypotheses:** (a) the modelled machine's rules, including: an ack can only be read for a record already in the sink's durable (fsynced) log, so "ack means durable commit" is built in; there is a single sink and the sink's identity is not modelled; release needs that id's ack to have been read and no earlier reply; (b) in the `real` setting the release guard also requires that the reply happen within T ticks of reading that id's ack. This is the `promptReply` premise, which the real proxy does not check; the model refuses any release that would violate it, so the "within T" clause largely follows from this guard, not from the watchdog (the machine's release does not test the serving flag); (c) the abstraction: the variant model's last-ack time is the time of the last record ack, not pings; (d) no admin halts in the concrete machine (the transfer uses an empty admin list); (e) no config or tamper operations.
- **Does NOT say:** (1) It does not say the Python proxy implements this machine; the scenario's mapping marks that link as tested (`reconcile.py`), not proved. (2) It does not say that replies are prompt in reality: that is the premise `promptReply`, observed in the reference run but not enforced. (3) It does not cover config tampering, forged acks, adversarial clients, digest matching of the record to the body, latency or the single-release-path premise.
- **Kind:** refinement/bridge (forward simulation into `Resume`, then `Resume.resume_safe` transferred).

### Claim 2
## `ControlStack.SC18Refinement.concrete_durable`

- **Says (plain English):** For the same concrete machine in its `real` setting, from the initial state and any event list, every released reply satisfies three things: its request id is among the first r.llen acknowledgements the proxy had read (r.llen being the number read when it replied); that id is in the sink's fsynced record log; and its clock is at most T past the clock of the last record acknowledgement.
- **Under these hypotheses:** same as `concrete_safe` (including the `promptReply` guard in release and the rule that an ack is read only for a record already in the sink's log). The "in the sink log" part additionally uses the concrete machine's invariant that every release was preceded by a read ack and every read ack names a logged record, which is the modelled "the sink acks only after fsync".
- **Does NOT say:** (1) It does not say that the sink's fsynced log in the real system is durable or tamper-evident; "the sink log" is the model's list. (2) It does not say that the log is the trusted log in the sense of the configuration (the concrete machine has one sink and no configuration). (3) The timing clause is not independent evidence: it follows from the model's `promptReply` guard, which is a premise.
- **Kind:** refinement/bridge (corollary of `concrete_safe` plus the concrete invariant).

### Claim 3
## `ControlStack.SC19.sc19_safe`

- **Says (plain English):** In the model of production targets (each with a version, bumped by every write, and a size), snapshots (a copy of a target's version and size), verifiers and approvers, take the initial empty state with all checks on (fresh-snapshot, verified-snapshot, atomic count at commit, halt check), and run any list of operations (writes, snapshots, verifies, prepares, approves, commits, halts). Then for every destructive operation in the final record: the number of objects actually affected (the target's size at commit) is at most R; the snapshot it names is a snapshot of the same target with the same version as the version destroyed, and that snapshot has been marked verified by someone in the verifier list; there is an approval for that operation by someone in the approver list other than the operation's author; and no operation id appears twice in the destroyed list.
- **Under these hypotheses:** none on the trace; the environment (approver, verifier and admin lists, R) is arbitrary. In the model: callers are identified by the identity they claim (credential separation is a world assumption, not proved here); a "verify" operation just records a snapshot index (it is the "trusted verifier" assumption that this means a real restore test passed); every write bumps the target's version (hypothesis "versioned targets" is built into `write`; unversioned writes are not representable); destruction occurs only via `commit`; "author" is the claimed caller of the prepare operation.
- **Does NOT say:** (1) It does not say a verified snapshot can in fact be restored, or that any real restore test was run: "verified" means an index that a verifier-listed caller marked. (2) It does not say that approver and author are different people or agents, only different claimed identities; with unauthenticated claims an agent could use any identity. (3) It does not cover side effects outside versioned targets, downstream consumers, or the object count being the real blast radius.
- **Kind:** general theorem (invariant induction over arbitrary traces, including concurrent writes between prepare and commit).

### Claim 4
## `ControlStack.SC19.halt_freezes`

- **Says (plain English):** If the model state is halted, then running any list of operations under the deployed checks returns exactly the same state: nothing changes at all (no writes, snapshots, approvals or destructive commits).
- **Under these hypotheses:** the starting state has its halted flag set; no other condition (it need not be reachable). The halt check is on in `full`.
- **Does NOT say:** (1) In the model, even writes and snapshots are blocked by the halt; this is a model choice and does not say that a real halt stops writes by other writers to production. (2) It does not say the halt happens in time or that an admin who halts is genuine. (3) It says nothing about operations that happen outside the model.
- **Kind:** general theorem (simple induction; every operation is the identity on a halted state).

### Claim 5
## `ControlStack.AuthInstances.sc19_safe_authenticated`

- **Says (plain English):** Pair every operation with its true issuer; the gate applies an operation that claims an identity (verify, prepare, approve, halt each claim their caller; write, snapshot, commit claim none) only if the claimed identity is the true issuer. Suppose the adversary's issuer set U contains no approver and no verifier. Then, for any trace: (1) the `sc19_safe` conclusion holds for the authenticated run; (2) every approval recorded in the final state came from an operation in the trace whose issuer is an approver and is not in U; (3) every verified snapshot index was verified by an operation in the trace issued by a verifier not in U.
- **Under these hypotheses:** U disjoint from the approver list and from the verifier list (world assumption about what the adversary controls); the true issuer attached to each operation is the real principal (issuer authenticity, not proved here); the model's `claim19` mapping.
- **Does NOT say:** (1) Conjunct (1) does not use the hypotheses at all: it is `sc19_safe` applied to the authenticated sub-trace; the content added by authentication is conjuncts (2) and (3). (2) It does not say the approving or verifying principals are honest or careful, only that they are the listed principals and not the adversary's issuers; a genuine but deceived approver is not covered. (3) It does not say the platform really provides the true issuer, and writes, snapshots and commits are not authenticated (they claim no identity).
- **Kind:** refinement/bridge (`authRun_eq` reduction to `sc19_safe` plus the generic `issued_trusted` lemma applied to approvals and verifications).

### Claim 6
## `ControlStack.AuthInstances.forged19_destroys_without_auth`

- **Says (plain English):** A single example. Author 1 issues all of: write 5 objects to target 7, snapshot it, "verify" it claiming to be verifier 3, prepare a destruction, "approve" claiming to be approver 2, and commit. With approver 2, verifier 3, admin 9 and R = 10: if claims are not checked, the destruction commits (version 1, 5 objects, snapshot 0); with claims checked, nothing is destroyed.
- **Under these hypotheses:** only the concrete numbers in the statement. The "without authentication" run uses a claim function that claims nothing.
- **Does NOT say:** (1) It is not a general theorem. (2) It does not show that authentication in a real platform works. (3) It does not isolate which forged claim mattered (both the verify and the approve are forged, and either alone is enough to block the commit).
- **Kind:** negative control (shows a weakened model fails) (finite computation by `decide`).

### Claim 7
## `ControlStack.SC20.sc20_safe`

- **Says (plain English):** Take the initial empty state with all checks on (source check, quarantine of agent-written examples, re-check of digests at training time, halt check) and any list of operations (ingest from a source, agent write, edit, promote, freeze a manifest, train, halt). Then in every training run recorded, for every (example id, content used) entry: either the environment's registry maps that example id to exactly the digest of that content, or some promotion record for that example id with exactly that digest was made by a caller who is in the reviewer list.
- **Under these hypotheses:** none on the trace; the environment (allowlist, registry function, reviewer list, admin list and the digest function h) is arbitrary. In the model: callers are identified by their claimed identities (credential separation is a world assumption, not proved here); the registry is a fixed trusted function in the environment; ingestion is an environment event (it claims no identity) and takes the source on trust; training reads only through the modelled loader; the digest function is an arbitrary function (no injectivity or collision resistance is assumed), so everything is at the digest level.
- **Does NOT say:** (1) It does not say the trained data is clean or unpoisoned, and nothing about label correctness: the registry and reviewers are trusted by premise. (2) It does not state that the example's source is on the allowlist (the gate checks that before freezing, but the conclusion `Adm` only mentions the registry entry), and it does not state that the promoting reviewer differs from the writer (the gate enforces that when promoting, but the conclusion only says the promoter is in the reviewer list). The theorem is weaker than the scenario's bad-event wording on both counts. (3) It does not say that an example is unchanged after the freeze: it only says the digest of what was used is admitted; two different contents with the same digest are not distinguished, and no statement is made that the content equals the frozen one. Also a training run may be empty, in which case the claim is vacuous for that run.
- **Kind:** general theorem (invariant induction over arbitrary traces, including edits after freeze).

### Claim 8
## `ControlStack.SC20.halt_freezes`

- **Says (plain English):** If the state is halted, then any list of operations under the deployed checks returns exactly the same state: no ingestion, write, edit, promotion, freeze or training run changes anything.
- **Under these hypotheses:** the starting state is halted; no other condition (it need not be reachable). Halt check is on in `full`.
- **Does NOT say:** (1) In the model even ingestion, writes and edits are blocked by halt; that is a model choice, not a statement that real writers to the data store are stopped. (2) It does not say halting happens in time or that the admin who halts is genuine. (3) It does not say that earlier training runs were safe.
- **Kind:** general theorem (simple induction).

### Claim 9
## `ControlStack.AuthInstances.sc20_safe_authenticated`

- **Says (plain English):** Pair every operation with its true issuer; the gate applies an operation that claims an identity (agent write, promote, freeze, halt claim their caller; ingest, edit and train claim none) only if the claimed identity is the true issuer. Suppose the adversary's issuer set U contains no reviewer. Then for any trace: (1) the `sc20_safe` conclusion holds for the authenticated run; (2) every promotion record in the final state came from a promote operation in the trace issued by a reviewer who is not in U, for that example id and with that reviewer recorded.
- **Under these hypotheses:** U disjoint from the reviewer list (world assumption about what the adversary controls); the true issuer attached to each operation is the real principal (issuer authenticity, not proved); the model's `claim20` mapping.
- **Does NOT say:** (1) Conjunct (1) is `sc20_safe` applied to the authenticated sub-trace and does not use the hypothesis; the new content is conjunct (2). (2) It does not say the issuing reviewer reviewed the data or that reviewers are honest. (3) It inherits the weaknesses of `sc20_safe` (no allowlist, no writer-differs, no frozen-content claim in the conclusion), and ingestion and edits are unauthenticated environment/adversary events (they claim no identity), so the registry trust remains a premise.
- **Kind:** refinement/bridge (`authRun_eq` reduction to `sc20_safe` plus the generic `issued_trusted` lemma applied to promotions).

### Claim 10
## `ControlStack.AuthInstances.forged20_trains_without_auth`

- **Says (plain English):** A single example. Agent 1 issues all of: write an example (id 1, content 66), "promote" it claiming to be reviewer 2, "freeze" a manifest claiming to be admin 9, and train. With allowlist [50], reviewer 2, admin 9: if claims are not checked, a training run on the example (1, 66) occurs; with claims checked, no training run is recorded.
- **Under these hypotheses:** only the concrete environment of the statement (the SC-20 example environment with digest equal to content). The "without authentication" run uses a claim function that claims nothing.
- **Does NOT say:** (1) It is not a general theorem. (2) It does not isolate the promotion: with authentication both the forged promote and the forged freeze are refused, and the missing freeze alone already prevents training. (3) It does not show that a real platform authenticates identities.
- **Kind:** negative control (shows a weakened model fails) (finite computation by `decide`).
