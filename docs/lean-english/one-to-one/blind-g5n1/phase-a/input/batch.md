# English statements under test

### Claim 1
## `ControlStack.EvalIntegrity.sc21_safe`

- **Says (plain English):** Start from an empty state and apply any list of operations (report a result for a task with a claimed value and an evaluator digest, re-execute a task, attempt to publish, halt) under the full set of checks. Then every record that was published (a snapshot of the results log plus the list of tasks re-executed so far) satisfies three things: every task on the frozen task list has a result in the snapshot; every result in the snapshot carries the frozen evaluator's digest; and every result in the snapshot whose task had been re-executed by then holds the true value for that task.
- **Under these hypotheses:** The environment (task list, a truth function, a frozen digest, a list of admin ids) is arbitrary but fixed. The "full" checks are all on: the results log is append-only (a second report for the same task is ignored), publication requires that every task has a result, that every stored result has the frozen digest, and that no flag has ever been raised, and re-executing a task compares the stored value to the environment's truth function and raises a permanent flag on mismatch. World assumptions, not provable in Lean: the digest attached to a report is honest (in the model it is just a number supplied with the `report` operation; nothing ties it to the evaluator actually run); re-execution returns the model's truth value (deterministic re-execution); the re-execution and publish operations are performed by an executor and publisher independent of the agent.
- **Does NOT say:** (a) That corrupted results are caught: the trace decides which tasks (if any) are re-executed, so a trace that re-executes nothing publishes unchecked values. How likely a hidden sample is to catch corruption is a different model (the sampling theorems). (b) That tasks and evaluator measure the intended capability, or that the digest equals the evaluator that actually ran. (c) Anything about values of results for tasks that were not re-executed.
- **Kind:** general theorem (induction over traces; the safety statement is an invariant of the model).

### Claim 2
## `ControlStack.EvalIntegrity.sc21_undetected_prob`

- **Says (plain English):** Fix N reported values and their N true values. Call a result "corrupted" if reported and true values differ; suppose exactly k are corrupted. If the re-execution sample is a uniformly random subset of size B of the N results (every size-B subset equally likely), and re-execution flags any sampled corrupted result, then the fraction of samples that flag nothing is exactly C(N−k,B) divided by C(N,B).
- **Under these hypotheses:** The number of corrupted results is exactly k. "Undetected" is defined in the model as: the sample is disjoint from the corrupted set (so perfect, deterministic detection of any sampled corrupted result is built into the definition). The corrupted set is fixed before the sample is drawn (non-adaptive). World assumptions: the sample is hidden from the agent until after publication; re-execution is deterministic with zero false negatives.
- **Does NOT say:** (a) That the escape probability is small: it is an exact value, which is large when B is small relative to N or k is small (N=100, B=10, k=5 gives about 0.584; k=1 gives 0.9). (b) Anything about an agent that chooses what to corrupt after seeing information about the sample, or adaptively (see `sc21_adaptive*`). (c) Anything about imperfect detection when sampled.
- **Kind:** general theorem (exact counting identity, reusing the `AuditBudget` counting lemma). Note the scenario text says "escapes with probability above" the quantity; this theorem is an equality, so the stated bound is attained, not merely upper.

### Claim 3
## `ControlStack.EvalIntegrity.sc21_undetected_le_pow`

- **Says (plain English):** Under the same setup as `sc21_undetected_prob`, with N positive and B at most N, the probability that a uniformly random hidden size-B sample misses all k corrupted results is at most ((N−B)/N) raised to the power k. In words: drawing the sample without replacement is no worse for the defender than checking each corrupted result independently with probability B/N.
- **Under these hypotheses:** N > 0; B ≤ N; exactly k corrupted results (k ≤ N follows from this). Same world assumptions as above (hidden sample, deterministic perfect re-execution).
- **Does NOT say:** That the bound is small (it is about 0.59 for N=100, B=10, k=5); that the corrupted set may be chosen with knowledge of the sample; anything about imperfect recall.
- **Kind:** general theorem (an inequality between the exact binomial ratio and a power).

### Claim 4
## `ControlStack.EvalIntegrity.observable_sample_nogo`

- **Says (plain English):** If the replication sample S (size B among N findings) is known to the agent in advance and k ≤ N−B, there exist k findings outside S that the agent can misreport and the survival probability against the known schedule is exactly 1.
- **Under these hypotheses:** S has B elements; k ≤ N−B. The schedule family is the single fixed set S. For SC-22 it is the statement that, if the replication sample is not hidden, the misreport bound gives no protection.
- **Does NOT say:** How the agent would learn S, or anything about a hidden sample.
- **Kind:** negative control (shows the sample_hidden assumption is load-bearing); the proof is a cardinality argument.

### Claim 5
## `ControlStack.EvalIntegrityAdaptive.sc21_adaptive`

- **Says (plain English):** Tasks are processed in a fixed order as N rounds. In each round the agent decides (possibly at random, and possibly depending on all its own earlier decisions and on the "caught" flags of earlier rounds) whether to corrupt that task's result. A catch flag is raised exactly when the agent corrupts a task that lies in the hidden random re-execution sample S (S uniform over all size-B subsets). The statement: for every such adaptive decision rule, the probability (averaged over the random S) that the agent corrupts at least k tasks and none of the corrupted ones is in S is at most C(N−k,B)/C(N,B). That is the same number as the non-adaptive case, so adaptivity gains nothing.
- **Under these hypotheses:** B ≤ N. The decision rule σ is any function from the visible history (the agent's own earlier corruption bits and the catch flags) to a probability distribution over {corrupt, not corrupt}. Success of the agent is defined as: at least k corruptions and no corrupted round in S. World assumptions, not provable: the real agent learns nothing about S except through catch flags (no timing, side-channel or other leak); detection is deterministic whenever a corrupted task is sampled; tasks are processed in a fixed order the agent cannot change.
- **Does NOT say:** (a) That a real agent sees this much or this little: it is a model of the interface (rounds, bits, flags). (b) Anything when the sample leaks (`leaked_sample_survives` shows survival 1 then). (c) That the bound is small: it is the same number as in the non-adaptive case (about 0.584 for N=100, B=10, k=5). (d) Anything about imperfect detection (see `sc21_adaptive_recall`).
- **Kind:** general theorem (an instance of the F6 hidden-schedule audit theorem `Leakage.audit_adaptive_hidden`).

### Claim 6
## `ControlStack.EvalIntegrityAdaptive.sc21_adaptive_content`

- **Says (plain English):** The same bound as `sc21_adaptive` for a richer model in which each round also has an arbitrary hidden component (task content, monitor flags, extra checks, even checks that depend on the sample S) and an arbitrary joint law with the visible output. The only restriction on the agent is that, for every sample S in the allowed family, every history and each corruption choice a, the probability that the agent makes choice a (summed over all hidden parts and all catch flags) is at most σ(visible history)(a) for some decision rule σ that does not see S. Then the probability, averaged over a uniformly random S, of the event "at least k corruptions, none in S, and no catch flag ever raised by any source" is at most C(N−k,B)/C(N,B).
- **Under these hypotheses:** B ≤ N; the round kernel K is non-negative and sums to at most 1 on each history for every size-B S; the agent's corruption choice has marginal probability bounded above by a rule σ of the visible history only (this is the "no leak about S" assumption, expressed as a hypothesis); σ is a distribution at every history. Success of the agent is defined as having no corrupted round in S and no catch flag at all, so detection of a sampled corrupted task and the effect of the extra checks are built into the definition of the event, not derived. World assumptions: the agent's behaviour really is a function of the visible history only (sample hidden, no side channel); extra checks only add catches.
- **Does NOT say:** That any particular extra check exists or is effective (extra checks can only lower the success probability, never raise it, in this statement); that task content cannot reveal S (the hypothesis on the marginal says it does not, but nothing proves that in a real system).
- **Kind:** general theorem (instance of `ReservedAudit.reserved_adaptive`). Largely a generalisation of the previous theorem; the substantive content is that hidden state does not help the agent provided the leak hypothesis holds.

### Claim 7
## `ControlStack.EvalIntegrityAdaptive.sc21_adaptive_recall`

- **Says (plain English):** Same setup as `sc21_adaptive_content`, but re-execution may miss: whenever a round is in the sample and the agent corrupted it, the probability of no catch in that round is at most (1−r), where r is the per-history recall (r between 0 and 1). Then the probability, averaged over the hidden uniform sample, that the agent corrupts at least k results and is never caught (by anything) is at most `hypMiss N B k r`, which is the hypergeometric sum: over j from 0 to min(k,B) of C(k,j)·C(N−k,B−j)/C(N,B) times (1−r)^j. That is the exact escape probability of a fixed k-set against a random sample with recall r.
- **Under these hypotheses:** B ≤ N; 0 ≤ r ≤ 1; the same kernel conditions as `sc21_adaptive_content`; an additional per-history condition `hrec` that bounds the joint probability of "agent makes choice a and no catch flag this round" by σ(visible history)(a) times (1−r) when the round is in S and a means corrupting, else times 1. World assumptions: the recall lower bound r holds on every history (re-execution of a corrupted sampled task is detected with probability at least r, with detection events handled history by history), the sample is hidden, no leak about S beyond catch flags.
- **Does NOT say:** That r is any particular value (r is a parameter); that detection events are independent across tasks beyond what `hrec` says; that undetected corruption would be actually harmless or that the number is small (with r = 1/2 and N=100, B=10, k=5 the bound in `ReservedRecall.recall_example` is about 0.79).
- **Kind:** general theorem (instance of `ReservedRecall.adaptive_recall_bound`).

### Claim 8
## `ControlStack.EvalIntegrity.sc22_unreplicated_misreport`

- **Says (plain English):** Fix N reported findings (as numbers) and N true values. Suppose exactly k reported values differ from their true values. If the replication sample is a uniformly random hidden subset of B of the N findings, and replication flags any sampled finding whose reported value differs from the truth, the probability that nothing is flagged is exactly C(N−k,B)/C(N,B).
- **Under these hypotheses:** Exactly k misreported findings; the misreported set is fixed before the sample is drawn; detection when sampled is perfect and deterministic (built into the definition of "undetected" as "sample disjoint from the misreported set"). It is literally the same statement as `sc21_undetected_prob`, proved by invoking it. World assumptions: the sample is hidden until after reporting; replication detects a misreport whenever it is sampled.
- **Does NOT say:** That a reproduced number is correctly interpreted (the docstring states that replication checks numerical reproducibility under the frozen pipeline, not interpretation); that the probability is small; anything about adaptive misreporters or imperfect replication. The word "findings" is only a relabelling of "results": the statement is about numbers, not scientific claims.
- **Kind:** definitional/trivial (a renaming of `sc21_undetected_prob`; the proof is one application of it). The underlying counting identity is nontrivial but standard.

### Claim 9
## `ControlStack.SC23.sc23_safe`

- **Says (plain English):** After any sequence of operations from the empty state (user inputs, tool results, derivations with arbitrary content from arbitrary stored values, confirmations by any caller number, sensitive or non-sensitive actions with any arguments), every executed action whose tool is on the sensitive list and whose arguments truly depend on a tool result (the ghost provenance bit is true) has a recorded user confirmation with the same tool and exactly the same argument values, made by a caller on the user list. Also, no confirmation is used by more than one executed action.
- **Under these hypotheses:** All checks on ("full"): a derived value is labelled tainted iff some source is; an action on a sensitive tool with any tainted-labelled argument needs a confirmation whose tool matches, whose values equal the resolved argument values exactly, and whose nonce has not been used; only callers in the user list may confirm. In this model "provenance" is not independent ground truth: the ghost bit is computed by the same operation rules (tool results are provenance-true, user inputs false, derived = any source true). World assumptions: that the only way untrusted content enters the system is through the model's tool-result operation, and that a derivation never takes untrusted content as input except through its listed sources (provenance_truthful); that confirmations are issued only by real users (credential separation) and the confirmation UI shows exact values.
- **Does NOT say:** (a) That laundering is impossible in practice. In this model a derivation with an empty source list yields an untainted value of arbitrary content, so a planner that copies injected text into such a derivation bypasses the check; the header excludes this by premise. (b) That a user's confirmation is wise, or that untainted values are correct. (c) Anything about non-sensitive tools. (d) That the user-input operation is by a real user: in this model it carries no caller at all.
- **Kind:** general theorem (inductive invariant over all traces, with label = provenance as the key invariant).

### Claim 10
## `ControlStack.SC23.halt_freezes`

- **Says (plain English):** If the model's state is already marked halted, then running any further list of operations leaves the state exactly unchanged: no new values, confirmations, or executed actions appear.
- **Under these hypotheses:** The halted flag is true in the starting state, under the full checks (the halt check is on). The flag is set only by a halt operation whose caller number is in the admin list.
- **Does NOT say:** That a halt ever happens, that it happens in time, or that the halt caller is a real administrator (credential separation is a premise); that actions already executed before the halt are undone.
- **Kind:** general theorem (the sticky halt bit makes every operation the identity; close to definitional by construction).
