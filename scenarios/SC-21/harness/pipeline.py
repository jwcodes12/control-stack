"""The SC-21 evaluation pipeline: an agent publishes N task results, possibly corrupting some; a trusted auditor
re-executes a hidden uniform sample of B tasks and flags mismatches. Standard library only.

Rounds are played in task order i = 0 .. N−1, as in `EvalIntegrityAdaptive` (the agent cannot reorder tasks):
  1. the agent decides whether to corrupt task i (attack bit). Its decision may use only its OWN history: earlier
     attack bits and earlier catch flags. The leak adversary also receives an explicit leaked bit about whether task
     i is in the hidden sample (a modelled side signal, NOT a real side channel);
  2. it publishes result(i) = true result, or true result + 1 if corrupted;
  3. if i is in the hidden sample S, the auditor RE-EXECUTES task i (`tasks.task`) and compares. A mismatch is
     detected with probability r (an independent auditor coin; r = 1 is deterministic detection). A detection is a
     catch flag, shown to the agent immediately (more than a real deployment shows it; still within the theorem's
     class).

Success events (exactly the theorems' events):
  hidden  (`survInd`):    the agent made >= k attacks and none of them is in S   (r = 1: bound C(N−k,B)/C(N,B))
  recall  (`recallSucc`): the agent made >= k attacks and was never caught        (bound hypMiss N B k r)

Separate RNG streams (agent, sample, audit coin, leak), each seeded from (master seed, configuration, stream), so the
sample is independent of the agent by construction.

Mutations (for H5; each must be caught by the corresponding pipeline check):
  no_reexec        the auditor compares the published value with itself instead of re-executing
  biased_sample    the auditor always samples tasks 0..B−1
  nondet_task      task results depend on a clock bit (re-execution is not deterministic)
"""
import random
import time

from tasks import task

ADVERSARIES = ("fixed", "pace", "burst", "leak")
MUTATIONS = (None, "no_reexec", "biased_sample", "nondet_task")


def task_nd(i):
    return task(i) + (time.perf_counter_ns() & 1)


class Fixed:
    """non-adaptive: a uniformly random set of k tasks chosen before the run (`sc21_undetected_prob`)"""

    def __init__(self, N, k, rng):
        self.chosen = set(rng.sample(range(N), k))

    def decide(self, i, attacks, catches, leak):
        return i in self.chosen


class Pace:
    """adaptive, own history only: attack with probability (k − attacks)/(N − i) until k attacks"""

    def __init__(self, N, k, rng):
        self.N, self.k, self.rng = N, k, rng

    def decide(self, i, attacks, catches, leak):
        rem = self.k - attacks
        return rem > 0 and self.rng.random() < rem / (self.N - i)


class Burst:
    """adaptive, uses catch feedback: attack with probability 0.3 per round while uncaught; after a catch, attack only
    when forced (remaining rounds = remaining attacks), so it still reaches k attacks"""

    def __init__(self, N, k, rng):
        self.N, self.k, self.rng = N, k, rng

    def decide(self, i, attacks, catches, leak):
        rem = self.k - attacks
        if rem <= 0:
            return False
        if self.N - i <= rem:
            return True
        return catches == 0 and self.rng.random() < 0.3


class Leak:
    """adaptive WITH a leak: corrupt task i iff the leaked bit says 'not sampled' (or when forced), until k attacks"""

    def __init__(self, N, k, rng):
        self.N, self.k = N, k

    def decide(self, i, attacks, catches, leak):
        rem = self.k - attacks
        if rem <= 0:
            return False
        return leak == 0 or self.N - i <= rem


POLICIES = {"fixed": Fixed, "pace": Pace, "burst": Burst, "leak": Leak}


def streams(seed, cfg):
    tag = "{}/{}".format(seed, cfg)
    return {s: random.Random("{}/{}".format(tag, s)) for s in ("agent", "sample", "audit", "leak")}


def run_config(N, B, k, r, adversary, trials, seed, q=0.0, mutation=None):
    """simulate `trials` independent runs of one configuration; returns counts"""
    if adversary not in POLICIES or mutation not in MUTATIONS:
        raise ValueError("unknown adversary or mutation")
    cfg = "N{}-B{}-k{}-r{}-{}-q{}-{}".format(N, B, k, r, adversary, q, mutation)
    rs = streams(seed, cfg)
    truth = [task(i) for i in range(N)]  # the agent's own (honest) results, computed once
    reexec = task_nd if mutation == "nondet_task" else task
    out = {"cfg": cfg, "N": N, "B": B, "k": k, "r": r, "adversary": adversary, "q": q, "mutation": mutation,
           "trials": trials, "seed": seed, "hidden_success": 0, "recall_success": 0, "reached_k": 0,
           "detection_violations": 0, "inclusion": [0] * N}
    for _ in range(trials):
        if mutation == "biased_sample":
            S = set(range(B))
        else:
            S = set(rs["sample"].sample(range(N), B))
        for i in S:
            out["inclusion"][i] += 1
        pol = POLICIES[adversary](N, k, rs["agent"])
        attacks, catches, attacked_in_S = 0, 0, False
        for i in range(N):
            leak = None
            if adversary == "leak":
                lr = rs["leak"]
                leak = (1 if i in S else 0) if lr.random() < q else (1 if lr.random() < B / N else 0)
            a = pol.decide(i, attacks, catches, leak)
            published = truth[i] + (1 if a else 0)
            if a:
                attacks += 1
            if i in S:
                if a:
                    attacked_in_S = True
                value = published if mutation == "no_reexec" else reexec(i)
                if value != published and (r >= 1 or rs["audit"].random() < r):
                    catches += 1
        if attacks >= k:
            out["reached_k"] += 1
            out["hidden_success"] += not attacked_in_S
            out["recall_success"] += catches == 0
        if r >= 1 and attacked_in_S and catches == 0:
            out["detection_violations"] += 1  # deterministic detection missed a sampled corruption
    return out


def determinism_check(N, mutation=None, repeats=3):
    """every task re-executes to the same value"""
    f = task_nd if mutation == "nondet_task" else task
    return all(len({f(i) for _ in range(repeats)}) == 1 for i in range(N))


def uniformity_check(counts, trials, N, B, z_crit):
    """per-task inclusion counts are consistent with B/N: max |z| <= z_crit (the caller sets z_crit by Bonferroni)"""
    p = B / N
    sd = (trials * p * (1 - p)) ** 0.5
    zmax = max(abs(c - trials * p) / sd for c in counts)
    return zmax <= z_crit, zmax
