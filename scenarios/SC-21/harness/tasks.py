"""N deterministic evaluation tasks for the SC-21 sampling validation (standard library only).

Task i is a tiny, fully deterministic "evaluation": a seeded 64-bit LCG stream of 64 points is scored by a fixed rule
and the score (0..64) is the task's result. Re-executing a task always gives the same result (checked by
`pipeline.determinism_check`). Each call does a few hundred integer operations, so the auditor genuinely re-executes
instead of looking up a cached value.
"""
import hashlib

TASK_SEED = 2121


def task(i, seed=TASK_SEED):
    h = hashlib.sha256("sc21/{}/{}".format(seed, i).encode()).digest()
    x = int.from_bytes(h[:8], "big")
    score = 0
    for _ in range(64):
        x = (6364136223846793005 * x + 1442695040888963407) % 18446744073709551616
        a, b = (x >> 33) % 1000, (x >> 13) % 1000
        score += 1 if (3 * a + 7 * b) % 11 < 5 else 0
    return score
