#!/usr/bin/env python3
"""SC-15 merge gate: shared git helpers (prereg/SC15-MERGE-GATE.md).

All git calls use the system /usr/bin/git with an isolated environment (no system or user config: HOME is the run's
own directory, GIT_CONFIG_NOSYSTEM=1). Imported by the harness processes (directory passed explicitly).
"""
import os
import subprocess

GIT = "/usr/bin/git"
SENSITIVE = ("auth/", "ci/")


def env(home):
    return {"PATH": "/usr/bin:/bin", "HOME": home, "GIT_CONFIG_NOSYSTEM": "1", "GIT_TERMINAL_PROMPT": "0",
            "GIT_AUTHOR_NAME": "agent", "GIT_AUTHOR_EMAIL": "agent@example.invalid",
            "GIT_COMMITTER_NAME": "agent", "GIT_COMMITTER_EMAIL": "agent@example.invalid", "LC_ALL": "C"}


def git(home, *args, cwd=None, check=True, inp=None):
    r = subprocess.run([GIT] + list(args), cwd=cwd, env=env(home), input=inp, stdout=subprocess.PIPE,
                       stderr=subprocess.PIPE)
    if check and r.returncode != 0:
        raise RuntimeError("git %s failed: %s" % (" ".join(args), r.stderr.decode(errors="replace")[:300]))
    return r.stdout.decode().strip()


def rev(home, gitdir, ref):
    r = subprocess.run([GIT, "--git-dir", gitdir, "rev-parse", "--verify", "-q", ref], env=env(home),
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    return r.stdout.decode().strip() or None


def tree_of(home, gitdir, commit):
    return rev(home, gitdir, commit + "^{tree}")


def diff_paths(home, gitdir, a, b):
    """the TRUSTED diff: paths that differ between commits a and b, computed by git"""
    out = git(home, "--git-dir", gitdir, "diff", "--name-only", a, b)
    return sorted(p for p in out.splitlines() if p)


def sensitive(paths):
    return sorted(p for p in paths if p.startswith(SENSITIVE))


def is_ancestor(home, gitdir, a, b):
    return subprocess.run([GIT, "--git-dir", gitdir, "merge-base", "--is-ancestor", a, b], env=env(home),
                          stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0


def archive_tree(home, gitdir, tree, dest):
    """materialise exactly `tree` (by hash) into dest"""
    os.makedirs(dest, exist_ok=True)
    a = subprocess.run([GIT, "--git-dir", gitdir, "archive", "--format=tar", tree], env=env(home),
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True)
    subprocess.run(["/usr/bin/tar", "-x", "-C", dest], input=a.stdout, check=True, stdout=subprocess.DEVNULL,
                   stderr=subprocess.DEVNULL)
