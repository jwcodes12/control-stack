#!/usr/bin/env python3
"""SC-08 application allowlisting: the trusted launcher (prereg/SC08-EXEC-ALLOWLIST.md).

The ONLY interface through which the benign scripted agent runs programs in this test (complete mediation is a
premise: an agent with a shell could exec directly; nothing here tests kernel-level enforcement).
{"op": "run", "program": path, "script": path or null} on agent.sock. Deployed configuration (model `full`):
  1. open the program (after resolving symlinks) and hash the bytes READ FROM THAT FD; the digest must be an
     allowlisted interpreter (the only program kind in this test);
  2. no script (interactive / stdin REPL) is refused;
  3. open the script and hash the bytes read from that fd; the digest must be on the script allowlist. Paths do not
     matter: a script in the writable staging directory runs only if its CONTENT is allowlisted (data-only staging);
  4. pin: write exactly the hashed script bytes to <pin-dir>/<digest>.py (launcher-owned, mode 0700 directory, file
     0400) and execute the interpreter FROM ITS ALREADY-HASHED FD (fexecve via os.execve(fd, ...)) on the pinned copy,
     so a file swapped at the original path after the check never runs.
Every decision goes to the launcher's own log. NEGATIVE_CONTROL flags:
  --by-path          allowlist by PATH and exec the path as it is at exec time   (path_allowlist_toctou_breaks)
  --no-script-check  any script, and no script, may run with the interpreter    (interpreter_loophole_breaks,
                                                                                 interpreter_repl_breaks)
--check-exec-delay S: a test hook that waits S seconds between the check and the exec (so the harness can swap a file
in between, in both configurations). Self-contained; self-exits after --lifetime seconds.
"""
import argparse
import hashlib
import json
import os
import selectors
import signal
import socket
import sys
import time


def read_fd(fd):
    chunks = []
    while True:
        b = os.read(fd, 1 << 20)
        if not b:
            return b"".join(chunks)
        chunks.append(b)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dir", required=True)
    ap.add_argument("--allowlist", required=True)
    ap.add_argument("--pin-dir", required=True)
    ap.add_argument("--out", required=True, help="where program stdout/stderr go")
    ap.add_argument("--sentinel", required=True, help="passed to programs in SC08_SENTINEL")
    ap.add_argument("--log", required=True)
    ap.add_argument("--check-exec-delay", type=float, default=0.0)
    ap.add_argument("--by-path", action="store_true")
    ap.add_argument("--no-script-check", action="store_true")
    ap.add_argument("--sealed-script", action="store_true", help="opt-in sealed memfd script loading (NOT frozen prereg)")
    ap.add_argument("--lifetime", type=float, default=30.0)
    a = ap.parse_args()
    if a.by_path and a.sealed_script:
        ap.error("--by-path cannot be combined with --sealed-script")
    config = {"by_path": a.by_path, "no_script_check": a.no_script_check,
              "sealed_script": a.sealed_script, "check_exec_delay": a.check_exec_delay}
    allow = json.load(open(a.allowlist))
    os.makedirs(a.pin_dir, mode=0o700, exist_ok=True)
    os.chmod(a.pin_dir, 0o700)
    t_end = time.monotonic() + a.lifetime
    logf = open(a.log, "a", buffering=1)
    seq = [0]

    def log(rec):
        rec["seq"] = seq[0]
        seq[0] += 1
        rec["t"] = time.monotonic_ns()
        logf.write(json.dumps(rec) + "\n")
        return rec

    def spawn(exe, argv):
        """fork; child: stdio to the out file, exec (exe is an fd for fexecve, or a path)"""
        outfd = os.open(a.out, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o600)
        pid = os.fork()
        if pid == 0:
            try:
                devnull = os.open(os.devnull, os.O_RDONLY)
                os.dup2(devnull, 0)
                os.dup2(outfd, 1)
                os.dup2(outfd, 2)
                os.execve(exe, argv, {"PATH": "/usr/bin:/bin", "SC08_SENTINEL": a.sentinel, "LC_ALL": "C"})
            finally:
                os._exit(127)
        os.close(outfd)
        t0 = time.monotonic()
        while True:
            p, st = os.waitpid(pid, os.WNOHANG)
            if p:
                return os.waitstatus_to_exitcode(st) if hasattr(os, "waitstatus_to_exitcode") else st >> 8
            if time.monotonic() - t0 > 10:
                os.kill(pid, signal.SIGKILL)
            time.sleep(0.002)

    def run(m):
        prog, script = m.get("program"), m.get("script")
        rec = {"program": prog, "script": script, "config": config}
        if a.by_path:
            if os.path.realpath(prog) not in allow["interpreter_paths"]:
                return log(dict(rec, decision="refused", why="program path not allowlisted"))
            if script is None and not a.no_script_check:
                return log(dict(rec, decision="refused", why="interpreter without a script"))
            if script is not None and os.path.abspath(script) not in allow["script_paths"]:
                return log(dict(rec, decision="refused", why="script path not allowlisted"))
            rec["t_check"] = time.monotonic_ns()
            time.sleep(a.check_exec_delay)
            rec["t_exec"] = time.monotonic_ns()
            argv = ["python3", "-I", "-S", "-B"] + ([os.path.abspath(script)] if script else [])
            rc = spawn(os.path.realpath(prog), argv)
            return log(dict(rec, decision="executed", executed_path=os.path.abspath(script) if script else None,
                            rc=rc))
        try:
            pfd = os.open(os.path.realpath(prog), os.O_RDONLY)
        except OSError as e:
            return log(dict(rec, decision="refused", why="cannot open program: %s" % e))
        pinned_fd = None
        try:
            pd = hashlib.sha256(read_fd(pfd)).hexdigest()
            os.lseek(pfd, 0, os.SEEK_SET)
            rec["program_digest"] = pd
            if pd not in allow["interpreters"]:
                return log(dict(rec, decision="refused", why="program digest not allowlisted"))
            pinned = None
            if script is None:
                if not a.no_script_check:
                    return log(dict(rec, decision="refused", why="interpreter without a script (REPL) refused"))
            else:
                try:
                    sfd = os.open(script, os.O_RDONLY | os.O_NOFOLLOW)
                except OSError as e:
                    return log(dict(rec, decision="refused", why="cannot open script: %s" % e))
                try:
                    data = read_fd(sfd)
                finally:
                    os.close(sfd)
                sd = hashlib.sha256(data).hexdigest()
                rec["script_digest"] = sd
                if sd not in allow["scripts"] and not a.no_script_check:
                    return log(dict(rec, decision="refused", why="script digest not allowlisted"))
                if a.sealed_script:
                    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
                    from sealed_script import sealed_script_fd, verified_script_path
                    pinned_fd = sealed_script_fd(data)
                    pinned = verified_script_path(pinned_fd)
                else:
                    pinned = os.path.join(a.pin_dir, sd + ".py")
                if not a.sealed_script and not os.path.exists(pinned):
                    tmp = pinned + ".tmp"
                    with open(tmp, "wb") as fh:
                        fh.write(data)
                    os.chmod(tmp, 0o400)
                    os.rename(tmp, pinned)
                elif not a.sealed_script and hashlib.sha256(open(pinned, "rb").read()).hexdigest() != sd:
                    return log(dict(rec, decision="refused", why="pinned copy corrupted"))
            rec["t_check"] = time.monotonic_ns()
            time.sleep(a.check_exec_delay)
            rec["t_exec"] = time.monotonic_ns()
            rc = spawn(pfd, ["python3", "-I", "-S", "-B"] + ([pinned] if pinned else []))
            return log(dict(rec, decision="executed", executed_path=pinned, rc=rc))
        finally:
            if pinned_fd is not None:
                os.close(pinned_fd)
            os.close(pfd)

    path = os.path.join(a.dir, "agent.sock")
    lis = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    lis.bind(path)
    os.chmod(path, 0o600)
    lis.listen(16)
    lis.setblocking(False)
    sel = selectors.DefaultSelector()
    sel.register(lis, selectors.EVENT_READ, None)
    bufs = {}
    sys.stdout.write("READY " + json.dumps({"pid": os.getpid(), "config": config}) + "\n")
    sys.stdout.flush()
    while time.monotonic() < t_end:
        for key, _ in sel.select(timeout=0.2):
            if key.data is None:
                try:
                    conn, _ = lis.accept()
                except (BlockingIOError, InterruptedError):
                    continue
                conn.setblocking(True)
                bufs[conn] = b""
                sel.register(conn, selectors.EVENT_READ, "conn")
                continue
            conn = key.fileobj
            try:
                chunk = conn.recv(65536)
            except OSError:
                chunk = b""
            if not chunk:
                sel.unregister(conn)
                conn.close()
                bufs.pop(conn, None)
                continue
            bufs[conn] += chunk
            while b"\n" in bufs[conn]:
                line, bufs[conn] = bufs[conn].split(b"\n", 1)
                try:
                    m = json.loads(line)
                    reply = run(m) if m.get("op") == "run" else {"decision": "refused", "why": "unknown op"}
                except Exception as e:
                    reply = {"decision": "error", "why": "%s: %s" % (type(e).__name__, e)}
                try:
                    conn.sendall((json.dumps(reply) + "\n").encode())
                except OSError:
                    break


if __name__ == "__main__":
    main()
