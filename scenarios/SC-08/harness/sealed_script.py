#!/usr/bin/env python3
"""Linux sealed-memory executable-script object, for an opt-in SC-08 reference mode.

A trusted launcher hashes its verified bytes and writes exactly those bytes to a
memfd. Kernel F_SEAL_WRITE/GROW/SHRINK/SEAL then forbids mutation, even by a
same-UID peer with access to the file descriptor. The interpreter must consume
/proc/self/fd/<fd> with this fd held open across exec.

NOT an OS-wide exec gate. A same-UID process that can ptrace the launcher, steal
its FDs before sealing, or bypass it entirely is outside this narrow property.
"""
import fcntl
import os


class SealedScriptUnavailable(RuntimeError):
    pass


def _requirements():
    needed = ("memfd_create", "MFD_ALLOW_SEALING")
    if any(not hasattr(os, x) for x in needed):
        raise SealedScriptUnavailable("Linux memfd sealing unavailable")
    if any(not hasattr(fcntl, x) for x in
           ("F_ADD_SEALS", "F_GET_SEALS", "F_SEAL_SEAL", "F_SEAL_SHRINK",
            "F_SEAL_GROW", "F_SEAL_WRITE")):
        raise SealedScriptUnavailable("Linux F_ADD_SEALS constants unavailable")


def sealed_script_fd(data):
    """Return readable, inheritable *sealed* memfd holding precisely data.

    Caller must close the returned descriptor after its interpreter child exits.
    The caller must not fall back to an unsealed writable copy.
    """
    _requirements()
    if not isinstance(data, bytes):
        raise TypeError("expected verified bytes")
    fd = os.memfd_create("sc08-verified-script", flags=os.MFD_ALLOW_SEALING)
    try:
        view = memoryview(data)
        while len(view):
            n = os.write(fd, view)
            if n <= 0:
                raise OSError("short or failed memfd write")
            view = view[n:]
        os.lseek(fd, 0, os.SEEK_SET)
        seals = (fcntl.F_SEAL_WRITE | fcntl.F_SEAL_GROW |
                 fcntl.F_SEAL_SHRINK | fcntl.F_SEAL_SEAL)
        fcntl.fcntl(fd, fcntl.F_ADD_SEALS, seals)
        if fcntl.fcntl(fd, fcntl.F_GET_SEALS) & seals != seals:
            raise SealedScriptUnavailable("kernel did not apply all seals")
        os.set_inheritable(fd, True)
        return fd
    except BaseException:
        os.close(fd)
        raise


def verified_script_path(fd):
    """Interpreter path valid only while the sealed fd stays open in child."""
    return "/proc/self/fd/%d" % fd
