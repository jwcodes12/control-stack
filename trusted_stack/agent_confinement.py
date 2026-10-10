"""Fail-closed Linux Landlock+seccomp confinement of one unprivileged agent process.

This is a scoped kernel-control profile, not universal effect mediation.
Never use it as a replacement for trusted host/VM isolation.
"""
from __future__ import annotations

import ctypes
import errno
import os
import platform
import resource
import socket
import stat
import sys
from pathlib import Path

_CREATE, _RESTRICT = 444, 446
_FS_MUTATIONS = sum(1 << b for b in (1, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14))
_DENY = (
    'socket socketpair connect bind listen accept accept4 sendto sendmsg sendmmsg '
    'recvmsg recvmmsg execve execveat fork vfork clone clone3 unshare setns '
    'mount umount2 pivot_root chroot ptrace process_vm_readv process_vm_writev '
    'pidfd_open pidfd_getfd pidfd_send_signal kill tkill tgkill rt_sigqueueinfo '
    'rt_tgsigqueueinfo io_uring_setup io_uring_enter io_uring_register '
    'userfaultfd bpf open_by_handle_at keyctl add_key request_key init_module '
    'finit_module delete_module shmget shmat shmctl semget semop semtimedop '
    'msgget msgsnd msgrcv msgctl chmod fchmod fchmodat fchmodat2 chown fchown '
    'lchown fchownat utime utimes futimesat utimensat setxattr lsetxattr '
    'fsetxattr removexattr lremovexattr fremovexattr'
).split()
_LIBC = ctypes.CDLL(None, use_errno=True)
_LIBC.syscall.restype = ctypes.c_long
_LIBC.prctl.restype = ctypes.c_int


class ConfinementUnavailable(RuntimeError):
    pass


def _syscall(num, *args):
    result = _LIBC.syscall(ctypes.c_long(num), *args)
    if result < 0:
        raise ConfinementUnavailable(f'kernel syscall {num} denied ({ctypes.get_errno()})')
    return result


def capability_probe():
    if platform.system() != 'Linux' or platform.machine() not in ('x86_64', 'aarch64'):
        raise ConfinementUnavailable('Linux x86_64/aarch64 only')
    abi = _syscall(_CREATE, ctypes.c_void_p(), ctypes.c_size_t(0), ctypes.c_uint(1))
    if abi < 3:
        raise ConfinementUnavailable('Landlock ABI 3+ required')
    try:
        lib = ctypes.CDLL('libseccomp.so.2', use_errno=True)
    except OSError as exc:
        raise ConfinementUnavailable('libseccomp missing') from exc
    return abi, lib


def _install_landlock():
    if _LIBC.prctl(ctypes.c_int(38), ctypes.c_ulong(1), 0, 0, 0):
        raise ConfinementUnavailable('PR_SET_NO_NEW_PRIVS failed')
    mask = ctypes.c_uint64(_FS_MUTATIONS)
    fd = _syscall(_CREATE, ctypes.byref(mask), ctypes.c_size_t(8), ctypes.c_uint(0))
    try:
        _syscall(_RESTRICT, ctypes.c_int(fd), ctypes.c_uint(0))
    finally:
        os.close(fd)


def _install_seccomp(lib):
    lib.seccomp_init.argtypes = [ctypes.c_uint32]
    lib.seccomp_init.restype = ctypes.c_void_p
    lib.seccomp_syscall_resolve_name.argtypes = [ctypes.c_char_p]
    lib.seccomp_syscall_resolve_name.restype = ctypes.c_int
    lib.seccomp_rule_add.argtypes = [ctypes.c_void_p, ctypes.c_uint32,
                                     ctypes.c_int, ctypes.c_uint32]
    lib.seccomp_rule_add.restype = ctypes.c_int
    lib.seccomp_load.argtypes = [ctypes.c_void_p]
    lib.seccomp_load.restype = ctypes.c_int
    lib.seccomp_release.argtypes = [ctypes.c_void_p]
    lib.seccomp_release.restype = None
    context = lib.seccomp_init(0x7FFF0000)
    if not context:
        raise ConfinementUnavailable('seccomp_init failed')
    try:
        for name in _DENY:
            num = lib.seccomp_syscall_resolve_name(name.encode('ascii'))
            if num < 0:
                continue
            code = lib.seccomp_rule_add(context, 0x00050000 | errno.EPERM, num, 0)
            if code:
                raise ConfinementUnavailable(f'seccomp rule {name} failed ({code})')
        code = lib.seccomp_load(context)
        if code:
            raise ConfinementUnavailable(f'seccomp_load failed ({code})')
    finally:
        lib.seccomp_release(context)


def _prepare_fds(keep):
    soft, _ = resource.getrlimit(resource.RLIMIT_NOFILE)
    if soft == resource.RLIM_INFINITY:
        soft = 1048576
    if 3 < keep:
        os.closerange(3, keep)
    os.closerange(keep + 1, soft)
    devnull = os.open('/dev/null', os.O_RDWR)
    try:
        for dest in (0, 1, 2):
            os.dup2(devnull, dest)
    finally:
        if devnull > 2:
            os.close(devnull)


def run_source(source: bytes, *, broker_socket: Path | None = None,
               broker_uid: int | None = None):
    if os.geteuid() == 0 or os.getuid() != os.geteuid():
        raise ConfinementUnavailable('separate non-root agent UID mandatory')
    if type(source) is not bytes or not source or len(source) > 1048576:
        raise ConfinementUnavailable('invalid source size')
    compiled = compile(source, '<confined-agent>', 'exec')
    _, seccomp = capability_probe()
    sock = None
    if broker_socket is not None:
        if type(broker_uid) is not int or broker_uid < 0 or broker_uid == os.geteuid():
            raise ConfinementUnavailable('distinct trusted broker UID mandatory')
        node = os.lstat(broker_socket)
        if not stat.S_ISSOCK(node.st_mode) or node.st_uid != broker_uid:
            raise ConfinementUnavailable('wrong broker socket owner/type')
        sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        sock.connect(str(broker_socket))
        import struct
        peer = sock.getsockopt(socket.SOL_SOCKET, socket.SO_PEERCRED, 12)
        if struct.unpack('3i', peer)[1] != broker_uid:
            raise ConfinementUnavailable('SO_PEERCRED broker mismatch')
        if sock.fileno() != 3:
            os.dup2(sock.fileno(), 3, inheritable=False)
            sock.close()
            sock = socket.socket(fileno=3)
    else:
        fd = os.open('/dev/null', os.O_RDONLY)
        if fd != 3:
            os.dup2(fd, 3, inheritable=False)
            os.close(fd)
    _prepare_fds(3)
    _install_landlock()
    _install_seccomp(seccomp)
    sys.dont_write_bytecode = True
    exec(compiled, {'__name__': '__confined_agent__', '__builtins__': __builtins__})


def main():
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('--script', type=Path, required=True)
    parser.add_argument('--broker-socket', type=Path)
    parser.add_argument('--broker-uid', type=int)
    parser.add_argument('--probe', action='store_true')
    args = parser.parse_args()
    if args.probe:
        abi, _ = capability_probe()
        print(f'landlock_abi={abi} libseccomp=present')
        return
    if (args.broker_socket is None) != (args.broker_uid is None):
        parser.error('broker socket and UID required together')
    try:
        run_source(args.script.read_bytes(), broker_socket=args.broker_socket,
                   broker_uid=args.broker_uid)
    except (ConfinementUnavailable, OSError, SyntaxError) as exc:
        print(f'DENIED: {exc}', file=sys.stderr)
        raise SystemExit(78)


if __name__ == '__main__':
    main()
