"""Fail-closed, test-only bubblewrap launcher. Does not modify host sandbox settings."""
import os
from pathlib import Path
import subprocess
import sys


def command(code, config, gateway_socket, arguments, shared_net=False):
    cmd = ['bwrap','--unshare-all','--die-with-parent','--new-session','--cap-drop','ALL','--clearenv',
           '--setenv','PATH','/usr/bin:/bin','--setenv','PYTHONDONTWRITEBYTECODE','1']
    # Fault injection only, exposed by the disposable harness, never by the CLI.
    if shared_net: cmd += ['--share-net']
    for path in ('/usr','/bin','/lib','/lib64'):
        if Path(path).exists(): cmd += ['--ro-bind',path,path]
    cmd += ['--dir','/etc','--proc','/proc','--dev','/dev','--tmpfs','/tmp','--tmpfs','/run',
            '--ro-bind',str(code),'/suite','--ro-bind',str(config),'/suite-config.json']
    if Path(gateway_socket).exists(): cmd += ['--ro-bind',str(gateway_socket),'/run/egress.sock']
    cmd += ['/usr/bin/python3','/suite/sandbox_entry.py',*arguments]
    return cmd


if __name__=='__main__':
    if len(sys.argv)<5: sys.exit('usage: launcher.py CODE_DIR CONFIG_JSON SOCKET CASE')
    result = subprocess.run(command(Path(sys.argv[1]).resolve(),Path(sys.argv[2]).resolve(),sys.argv[3],sys.argv[4:]),close_fds=True)
    sys.exit(result.returncode)
