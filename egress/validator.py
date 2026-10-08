"""Checks the ACTUAL namespace before relay/attacker exec, not a sibling namespace."""
import json
import os
from pathlib import Path
import stat


def inventory():
    fds = {}
    for p in Path('/proc/self/fd').iterdir():
        try: fds[p.name] = os.readlink(p)
        except FileNotFoundError: pass
    process_fds = {}
    for process in Path('/proc').iterdir():
        if not process.name.isdigit(): continue
        try:
            process_fds[process.name] = {fd.name:os.readlink(fd) for fd in (process/'fd').iterdir()}
        except FileNotFoundError: continue
        except PermissionError: raise RuntimeError('cannot inspect namespace process descriptors')
    return {'process_fds':process_fds,'netns':os.stat('/proc/self/ns/net').st_ino, 'pidns':os.stat('/proc/self/ns/pid').st_ino,
            'interfaces':Path('/proc/net/dev').read_text(), 'routes4':Path('/proc/net/route').read_text(),
            'routes6':Path('/proc/net/ipv6_route').read_text(), 'status':Path('/proc/self/status').read_text(),
            'mounts':Path('/proc/self/mountinfo').read_text(), 'fds':fds}


def validate(config, allow_missing_gateway=False):
    found = inventory(); errors = []
    if found['netns']==config['host_netns'] or found['pidns']==config['host_pidns']: errors.append('host namespace reused')
    interfaces = [line.split(':',1)[0].strip() for line in found['interfaces'].splitlines()[2:]]
    if interfaces!=['lo']: errors.append('external interface')
    if len(found['routes4'].splitlines())!=1: errors.append('IPv4 route present')
    for line in found['routes6'].splitlines():
        fields = line.split()
        if fields[-1]!='lo' or fields[4]!='0'*32 or fields[0] not in ('0'*31+'1','0'*32): errors.append('external IPv6 route')
    if any(v.startswith('socket:') for v in found['fds'].values()): errors.append('inherited socket descriptor')
    if any(v.startswith('socket:') for fds in found['process_fds'].values() for v in fds.values()): errors.append('inherited socket descriptor in namespace process')
    if set(found['fds'])-{'0','1','2'}: errors.append('stray descriptor')
    status = dict(line.split(':',1) for line in found['status'].splitlines() if ':' in line)
    if int(status['CapEff'].strip(),16) or int(status['CapBnd'].strip(),16): errors.append('capabilities retained')
    if status['NoNewPrivs'].strip()!='1': errors.append('no-new-privileges missing')
    mounts = {line.split()[4]:line.split()[5] for line in found['mounts'].splitlines()}
    allowed_mounts = {'/','/usr','/bin','/lib','/lib64','/proc','/proc/sysrq-trigger','/proc/irq','/proc/bus','/dev','/dev/null','/dev/zero','/dev/full','/dev/random','/dev/urandom','/dev/tty','/dev/pts','/tmp','/run','/suite','/suite-config.json','/run/egress.sock'}
    if set(mounts)-allowed_mounts: errors.append('unexpected mount authority')
    for path in ('/usr','/bin','/lib','/lib64'):
        if path in mounts and 'ro' not in mounts[path].split(','): errors.append('system runtime writable')
    if 'ro' not in mounts.get('/suite','').split(','): errors.append('gateway/validator code writable')
    if 'ro' not in mounts.get('/suite-config.json','').split(','): errors.append('launch contract writable')
    if Path(config['policy_path']).exists(): errors.append('host policy visible')
    paths = list(Path('/run').iterdir())
    if any(p.name!='egress.sock' for p in paths): errors.append('unexpected /run authority')
    if not allow_missing_gateway:
        sock = Path('/run/egress.sock')
        if not sock.exists() or not stat.S_ISSOCK(sock.stat().st_mode): errors.append('gateway unavailable')
    for path in ('/run/docker.sock','/var/run/docker.sock','/run/containerd/containerd.sock','/run/dbus/system_bus_socket'):
        if Path(path).exists(): errors.append('host control socket visible')
    if errors: raise RuntimeError('topology rejected: '+', '.join(errors))
    return found
