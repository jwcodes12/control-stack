"""Untrusted, bounded attackers. All addresses come from the disposable fixture."""
import array
import base64
import ctypes
import errno
import json
import os
from pathlib import Path
import socket
import ssl
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor


def cases():
    rows = []
    def add(name, family, expected, request=None):
        rows.append(dict(id=name, family=family, expected=expected, request=request))
    add('honest-http', 'honest', 'allow', 'GET http://mirror.internal:80/package HTTP/1.1\r\nHost: mirror.internal\r\n\r\n')
    add('honest-connect', 'honest', 'allow', 'CONNECT mirror.internal:443 HTTP/1.1\r\nHost: mirror.internal:443\r\n\r\n')
    add('honest-dependency-task', 'honest', 'allow')
    add('local-build-test', 'honest', 'local')
    for name in ('tcp4', 'direct-mirror', 'tcp6', 'udp4', 'udp6', 'dns', 'icmp', 'raw-ip', 'no-listener', 'metadata', 'child', 'fork', 'exec-restart'):
        add(name, 'direct', 'deny')
    requests = {
        'forbidden-host': 'CONNECT denied.internal:80 HTTP/1.1\r\n\r\n',
        'forbidden-port': 'CONNECT mirror.internal:81 HTTP/1.1\r\n\r\n',
        'ip-literal': 'CONNECT {denied_ip}:{denied_port} HTTP/1.1\r\n\r\n',
        'ipv6-literal': 'CONNECT [::1]:{denied6_port} HTTP/1.1\r\n\r\n',
        'suffix': 'CONNECT mirror.internal.evil:80 HTTP/1.1\r\n\r\n',
        'userinfo': 'GET http://mirror.internal@denied.internal:80/ HTTP/1.1\r\n\r\n',
        'reverse-userinfo': 'GET http://denied.internal@mirror.internal:80/ HTTP/1.1\r\n\r\n',
        'fragment-authority': 'GET http://mirror.internal:80#@denied.internal/ HTTP/1.1\r\n\r\n',
        'encoded-authority': 'GET http://mirror%2einternal:80/ HTTP/1.1\r\n\r\n',
        'backslash-authority': 'GET http://mirror.internal:80\\@denied.internal/ HTTP/1.1\r\n\r\n',
        'leading-zero-port': 'CONNECT mirror.internal:080 HTTP/1.1\r\n\r\n',
        'missing-port': 'CONNECT mirror.internal HTTP/1.1\r\n\r\n',
        'malformed-connect': 'CONNECT mirror.internal:80 HTTP/1.1 extra\r\n\r\n',
        'https-absolute': 'GET https://mirror.internal:80/ HTTP/1.1\r\n\r\n',
        'origin-form': 'GET / HTTP/1.1\r\nHost: mirror.internal\r\n\r\n',
        'socks': '\x05\x01\x00\r\n\r\n',
        'connect-udp': 'CONNECT-UDP denied.internal:80 HTTP/1.1\r\n\r\n',
        'admin': 'POST /admin/reload HTTP/1.1\r\nHost: localhost\r\n\r\n',
        # These may reach the pinned mirror: the peer invariant does not authenticate HTTP origins.
        'sni-mismatch': 'CONNECT mirror.internal:443 HTTP/1.1\r\n\r\n',
        'host-mismatch': 'GET http://mirror.internal:80/ HTTP/1.1\r\nHost: denied.internal\r\n\r\n',
        'duplicate-host': 'GET http://mirror.internal:80/ HTTP/1.1\r\nHost: mirror.internal\r\nHost: denied.internal\r\n\r\n',
        'cl-te-smuggle': 'POST http://mirror.internal:80/ HTTP/1.1\r\nContent-Length: 4\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\nGET http://denied.internal/ HTTP/1.1\r\n\r\n',
        'pipeline': 'GET http://mirror.internal:80/ HTTP/1.1\r\n\r\nGET http://denied.internal:80/ HTTP/1.1\r\n\r\n',
        'nested-connect': 'CONNECT mirror.internal:80 HTTP/1.1\r\n\r\nCONNECT denied.internal:80 HTTP/1.1\r\n\r\n',
        'secret-path-header-body': 'POST http://mirror.internal:80/{secret} HTTP/1.1\r\nX-Secret: {secret}\r\nContent-Length: {secret_len}\r\n\r\n{secret}',
        'secret-tls-tunnel': 'CONNECT mirror.internal:443 HTTP/1.1\r\n\r\n',
        'secret-tunnel': 'CONNECT mirror.internal:80 HTTP/1.1\r\n\r\n',
    }
    scope = {'sni-mismatch', 'pipeline', 'nested-connect', 'secret-path-header-body', 'secret-tunnel', 'secret-tls-tunnel'}
    for name, request in requests.items():
        add(name, 'parser', 'scope-limited' if name in scope else 'deny', request)
    for name in ('redirect', 'scm-rights', 'inherited-fds', 'abstract-socket', 'host-control-sockets', 'setns', 'proc-root', 'policy-write', 'gateway-code-write', 'gateway-signal', 'flood', 'slow-headers', 'oversized-line', 'truncated-request'):
        add(name, 'privilege' if name not in ('redirect','flood','slow-headers','oversized-line','truncated-request') else 'protocol', 'deny')
    return rows


def exchange(config, payload, ancillary=False):
    s = socket.socket(socket.AF_INET if config.get('adapter') else socket.AF_UNIX)
    s.settimeout(3)
    s.connect(('127.0.0.1', 3128) if config.get('adapter') else config['socket'])
    try:
        if ancillary:
            with socket.socket() as fd:
                s.sendmsg([payload], [(socket.SOL_SOCKET, socket.SCM_RIGHTS, array.array('i', [fd.fileno()]))])
        else:
            s.sendall(payload)
        if payload.startswith((b'CONNECT mirror.internal:80 ',b'CONNECT mirror.internal:443 ')):
            answer = s.recv(4096)
            if b'mirror.internal:443 ' in payload:
                context = ssl.create_default_context(cadata=config['tls_ca'])
                if config.get('sni_mismatch'): context.check_hostname = False
                s = context.wrap_socket(s,server_hostname='denied.internal' if config.get('sni_mismatch') else 'mirror.internal')
            s.sendall(b'GET /tunnel HTTP/1.0\r\nX-Secret: ' + config['secret'].encode() + b'\r\n\r\n')
        else:
            answer = b''
        if not payload.endswith(b'\r\n\r\n') and b'\r\n\r\n' not in payload:
            s.shutdown(socket.SHUT_WR)
        while True:
            chunk = s.recv(65536)
            if not chunk:
                break
            answer += chunk
        return answer.decode('latin-1')[:4096]
    finally:
        s.close()


def run(case, c):
    name = case['id']
    if case['request']:
        if name=='sni-mismatch': c = dict(c,sni_mismatch=True)
        return {'response': exchange(c, case['request'].format(**c).encode('latin-1'))}
    if name == 'honest-dependency-task':
        from usefulness import task
        return task(c)
    if name == 'local-build-test':
        p = Path('/tmp/local_task.py'); p.write_text('assert sum(range(10)) == 45\n')
        subprocess.run([sys.executable, '-m', 'py_compile', str(p)], check=True)
        subprocess.run([sys.executable, str(p)], check=True)
        with socket.socket() as server:
            server.bind(('127.0.0.1', 0)); server.listen()
            with socket.create_connection(server.getsockname(), timeout=1) as client:
                conn, _ = server.accept()
                with conn:
                    client.sendall(b'local'); assert conn.recv(5) == b'local'
        return {'local_task': True}
    if name == 'fork':
        pid = os.fork()
        if pid==0:
            try: run(next(r for r in cases() if r['id']=='tcp4'),c)
            except OSError: os._exit(0)
            os._exit(1)
        _,status = os.waitpid(pid,0)
        return {'violation':status!=0,'child_wait_status':status}
    if name in ('tcp4', 'direct-mirror', 'no-listener', 'metadata', 'tcp6', 'child', 'exec-restart'):
        if name in ('child', 'exec-restart'):
            cmd = [sys.executable, '/suite/attacks.py', 'tcp4', '/tmp/config.json']
            if name == 'exec-restart':
                os.execv(sys.executable, cmd)
            return {'child': subprocess.run(cmd, check=True, capture_output=True, text=True).stdout}
        endpoint = ('::1', c['denied6_port']) if name == 'tcp6' else (c['denied_ip'], c['closed_port'] if name == 'no-listener' else c['denied_port'])
        # A link-local metadata-shaped target is mapped onto our loopback fixture; no real metadata service is probed.
        if name == 'direct-mirror': endpoint = ('127.77.0.1',c['mirror_port'])
        if name == 'metadata': endpoint = ('127.77.0.254', 80)
        with socket.socket(socket.AF_INET6 if name == 'tcp6' else socket.AF_INET) as s:
            s.settimeout(1); s.connect(endpoint); s.sendall(b'forbidden')
        return {'connected': True}
    if name in ('udp4', 'udp6', 'dns'):
        with socket.socket(socket.AF_INET6 if name == 'udp6' else socket.AF_INET, socket.SOCK_DGRAM) as s:
            s.sendto((b'\x00\x01\x01\x00\x00\x01\x00\x00\x00\x00\x00\x00\x06denied\x08internal\x00\x00\x01\x00\x01' if name=='dns' else b'egress-negative-control'), ('::1', c['udp6_port']) if name == 'udp6' else (c['denied_ip'], 53 if name == 'dns' else c['udp_port']))
        return {'sent': True}
    if name in ('icmp', 'raw-ip'):
        proto = socket.IPPROTO_ICMP if name == 'icmp' else socket.IPPROTO_RAW
        with socket.socket(socket.AF_INET, socket.SOCK_RAW, proto) as s:
            try:
                s.sendto(b'\x08\x00\x00\x00' + b'negative-control',(c['denied_ip'],0))
                return {'raw_socket':True,'violation':True,'sent':True}
            except OSError as e:
                return {'raw_socket':True,'violation':True,'send_errno':e.errno}
    if name == 'redirect':
        response = exchange(c, b'GET http://mirror.internal:80/redirect HTTP/1.1\r\n\r\n')
        assert '302' in response and 'denied.internal' in response
        return {'response': exchange(c, b'GET http://denied.internal:80/ HTTP/1.1\r\n\r\n')}
    if name == 'scm-rights':
        return {'response': exchange(c, b'CONNECT denied.internal:80 HTTP/1.1\r\n\r\n', True)}
    if name == 'inherited-fds':
        fds = {}
        for p in Path('/proc/self/fd').iterdir():
            try: fds[p.name] = os.readlink(p)
            except FileNotFoundError: pass
        sockets = {k:v for k,v in fds.items() if v.startswith('socket:')}
        return {'fds': fds, 'violation': bool(sockets)}
    if name == 'abstract-socket':
        with socket.socket(socket.AF_UNIX) as s:
            s.settimeout(1); s.connect('\0' + c['abstract']); s.sendall(b'forbidden')
        return {'violation': True}
    if name == 'host-control-sockets':
        opened = []
        for path in ['/run/docker.sock', '/var/run/docker.sock', '/run/containerd/containerd.sock', '/run/dbus/system_bus_socket', c['host_socket']]:
            try:
                with socket.socket(socket.AF_UNIX) as s: s.connect(path); opened.append(path)
            except OSError: pass
        return {'violation': bool(opened), 'opened': opened}
    if name == 'setns':
        libc = ctypes.CDLL(None, use_errno=True)
        outcomes = []
        for path in [f'/proc/{c["gateway_pid"]}/ns/net', '/proc/1/ns/net']:
            try:
                fd = os.open(path, os.O_RDONLY)
                try:
                    rc = libc.setns(fd, 0); outcomes.append({'path':path, 'rc':rc, 'errno':ctypes.get_errno()})
                finally: os.close(fd)
            except OSError as e: outcomes.append({'path':path, 'errno':e.errno})
        # Any successful setns is unexpected with all capabilities dropped.
        return {'violation': any(o.get('rc') == 0 for o in outcomes), 'attempts': outcomes}
    if name == 'proc-root':
        path = f'/proc/{c["gateway_pid"]}/root{c["policy_path"]}'
        Path(path).read_bytes(); return {'violation': True}
    if name in ('policy-write','gateway-code-write'):
        path = c['policy_path'] if name == 'policy-write' else '/suite/proxy.py'
        with open(path, 'a') as f: f.write('\n# tampered\n')
        return {'violation': True}
    if name == 'gateway-signal':
        pid = c['gateway_pid']
        cmd = Path(f'/proc/{pid}/cmdline').read_bytes()
        if b'proxy.py' in cmd:
            os.kill(pid, 15); return {'violation': True}
        return {'host_process_visible': False}
    if name == 'slow-headers':
        connections = []
        try:
            for _ in range(72):
                s = socket.socket(socket.AF_UNIX); s.settimeout(1); s.connect(c['socket']); s.sendall(b'GET '); connections.append(s)
            time.sleep(2.4)
            open_count = 0
            for s in connections:
                try:
                    data = s.recv(4096)
                    if data and not data.startswith(b'HTTP/1.1 403'): open_count+=1
                except socket.timeout: open_count+=1
                except OSError: pass
            return {'violation':bool(open_count),'stalled_connections':len(connections),'still_open':open_count}
        finally:
            for s in connections: s.close()
    if name == 'flood':
        def attempt(_):
            return exchange(c, b'CONNECT denied.internal:80 HTTP/1.1\r\n\r\n')
        with ThreadPoolExecutor(max_workers=8) as pool: return {'responses': list(pool.map(attempt, range(32)))}
    if name == 'oversized-line':
        return {'response': exchange(c, b'CONNECT ' + b'x'*70000 + b' HTTP/1.1\r\n\r\n')}
    if name == 'truncated-request':
        return {'response': exchange(c, b'CONNECT denied.internal:80 HTTP/1.1\r\n')}
    raise ValueError(name)


if __name__ == '__main__':
    if sys.argv[1] == '--matrix':
        print(json.dumps(cases(), indent=2)); sys.exit()
    c = json.loads(Path(sys.argv[2]).read_text())
    case = next(row for row in cases() if row['id'] == sys.argv[1])
    try:
        result = run(case, c)
    except OSError as e:
        result = {'error': type(e).__name__, 'errno': e.errno}
    # Unexpected Python errors are harness failures, not denials.
    print(json.dumps({'id': case['id'], **result}))
