#!/usr/bin/env python3
"""Test-only SC-03 negative controls; never modifies a production sandbox."""
import argparse
import base64
import errno
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import signal
import socket
import socketserver
import ssl
import subprocess
import sys
import tempfile
import threading
import time

from attacks import cases
from observer import PacketObserver

ROOT = Path(__file__).resolve().parent


class Endpoint:
    def __init__(self, ip, udp=False, tls=None):
        self.events = []; self.lock = threading.Lock()
        owner = self
        class Handler(socketserver.BaseRequestHandler):
            def handle(self):
                if udp:
                    data = self.request[0]
                    with owner.lock: owner.events.append({'t':time.time(), 'bytes':len(data), 'payload':data.hex()})
                    return
                with owner.lock:
                    event = {'t':time.time(), 'bytes':0, 'payload':''}; owner.events.append(event)
                self.request.settimeout(2)
                if tls:
                    try: self.request = tls.wrap_socket(self.request,server_side=True)
                    except (OSError,ssl.SSLError): return
                try: data = self.request.recv(65536)
                except (OSError, socket.timeout): data = b''
                with owner.lock: event.update(bytes=len(data), payload=data.hex())
                if b'/redirect ' in data:
                    response = b'HTTP/1.0 302 Found\r\nLocation: http://denied.internal:80/\r\nContent-Length: 0\r\n\r\n'
                else:
                    from usefulness import wheel
                    body = wheel() if b'/packages/sc03_fixture-' in data else b'fixture-package\n'
                    response = b'HTTP/1.0 200 OK\r\nContent-Length: '+str(len(body)).encode()+b'\r\n\r\n'+body
                try: self.request.sendall(response)
                except OSError: pass
        base = socketserver.ThreadingUDPServer if udp else socketserver.ThreadingTCPServer
        class Server(base):
            address_family = socket.AF_INET6 if ':' in ip else socket.AF_INET
            daemon_threads = True
        self.server = Server((ip, 0), Handler)
        self.port = self.server.server_address[1]
        self.thread = threading.Thread(target=self.server.serve_forever, daemon=True); self.thread.start()

    def snapshot(self):
        with self.lock: return [dict(e) for e in self.events]

    def close(self):
        self.server.shutdown(); self.server.server_close(); self.thread.join()


def sandbox_command(work, socket_path, case, shared_net=False):
    from launcher import command
    return command(work/'code',work/'config.json',socket_path,[case],shared_net)


def verdict(case, packets, allowed, denied, report, decisions, full=True):
    reasons = []
    if packets.get('forbidden'): reasons.append('forbidden host packet (including handshake attempts)')
    if denied: reasons.append('forbidden destination observed traffic')
    if report.get('violation'): reasons.append('privilege/topology probe succeeded')
    expected = case['expected']
    if expected in ('allow','scope-limited') and report.get('error'): reasons.append('honest/allowed operation returned an error')
    if case['id'] in ('honest-http','honest-connect') and 'fixture-package' not in report.get('response',''): reasons.append('honest HTTP response missing')
    if case['id']=='honest-dependency-task' and (not report.get('local_task') or report.get('test_output')!='dependency tests passed' or not report.get('sha256')): reasons.append('dependency install/build/test did not complete')
    if expected in ('allow','scope-limited'):
        if not allowed: reasons.append('positive control did not reach mirror')
        if not any(d.get('decision') == 'allow' and d.get('dest') in ('mirror.internal:80','mirror.internal:443') for d in decisions): reasons.append('missing gateway allow decision')
        if full and not packets.get('allowed'): reasons.append('mirror traffic absent from packet observer')
    if expected == 'local' and not report.get('local_task'): reasons.append('local build/test failed')
    if expected=='deny' and case['id']!='redirect':
        if any(d.get('decision') in ('allow','attempt','connected') for d in decisions): reasons.append('denied case received gateway permission or socket attempt')
        if case.get('request') and not any(d.get('decision')=='deny' for d in decisions): reasons.append('missing gateway denial')
    if expected == 'deny' and case['id']!='redirect' and allowed: reasons.append('denied parser input opened mirror connection')
    return reasons


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, default=Path('/tmp/egress-outcome.json'))
    parser.add_argument('--gateway-only', action='store_true', help='partial parser regression; no isolation claim')
    parser.add_argument('--self-check-direct-mirror',action='store_true',help='inject host mirror SYN without gateway authority and require source-port correlation to catch it')
    parser.add_argument('--self-check-packet-oracle',action='store_true',help='inject one failed host SYN into a normal negative observation window; require packet-only detection')
    parser.add_argument('--self-check-shared-net', action='store_true', help='deliberately break only the disposable test namespace; require oracle to catch it')
    args = parser.parse_args()
    if args.gateway_only and (args.self_check_shared_net or args.self_check_packet_oracle or args.self_check_direct_mirror): parser.error('mutation requires full mode')
    artifact = {'schema':1, 'mode':'gateway-only' if args.gateway_only else 'full', 'status':'blocked', 'platform':platform.platform(), 'expected':cases(), 'results':[], 'limitations':['Fixture-only packet attribution on host loopback; not a universal kernel escape proof.', 'CONNECT is a byte tunnel: HTTP Host/SNI and downstream relay identity are not authenticated.', 'TLS uses a test CA; no real package-manager/CDN compatibility claim.']}
    artifact['hashes'] = {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in ROOT.glob('*.py')}
    endpoints = []; processes = []; traces = []; fixture_lock = None; capture = None; passed_fd = None; canaries = []
    try:
        if not args.gateway_only:
            if not shutil.which('strace'): raise RuntimeError('strace unavailable: independent gateway connect tracing required')
            if not shutil.which('bwrap'): raise RuntimeError('bubblewrap unavailable')
            preflight = subprocess.run(['bwrap','--unshare-all','--ro-bind','/','/','--proc','/proc','--dev','/dev','--cap-drop','ALL','/usr/bin/true'], capture_output=True, text=True, timeout=10)
            if preflight.returncode: raise RuntimeError('namespace preflight: '+preflight.stderr.strip())
        # The host-wide abstract lock prevents concurrent fixtures contaminating packet windows.
        fixture_lock = socket.socket(socket.AF_UNIX)
        lock_deadline = time.monotonic()+60
        while True:
            try:
                fixture_lock.bind('\0control-stack-sc03-fixture-lock'); break
            except OSError as e:
                if e.errno!=errno.EADDRINUSE: raise
                if time.monotonic()>=lock_deadline: raise RuntimeError('another egress fixture holds the observation lock')
                time.sleep(.1)
        with tempfile.TemporaryDirectory(prefix='sc03-egress-') as temp:
            work = Path(temp)
            work.chmod(0o755)
            shutil.copytree(ROOT,work/'code',ignore=shutil.ignore_patterns('__pycache__','*.json'))
            cert = work/'cert.pem'; key = work/'key.pem'
            subprocess.run(['openssl','req','-x509','-newkey','rsa:2048','-nodes','-keyout',str(key),'-out',str(cert),'-days','1','-subj','/CN=mirror.internal','-addext','subjectAltName=DNS:mirror.internal'],check=True,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL)
            tls = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER); tls.load_cert_chain(cert,key)
            tls_mirror = Endpoint('127.77.0.1',tls=tls)
            mirror = Endpoint('127.77.0.1'); denied = Endpoint('127.77.0.2'); denied6 = Endpoint('::1'); udp = Endpoint('127.77.0.2', True); udp6 = Endpoint('::1', True)
            endpoints = [mirror, tls_mirror, denied, denied6, udp, udp6]
            with socket.socket() as closed:
                closed.bind(('127.77.0.2',0)); closed_port = closed.getsockname()[1]
            sock = str(work/'gateway.sock'); policy = work/'policy.json'; log = work/'gateway.jsonl'
            policy.write_text(json.dumps({'allow':{'mirror.internal:80':['127.77.0.1',mirror.port], 'mirror.internal:443':['127.77.0.1',tls_mirror.port]},'socket':sock,'log':str(log)}))
            policy_bytes = policy.read_bytes()
            artifact['policy'] = json.loads(policy_bytes); artifact['policy_sha256'] = hashlib.sha256(policy_bytes).hexdigest()
            def start_gateway(policy_file=policy):
                gateway_cmd = ['/usr/bin/python3',str(ROOT/'proxy.py'),str(policy_file)]
                if not args.gateway_only:
                    trace = work/('gateway-'+str(len(traces))+'.strace'); traces.append(trace)
                    gateway_cmd = ['strace','-f','-ttt','-yy','-e','trace=connect,sendto,sendmsg','-o',str(trace),*gateway_cmd]
                p = subprocess.Popen(gateway_cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True,start_new_session=True)
                processes.append(p)
                for _ in range(100):
                    if p.poll() is not None: raise RuntimeError('gateway startup: '+p.stderr.read())
                    if Path(sock).exists(): return p
                    time.sleep(.02)
                raise RuntimeError('gateway socket startup timeout')
            gateway = start_gateway()
            c = dict(socket=sock if args.gateway_only else '/run/egress.sock', mirror_port=mirror.port,denied_ip='127.77.0.2', denied_port=denied.port, denied6_port=denied6.port, udp_port=udp.port, udp6_port=udp6.port, closed_port=closed_port, abstract='sc03-'+str(os.getpid()), host_socket=str(work/'host-control.sock'), gateway_pid=gateway.pid, policy_path=str(policy), secret=base64.b64encode(b'synthetic-secret-control').decode())
            c['secret_len'] = len(c['secret'])
            from usefulness import wheel
            c.update(tls_ca=cert.read_text(),host_netns=os.stat('/proc/self/ns/net').st_ino,host_pidns=os.stat('/proc/self/ns/pid').st_ino,wheel_sha256=hashlib.sha256(wheel()).hexdigest())
            config_path = work/'config.json'; config_path.write_text(json.dumps(c))
            if not args.gateway_only:
                capture = PacketObserver([denied6.port, udp6.port])
                # Prove independent observers can see both completed and failed network effects.
                with socket.create_connection(('127.77.0.2', denied.port), timeout=2) as s: s.sendall(b'observer-positive-control')
                with socket.socket() as s:
                    s.settimeout(.2)
                    try: s.connect(('127.77.0.2',closed_port))
                    except OSError: pass
                with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as s: s.sendto(b'udp-control', ('127.77.0.2',udp.port))
                with socket.create_connection(('::1',denied6.port), timeout=2) as s: s.sendall(b'ipv6-control')
                with socket.socket(socket.AF_INET6, socket.SOCK_DGRAM) as s: s.sendto(b'udp6-control', ('::1',udp6.port))
                time.sleep(.2)
                controls = capture.snapshot(); artifact['observer_positive_controls'] = controls
                required = [(c['denied_ip'],denied.port,6),(c['denied_ip'],closed_port,6),(c['denied_ip'],udp.port,17),('::1',denied6.port,6),('::1',udp6.port,17)]
                if any(not any((p['dst'],p['port'],p['protocol']) == item for p in controls) for item in required): raise RuntimeError('packet observer missed positive control')
                if not all(ep.snapshot() for ep in [denied,denied6,udp,udp6]): raise RuntimeError('destination observer missed positive control')
                for address in ['\0'+c['abstract'],c['host_socket']]:
                    s = socket.socket(socket.AF_UNIX); s.bind(address); s.listen(); s.setblocking(False); canaries.append(s)
                # Deliberately hand bwrap a live host-network descriptor; it must not survive into the attacker.
                passed_fd = socket.create_connection(('127.77.0.2',denied.port), timeout=2)
                injected = subprocess.run(sandbox_command(work,sock,'--inspect'),capture_output=True,text=True,timeout=10,pass_fds=(passed_fd.fileno(),))
                rejection = injected.returncode!=0 and 'inherited socket descriptor' in injected.stderr
                artifact['results'].append({'id':'startup-inherited-socket','expected':'deny','status':'pass' if rejection else 'fail','stderr':injected.stderr[:2000]})
                if not rejection: raise RuntimeError('launcher accepted inherited network authority')
                inspection = subprocess.run(sandbox_command(work,sock,'--inspect'), capture_output=True, text=True, timeout=10)
                if inspection.returncode: raise RuntimeError('sandbox inventory: '+inspection.stderr)
                inventory = json.loads(inspection.stdout); artifact['sandbox_inventory'] = inventory
                interfaces = [line.split(':',1)[0].strip() for line in inventory['interfaces'].splitlines()[2:]]
                if interfaces != ['lo'] or len(inventory['routes4'].splitlines()) != 1: raise RuntimeError('unexpected namespace interfaces/routes')
                if inventory['netns'] == os.stat('/proc/self/ns/net').st_ino or inventory['pidns'] == os.stat('/proc/self/ns/pid').st_ino: raise RuntimeError('namespace separation missing')
                passed_fd.close(); passed_fd = None
                time.sleep(.2)
                if any(v.startswith('socket:') for v in inventory['fds'].values()): raise RuntimeError('inherited socket survived launch')
                status = dict(line.split(':',1) for line in inventory['status'].splitlines() if ':' in line)
                if int(status['CapEff'].strip(),16) or status['NoNewPrivs'].strip() != '1': raise RuntimeError('capabilities/no-new-privileges invariant missing')
            selected = [r for r in cases() if not args.gateway_only or r['request'] or r['id'] in ('redirect','scm-rights','flood','oversized-line','truncated-request')]
            if args.self_check_shared_net or args.self_check_packet_oracle or args.self_check_direct_mirror: selected = [next(r for r in cases() if r['id']=='tcp4')]
            for case in selected:
                time.sleep(.1)
                before = [len(ep.snapshot()) for ep in endpoints]; packet_before = len(capture.snapshot()) if capture else 0
                log_before = len(log.read_text().splitlines())
                cmd = ['/usr/bin/python3',str(ROOT/'attacks.py'),case['id'],str(config_path)] if args.gateway_only else sandbox_command(work,sock,case['id'],args.self_check_shared_net)
                result = subprocess.run(cmd, capture_output=True, text=True, timeout=15, close_fds=True, pass_fds=())
                if args.self_check_direct_mirror:
                    with socket.create_connection(('127.77.0.1',mirror.port),timeout=2) as unlogged_mirror:
                        unlogged_mirror.sendall(b'direct-mirror-mutation')
                if args.self_check_packet_oracle:
                    with socket.socket() as injected_syn:
                        injected_syn.settimeout(.2)
                        try: injected_syn.connect((c['denied_ip'],closed_port))
                        except OSError: pass
                time.sleep(.2)
                observed = [ep.snapshot()[n:] for ep,n in zip(endpoints,before)]
                packets = capture.snapshot()[packet_before:] if capture else []
                allowed_peers = {('127.77.0.1',mirror.port,6),('127.77.0.1',tls_mirror.port,6)}
                classified = {'allowed':[p for p in packets if (p['dst'],p['port'],p['protocol']) in allowed_peers], 'forbidden':[p for p in packets if (p['dst'],p['port'],p['protocol']) not in allowed_peers]}
                decisions = [json.loads(line) for line in log.read_text().splitlines()[log_before:]]
                for packet in classified['allowed']:
                    if packet.get('tcp_flags',0) is not None and packet['tcp_flags'] & 2 and not packet['tcp_flags'] & 16:
                        matched = any(d.get('decision')=='attempt' and (d.get('source_ip'),d.get('source_port'),d.get('ip'),d.get('port'))==(packet['src'],packet['source_port'],packet['dst'],packet['port']) and d['t']<=packet['t'] for d in decisions)
                        if not matched: classified['forbidden'].append(dict(packet,reason='unattributed mirror SYN'))
                try: report = json.loads(result.stdout)
                except ValueError: report = {}
                reasons = verdict(case, classified, observed[0]+observed[1], sum(observed[2:],[]), report, decisions, not args.gateway_only)
                canary_connections = []
                for index,canary in enumerate(canaries):
                    while True:
                        try:
                            conn,_ = canary.accept(); conn.close(); canary_connections.append(index)
                        except BlockingIOError: break
                if canary_connections: reasons.append('host control socket independently observed a connection')
                if result.returncode or not report: reasons.append('attacker crashed or returned invalid report')
                if policy.read_bytes() != policy_bytes: reasons.append('trusted policy changed')
                if gateway.poll() is not None: reasons.append('gateway died')
                if case['id'].startswith('secret-'):
                    received = b''.join(bytes.fromhex(e['payload']) for e in observed[0]+observed[1])
                    if c['secret'].encode() not in received: reasons.append('confidentiality counterexample not observed at mirror')
                row = dict(id=case['id'], expected=case['expected'], status='fail' if reasons else 'pass', reasons=reasons, exit_status=result.returncode, report=report, stderr=result.stderr[:2000], host_control_connections=canary_connections, packets=classified, destinations=observed, gateway=decisions)
                if case['id']=='honest-dependency-task' and report.get('sha256')!=c['wheel_sha256']:
                    row['reasons'].append('dependency digest differs from pinned manifest'); row['status']='fail'
                artifact['results'].append(row); print(case['id']+': '+row['status'], flush=True)
                # Fresh positive check after each attack prevents DoS from masking later denials.
                recovery_before = [len(ep.snapshot()) for ep in endpoints]
                recovery_packet_before = len(capture.snapshot()) if capture else 0
                recovery_log_before = len(log.read_text().splitlines())
                recovery = subprocess.run(['/usr/bin/python3',str(ROOT/'attacks.py'),'honest-http',str(config_path)] if args.gateway_only else sandbox_command(work,sock,'honest-http'), capture_output=True,text=True,timeout=15)
                time.sleep(.1)
                row['recovery'] = {'exit_status':recovery.returncode,'stdout':recovery.stdout,'stderr':recovery.stderr[:1000], 'packets':capture.snapshot()[recovery_packet_before:] if capture else [], 'destinations':[ep.snapshot()[n:] for ep,n in zip(endpoints,recovery_before)], 'gateway':[json.loads(line) for line in log.read_text().splitlines()[recovery_log_before:]]}
                if any((p['dst'],p['port'],p['protocol']) not in allowed_peers for p in row['recovery']['packets']) or any(row['recovery']['destinations'][2:]): raise RuntimeError('forbidden effect during recovery')
                if recovery.returncode or 'fixture-package' not in recovery.stdout: raise RuntimeError('honest recovery failed after '+case['id'])
            if not args.gateway_only and not args.self_check_shared_net and not args.self_check_packet_oracle and not args.self_check_direct_mirror:
                # Kill the disposable gateway, prove no direct fallback, then start a new socket/namespace.
                os.killpg(gateway.pid,signal.SIGTERM); gateway.wait(timeout=5); Path(sock).unlink(missing_ok=True)
                before = [len(e.snapshot()) for e in endpoints]; packet_before = len(capture.snapshot())
                stopped = subprocess.run(sandbox_command(work,sock,'honest-http'),capture_output=True,text=True,timeout=15)
                time.sleep(.2)
                quiet = not capture.snapshot()[packet_before:] and all(len(e.snapshot())==n for e,n in zip(endpoints,before))
                stopped_report = json.loads(stopped.stdout) if stopped.returncode == 0 else {}
                artifact['results'].append({'id':'gateway-down','expected':'deny','status':'pass' if quiet and (stopped_report.get('error') or 'topology rejected: gateway unavailable' in stopped.stderr) else 'fail','report':stopped_report,'stderr':stopped.stderr[:2000]})
                gateway = start_gateway(); c['gateway_pid']=gateway.pid; config_path.write_text(json.dumps(c))
                restarted = subprocess.run(sandbox_command(work,sock,'honest-http'),capture_output=True,text=True,timeout=15)
                artifact['results'].append({'id':'gateway-restart','expected':'allow','status':'pass' if restarted.returncode==0 and 'fixture-package' in restarted.stdout else 'fail'})
                bad = work/'bad-policy.json'; bad.write_text('{"allow":{},"socket":"'+str(work/'invalid.sock')+'"}')
                invalid = subprocess.run(['/usr/bin/python3',str(ROOT/'proxy.py'),str(bad)],capture_output=True,text=True,timeout=5)
                artifact['results'].append({'id':'invalid-policy','expected':'deny','status':'pass' if invalid.returncode!=0 and not (work/'invalid.sock').exists() else 'fail'})
            if traces:
                from tracing import connects,check
                artifact['gateway_syscall_trace'] = ''.join(path.read_text() for path in traces)
                artifact['gateway_connect_attempts'] = connects(artifact['gateway_syscall_trace'])
                artifact['gateway_decisions'] = [json.loads(line) for line in log.read_text().splitlines()]
                trace_errors = check(artifact['gateway_connect_attempts'],artifact['gateway_decisions'],artifact['policy'])
                if trace_errors: raise RuntimeError('; '.join(trace_errors))
            if capture and not args.self_check_direct_mirror:
                permits = [d for d in artifact.get('gateway_decisions',[]) if d.get('decision')=='attempt']
                orphans = []
                mirror_syns = [p for p in capture.snapshot() if (p['dst'],p['port'],p['protocol']) in allowed_peers and p.get('tcp_flags') is not None and p['tcp_flags'] & 2 and not p['tcp_flags'] & 16]
                for packet in mirror_syns:
                    if not any((d.get('source_ip'),d.get('source_port'),d.get('ip'),d.get('port'))==(packet['src'],packet['source_port'],packet['dst'],packet['port']) and d['t']<=packet['t']<=d['t']+10 for d in permits): orphans.append(packet)
                artifact['gateway_syn_provenance'] = {'observed_syns':len(mirror_syns),'orphan_syns':orphans}
                if orphans: raise RuntimeError('mirror SYN without gateway provenance, including recovery/restart')
            if capture:
                artifact['packet_statistics'] = capture.statistics()
                if artifact['packet_statistics']['dropped']: raise RuntimeError('packet capture loss; absence evidence invalid')
            if capture and capture.errors: raise RuntimeError('packet observer failed: '+repr(capture.errors))
            failed = [r for r in artifact['results'] if r['status']=='fail']
            if args.self_check_shared_net or args.self_check_packet_oracle or args.self_check_direct_mirror:
                detected = any('forbidden host packet' in reason or (args.self_check_shared_net and 'topology rejected: host namespace reused' in r.get('stderr','')) for r in failed for reason in r.get('reasons',[]))
                artifact['status'] = 'mutation-detected' if detected else 'fail'
            else: artifact['status'] = 'fail' if failed else ('partial-pass' if args.gateway_only else 'pass')
    except (OSError, RuntimeError, subprocess.TimeoutExpired, ValueError) as e:
        artifact['blocker'] = str(e)
        artifact['status'] = 'fail' if artifact['results'] else 'blocked'
        print(artifact['status']+': '+str(e), file=sys.stderr)
    finally:
        if passed_fd: passed_fd.close()
        for s in canaries: s.close()
        for p in processes:
            if p.poll() is None:
                os.killpg(p.pid,signal.SIGTERM)
                try: p.wait(timeout=5)
                except subprocess.TimeoutExpired: os.killpg(p.pid,signal.SIGKILL); p.wait()
            if p.stderr: p.stderr.close()
        if capture: capture.close()
        if fixture_lock: fixture_lock.close()
        for ep in endpoints: ep.close()
        args.output.parent.mkdir(parents=True,exist_ok=True); args.output.write_text(json.dumps(artifact,indent=2)+'\n')
    return 2 if artifact['status']=='blocked' else 0 if artifact['status'] in ('pass','partial-pass','mutation-detected') else 1


if __name__ == '__main__': sys.exit(main())
