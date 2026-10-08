#!/usr/bin/env python3
"""Bounded accounting calibration, invoked ONLY inside unshare --net.

No external interface, default route, DNS, service, gateway, or production agent.
Documentation addresses are assigned locally to lo. Trace binds independently
attribute initial TCP/UDP packets to two disposable traced sender processes.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import socket
import subprocess
import sys
import tempfile
import threading
import time

EGRESS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(EGRESS))
from observer import decode_packet

TARGETS = [('192.0.2.1', 40101), ('198.51.100.2', 40102),
           ('2001:db8::1', 40103), ('2001:db8::2', 40104)]


def require_local_topology(host_netns):
    if host_netns is None or os.stat('/proc/self/ns/net').st_ino == host_netns:
        raise RuntimeError('private outer namespace required')
    links = json.loads(subprocess.check_output(['ip','-j','link'],text=True))
    if [x['ifname'] for x in links] != ['lo']: raise RuntimeError('external interface present')
    addresses = json.loads(subprocess.check_output(['ip','-j','addr','show','dev','lo'],text=True))
    local = {a['local'] for interface in addresses for a in interface['addr_info']}
    if not {ip for ip,_ in TARGETS} <= local: raise RuntimeError('targets must be assigned locally')
    for family in ('-4','-6'):
        routes = json.loads(subprocess.check_output(['ip',family,'-j','route','show','table','all'],text=True))
        if any(r.get('dev')!='lo' or r.get('dst')=='default' for r in routes):
            raise RuntimeError('nonlocal/default route present')


def sender(role):
    for i, (ip, port) in enumerate(TARGETS):
        if i % 2 != role: continue
        family = socket.AF_INET6 if ':' in ip else socket.AF_INET
        source = '::1' if family == socket.AF_INET6 else '127.0.0.1'
        for j, kind in enumerate((socket.SOCK_STREAM, socket.SOCK_DGRAM)):
            with socket.socket(family, kind) as s:
                s.settimeout(.5)
                s.bind((source, 39000 + i*2 + j))
                if kind == socket.SOCK_STREAM:
                    try: s.connect((ip, port))
                    except ConnectionRefusedError: pass
                    else: raise RuntimeError('expected refused TCP connect')
                else: s.sendto(b'outer-accounting-calibration', (ip, port))


def sockaddr(line):
    v6 = 'sa_family=AF_INET6' in line
    ip = re.search(r'inet_pton\(AF_INET6, "([^"]+)"', line) if v6 else re.search(r'inet_addr\("([^"]+)"\)', line)
    port = re.search(r'sin6_port=htons\((\d+)\)', line) if v6 else re.search(r'sin_port=htons\((\d+)\)', line)
    if not ip or not port: raise ValueError('unparsed internet sockaddr: '+line)
    return ip.group(1), int(port.group(1))


def trace_flows(paths):
    flows = []
    for path in paths:
        pid = int(path.suffix[1:]); binds = {}
        for line in path.read_text().splitlines():
            call = re.search(r'(\d+\.\d+) (bind|connect|sendto)\((\d+)', line)
            if not call or 'sa_family=AF_INET' not in line: continue
            stamp, operation, fd = call.groups()
            address = sockaddr(line)
            if operation == 'bind':
                if not line.endswith(' = 0'): raise ValueError('failed bind: '+line)
                binds[fd] = address
                continue
            if fd not in binds: raise ValueError('network attempt without traced bind')
            source = binds[fd]
            flows.append(dict(pid=pid, t=float(stamp), src=source[0], source_port=source[1],
                              dst=address[0], port=address[1], protocol=6 if operation=='connect' else 17,
                              raw=line))
    return flows


def key(row):
    return tuple(row[k] for k in ('src','source_port','dst','port','protocol'))


def main(args):
    artifact = {'status':'fail', 'scope':'isolated two-sender TCP/UDP calibration',
                'limitations':['Not integrated with gateway/sandbox or its permit oracle.',
                    'PID attribution covers initial TCP SYN and UDP datagrams via traced explicit binds.',
                    'ICMP/TCP replies are captured but not assigned a sender PID.',
                    'No raw sockets, inherited FDs, connected UDP, sendmsg, io_uring or universal syscall coverage claim.'],
                'hashes':{str(p.relative_to(EGRESS)):hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in (Path(__file__).resolve(), EGRESS/'observer.py')}}
    raw = None; thread = None; stop = threading.Event(); events = []; errors = []
    try:
        namespace = os.stat('/proc/self/ns/net').st_ino
        if namespace == args.host_netns: raise RuntimeError('outer net namespace is not private')
        links = json.loads(subprocess.check_output(['ip','-j','link'],text=True))
        if [x['ifname'] for x in links] != ['lo']: raise RuntimeError('external interface present')
        subprocess.run(['ip','link','set','lo','up'],check=True)
        for ip,_ in TARGETS:
            subprocess.run(['ip','addr','add',ip+('/128' if ':' in ip else '/32'),'dev','lo'],check=True)
        routes = {family:json.loads(subprocess.check_output(['ip',family,'-j','route','show','table','all'],text=True))
                  for family in ('-4','-6')}
        if any(r.get('dev') != 'lo' or r.get('dst') == 'default' for rs in routes.values() for r in rs):
            raise RuntimeError('nonlocal/default route present')
        artifact.update(netns=namespace, host_netns=args.host_netns, links=links, routes=routes)
        raw = socket.socket(socket.AF_PACKET,socket.SOCK_RAW,socket.htons(3))
        raw.setsockopt(socket.SOL_SOCKET,socket.SO_RCVBUF,4*1024*1024)
        raw.bind(('lo',0)); raw.settimeout(.1)
        def capture():
            while not stop.is_set():
                try:
                    data, address = raw.recvfrom(262144)
                    if address[2] != socket.PACKET_OUTGOING: continue
                    event = decode_packet(data)
                    if event is None: errors.append('unparsed frame')
                    else: events.append(event)  # Deliberately NO destination filter.
                except socket.timeout: pass
                except OSError as error: errors.append(repr(error)); break
        thread = threading.Thread(target=capture); thread.start()
        with tempfile.TemporaryDirectory(prefix='sc03-outer-') as directory:
            trace = Path(directory)/'trace'
            run = subprocess.run(['strace','-ff','-ttt','-yy','-e','trace=bind,connect,sendto,close,clone,clone3,vfork,execve',
                                  '-o',str(trace),'/usr/bin/python3',str(Path(__file__).resolve()),'--workers',
                                  '--host-netns',str(args.host_netns)],
                                 capture_output=True,text=True,timeout=10)
            if run.returncode: raise RuntimeError('sender/trace failed: '+run.stderr)
            time.sleep(.2); stop.set(); thread.join(timeout=2)
            paths = sorted(Path(directory).glob('trace.*'))
            flows = trace_flows(paths)
            artifact['traces'] = {p.name:p.read_text() for p in paths}
        import struct
        received,dropped = struct.unpack('II',raw.getsockopt(263,6,8))
        artifact.update(flows=flows, packets=events, packet_statistics={'received':received,'dropped':dropped}, errors=errors)
        initial = [p for p in events if p['protocol']==17 or
                   (p['protocol']==6 and p['tcp_flags'] is not None and p['tcp_flags']&2 and not p['tcp_flags']&16)]
        matches = [{**packet,'pids':sorted({f['pid'] for f in flows if key(f)==key(packet) and f['t']<=packet['t']})}
                   for packet in initial]
        artifact['attributed_initial_packets'] = matches
        expected = {(ip,port,protocol) for ip,port in TARGETS for protocol in (6,17)}
        if len(flows)!=8 or {(f['dst'],f['port'],f['protocol']) for f in flows}!=expected:
            raise RuntimeError('missing/unexpected independently traced flow')
        if len({f['pid'] for f in flows})!=2: raise RuntimeError('two distinct sender PIDs required')
        if {key(f) for f in flows}!={key(p) for p in initial} or any(len(p['pids'])!=1 for p in matches):
            raise RuntimeError('packet/trace attribution mismatch')
        # Deleting a traced transmission must invalidate packet provenance.
        reduced = flows[1:]
        artifact['missing_trace_mutation_detected'] = any(not any(key(f)==key(p) for f in reduced) for p in initial)
        if dropped or errors or not artifact['missing_trace_mutation_detected']:
            raise RuntimeError('loss, capture failure or insensitive oracle')
        artifact['status'] = 'pass'
    except Exception as error:
        artifact['error'] = str(error)
    finally:
        stop.set()
        if thread: thread.join(timeout=2)
        if raw: raw.close()
        args.output.write_text(json.dumps(artifact,indent=2)+'\n')
    print(json.dumps({k:artifact[k] for k in ('status','error') if k in artifact}))
    return 0 if artifact['status']=='pass' else 1


if __name__=='__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--host-netns',type=int)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--workers',action='store_true')
    parser.add_argument('--sender',type=int,choices=(0,1))
    args = parser.parse_args()
    if args.sender is not None:
        require_local_topology(args.host_netns)
        sender(args.sender)
    elif args.workers:
        require_local_topology(args.host_netns)
        children = [subprocess.Popen(['/usr/bin/python3',str(Path(__file__).resolve()),'--sender',str(role),
                                     '--host-netns',str(args.host_netns)]) for role in (0,1)]
        sys.exit(int(any([child.wait(timeout=5) for child in children])))
    else:
        if args.host_netns is None or args.output is None: parser.error('--host-netns and --output required')
        sys.exit(main(args))
