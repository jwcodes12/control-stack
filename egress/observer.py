"""Independent host-side packet observer. Linux AF_PACKET includes failed SYNs.

No gateway decision or attacker output feeds this observer. The disposable fixture
uses 127.77.0.0/16 plus designated ::1 ports to distinguish it from other host work.
"""
import socket
import struct
import threading
import time


def decode_packet(data):
    if len(data) < 14: return None
    kind = struct.unpack('!H', data[12:14])[0]
    if kind == 0x0800:
        p = data[14:]
        if len(p) < 20: return None
        offset = (p[0] & 15)*4
        if offset < 20 or len(p) < offset: return None
        src, dst = socket.inet_ntop(socket.AF_INET, p[12:16]), socket.inet_ntop(socket.AF_INET, p[16:20])
        proto = p[9]
        fragmented = bool(struct.unpack('!H',p[6:8])[0] & 0x1fff)
    elif kind == 0x86dd:
        p = data[14:]
        if len(p) < 40: return None
        offset = 40; proto = p[6]; fragmented = False
        while proto in (0,43,44,51,60):
            if len(p)<offset+8: return None
            next_proto = p[offset]
            if proto==44:
                fragmented = bool(struct.unpack('!H',p[offset+2:offset+4])[0] & 0xfff8)
                size = 8
            else: size = (p[offset+1]+(2 if proto==51 else 1))*(4 if proto==51 else 8)
            proto = next_proto; offset += size
            if len(p)<offset: return None
            # Non-initial fragments start in arbitrary payload, not an extension
            # header. Preserve their address-level evidence without reading ports.
            if fragmented: break
        src, dst = socket.inet_ntop(socket.AF_INET6, p[8:24]), socket.inet_ntop(socket.AF_INET6, p[24:40])
    else: return None
    has_ports = not fragmented and proto in (6,17) and len(p)>=offset+4
    source_port,port = struct.unpack('!HH',p[offset:offset+4]) if has_ports else (None,None)
    flags = p[offset+13] if proto==6 and not fragmented and len(p)>=offset+14 else None
    return dict(src=src,dst=dst,source_port=source_port,protocol=proto,port=port,tcp_flags=flags,fragmented=fragmented,bytes=len(data),t=time.time())


class PacketObserver:
    def __init__(self, ipv6_ports):
        self.ports = set(ipv6_ports)
        self.events = []; self.errors = []; self.lock = threading.Lock()
        self.socket = socket.socket(socket.AF_PACKET, socket.SOCK_RAW, socket.htons(3))
        self.socket.setsockopt(socket.SOL_SOCKET,socket.SO_RCVBUF,4*1024*1024)
        self.received = 0; self.dropped = 0
        self.socket.bind(('lo', 0)); self.socket.settimeout(.1)
        self.stop = threading.Event()
        self.thread = threading.Thread(target=self._run, daemon=True); self.thread.start()

    def _run(self):
        while not self.stop.is_set():
            try:
                data, address = self.socket.recvfrom(262144)
                if address[2] != socket.PACKET_OUTGOING: continue
                event = decode_packet(data)
                if event and (event['dst'].startswith('127.77.') or event['dst'] == '::1'):
                    with self.lock: self.events.append(event)
            except socket.timeout: pass
            except OSError as e:
                if not self.stop.is_set(): self.errors.append(repr(e))

    def snapshot(self):
        with self.lock: return list(self.events)

    def statistics(self):
        # Linux SOL_PACKET/PACKET_STATISTICS reads and resets interval counters.
        received,dropped = struct.unpack('II',self.socket.getsockopt(263,6,8))
        self.received += received; self.dropped += dropped
        return {'received':self.received,'dropped':self.dropped}

    def close(self):
        self.stop.set(); self.thread.join(timeout=2); self.socket.close()
