"""Host-side, pinned-peer test gateway. Invalid policy fails before socket bind."""
import asyncio
import ipaddress
import json
import os
from pathlib import Path
import sys
import socket
import time

from protocol import MAX_HEADERS, MAX_LINE, Rejected, authority, parse


def load_policy(path):
    policy = json.loads(Path(path).read_text())
    if set(policy)!= {'allow','socket','log'} or not isinstance(policy['allow'],dict) or not policy['allow']: raise ValueError('policy shape')
    for key, peer in policy['allow'].items():
        if authority(key)!=key or not isinstance(peer,list) or len(peer)!=2: raise ValueError('policy entry')
        ipaddress.ip_address(peer[0])
        if type(peer[1]) is not int or not 1<=peer[1]<=65535: raise ValueError('peer port')
        # Safe test-only defaults. No public destination or DNS resolution permitted.
        if not ipaddress.ip_address(peer[0]).is_loopback: raise ValueError('test gateway accepts loopback fixtures only')
    for key in ('socket','log'):
        if not isinstance(policy[key],str) or not Path(policy[key]).is_absolute(): raise ValueError('absolute path required')
    if Path(policy['socket']).exists(): raise ValueError('refuse to replace existing socket')
    return policy


class Gateway:
    def __init__(self, policy):
        self.policy = policy
        self.logfile = open(policy['log'],'a',buffering=1)
        self.serial = 0
        self.active = 0

    def log(self, **event): self.logfile.write(json.dumps({'t':time.time(),'pid':os.getpid(),**event})+'\n')

    async def copy(self, reader, writer):
        try:
            while True:
                data = await asyncio.wait_for(reader.read(65536),5)
                if not data: break
                writer.write(data); await writer.drain()
        except (OSError,asyncio.TimeoutError): pass
        finally:
            try: writer.write_eof()
            except (OSError,RuntimeError): pass

    async def handle(self, reader, writer):
        self.serial += 1; cid = self.serial
        upstream = None; connecting_socket = None
        entered = False
        try:
            if self.active>=64: raise Rejected('busy')
            self.active+=1; entered = True
            deadline = asyncio.get_running_loop().time()+2
            async def bounded_line():
                remaining = deadline-asyncio.get_running_loop().time()
                if remaining<=0: raise asyncio.TimeoutError
                return await asyncio.wait_for(reader.readline(),remaining)
            line = await bounded_line()
            headers = []; total = 0
            while True:
                header = await bounded_line()
                if header==b'\r\n': break
                if not header: raise Rejected('truncated headers')
                total += len(header)
                if total>MAX_HEADERS: raise Rejected('headers too large')
                headers.append(header)
            method,dest,path,fields,length = parse(line,headers)
            if dest not in self.policy['allow']: raise Rejected('not_allowlisted')
            ip,port = self.policy['allow'][dest]
            # Permission decision precedes socket creation. Only numeric pinned addresses reach open_connection.
            self.log(cid=cid,decision='allow',dest=dest,ip=ip,port=port,protocol='tcp',method=method)
            family = socket.AF_INET6 if ':' in ip else socket.AF_INET
            connecting_socket = socket.socket(family,socket.SOCK_STREAM)
            connecting_socket.setblocking(False)
            connecting_socket.bind(('::1' if family==socket.AF_INET6 else '127.0.0.1',0))
            local = connecting_socket.getsockname()
            self.log(cid=cid,decision='attempt',ip=ip,port=port,protocol='tcp',source_ip=local[0],source_port=local[1])
            await asyncio.wait_for(asyncio.get_running_loop().sock_connect(connecting_socket,(ip,port)),2)
            ur, upstream = await asyncio.open_connection(sock=connecting_socket)
            connecting_socket = None
            peer = upstream.get_extra_info('peername')
            if peer[0]!=ip or peer[1]!=port: raise RuntimeError('peer differs from pinned policy')
            self.log(cid=cid,decision='connected',ip=peer[0],port=peer[1],protocol='tcp')
            if method=='CONNECT':
                writer.write(b'HTTP/1.1 200 Connection Established\r\n\r\n'); await writer.drain()
                await asyncio.wait_for(asyncio.gather(self.copy(reader,upstream), self.copy(ur,writer)),10)
            else:
                request = f'{method} {path} HTTP/1.0\r\nHost: {dest}\r\nConnection: close\r\nContent-Length: {length}\r\n'
                request += ''.join(f'{k}: {v}\r\n' for k,v in fields)+'\r\n'
                upstream.write(request.encode('ascii'))
                if length: upstream.write(await asyncio.wait_for(reader.readexactly(length),2))
                await upstream.drain()
                # One request per connection. Pipelined/trailing bytes are not forwarded.
                await self.copy(ur,writer)
        except (Rejected,ValueError,asyncio.LimitOverrunError) as e:
            self.log(cid=cid,decision='deny',reason=str(e)[:200])
            writer.write(b'HTTP/1.1 403 Forbidden\r\nContent-Length: 0\r\nConnection: close\r\n\r\n')
            try: await writer.drain()
            except OSError: pass
        except Exception as e:
            self.log(cid=cid,decision='error',reason=type(e).__name__)
        finally:
            if entered: self.active-=1
            if connecting_socket: connecting_socket.close()
            if upstream:
                upstream.close()
                try: await upstream.wait_closed()
                except OSError: pass
            writer.close()
            try: await writer.wait_closed()
            except OSError: pass

    async def serve(self):
        old_umask = os.umask(0o077)
        try: server = await asyncio.start_unix_server(self.handle,path=self.policy['socket'],limit=MAX_LINE)
        finally: os.umask(old_umask)
        # The launcher mounts this single endpoint; local host users are outside the test threat model.
        os.chmod(self.policy['socket'],0o666)
        async with server: await server.serve_forever()


if __name__=='__main__':
    asyncio.run(Gateway(load_policy(sys.argv[1])).serve())
