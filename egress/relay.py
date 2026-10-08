"""Untrusted in-sandbox loopback adapter. No policy or external network authority."""
import asyncio

async def pipe(reader, writer):
    try:
        while True:
            data = await reader.read(65536)
            if not data: break
            writer.write(data); await writer.drain()
    except (OSError,RuntimeError): pass
    finally:
        try: writer.write_eof()
        except (OSError,RuntimeError): pass

async def handle(reader, writer):
    upstream = None
    try:
        ur,upstream = await asyncio.open_unix_connection('/run/egress.sock')
        await asyncio.gather(pipe(reader,upstream),pipe(ur,writer))
    except OSError: pass
    finally:
        if upstream: upstream.close()
        writer.close()

async def main():
    server = await asyncio.start_server(handle,'127.0.0.1',3128)
    async with server: await server.serve_forever()

if __name__=='__main__': asyncio.run(main())
