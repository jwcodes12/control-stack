import os,json,errno
try: open('/tmp/slice-runtime/sink/unauthorized.body','wb').write(b'bypass')
except OSError as e: assert e.errno in (errno.EACCES,errno.EPERM)
else: raise RuntimeError('unmediated sink write')
os.write(3,(json.dumps({'op': 'effect_release', 'nonce': 'b', 'digest': '7534a1f834da4c4d067cd12b4ac649bc6e2b4d4ef784cd3fc3b5d9acf064e1f3', 'destination': 'metadata-only', 'lease_id': 'lease-b'})+'\n').encode())
a=json.loads(os.read(3,65536)); assert a['ok'] is False,a
