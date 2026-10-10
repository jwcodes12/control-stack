import errno
try: open('/tmp/slice-runtime/sink/confined-mutation.body','wb').write(b'bad')
except OSError as e: assert e.errno in (errno.EPERM,errno.EACCES)
else: raise RuntimeError('confinement failed')
