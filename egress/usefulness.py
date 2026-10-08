"""Pinned pure-Python wheel fetch, install, compile and test through HTTP proxy."""
import base64
import hashlib
import io
import json
from pathlib import Path
import subprocess
import sys
import urllib.request
import zipfile


def wheel():
    files = {
        'sc03_fixture/__init__.py': 'def double(n):\n    return 2*n\n',
        'sc03_fixture-1.0.dist-info/METADATA': 'Metadata-Version: 2.1\nName: sc03-fixture\nVersion: 1.0\n',
        'sc03_fixture-1.0.dist-info/WHEEL': 'Wheel-Version: 1.0\nGenerator: control-stack\nRoot-Is-Purelib: true\nTag: py3-none-any\n',
    }
    rows = []
    for path,data in files.items():
        digest = base64.urlsafe_b64encode(hashlib.sha256(data.encode()).digest()).decode().rstrip('=')
        rows.append(f'{path},sha256={digest},{len(data.encode())}')
    files['sc03_fixture-1.0.dist-info/RECORD'] = '\n'.join(rows)+'\nsc03_fixture-1.0.dist-info/RECORD,,\n'
    buffer = io.BytesIO()
    with zipfile.ZipFile(buffer,'w') as z:
        for path,data in sorted(files.items()):
            info = zipfile.ZipInfo(path,(2026,10,8,0,0,0)); z.writestr(info,data)
    return buffer.getvalue()


def task(config):
    opener = urllib.request.build_opener(urllib.request.ProxyHandler({'http':'http://127.0.0.1:3128'}))
    url = 'http://mirror.internal:80/packages/sc03_fixture-1.0-py3-none-any.whl'
    with opener.open(url,timeout=5) as response: data = response.read()
    digest = hashlib.sha256(data).hexdigest()
    assert digest==config['wheel_sha256'], 'dependency digest mismatch'
    install = Path('/tmp/dependency'); install.mkdir()
    with zipfile.ZipFile(io.BytesIO(data)) as z:
        for name in z.namelist():
            assert not name.startswith('/') and '..' not in Path(name).parts
        z.extractall(install)
    subprocess.run([sys.executable,'-m','compileall','-q',str(install)],check=True)
    test = install/'test_dependency.py'
    test.write_text('from sc03_fixture import double\nassert double(21)==42\nassert double(-3)==-6\nprint("dependency tests passed")\n')
    result = subprocess.run([sys.executable,str(test)],capture_output=True,text=True,check=True)
    return {'task':'sc03-fixture/1.0 wheel install/compile/test', 'sha256':digest, 'test_output':result.stdout.strip(), 'local_task':True}
