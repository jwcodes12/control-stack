"""Deliberately narrow HTTP/1 proxy grammar; see README.md for the contract."""
import ipaddress
import re
from urllib.parse import urlsplit

MAX_LINE = 8192
MAX_HEADERS = 32768
NAME = re.compile(r'[a-z0-9](?:[a-z0-9.-]*[a-z0-9])?\Z')
TOKEN = re.compile(r"[!#$%&'*+.^_`|~0-9A-Za-z-]+\Z")


class Rejected(ValueError): pass


def authority(value, default_port=None):
    # DNS labels only: literals, escapes, userinfo, IPv6 and trailing dots are excluded.
    if any(c in value for c in '@/#?\\%') or value.count(':') > 1: raise Rejected('authority')
    parts = value.lower().split(':')
    name = parts[0]
    if not NAME.fullmatch(name) or '..' in name or any(not part or len(part)>63 or part.startswith('-') or part.endswith('-') for part in name.split('.')): raise Rejected('hostname')
    try: ipaddress.ip_address(name)
    except ValueError: pass
    else: raise Rejected('literal')
    if len(parts)==1:
        if default_port is None: raise Rejected('missing port')
        port = default_port
    else:
        raw = parts[1]
        if not raw.isascii() or not raw.isdigit() or raw.startswith('0') or len(raw)>5: raise Rejected('port')
        port = int(raw)
    if not 1 <= port <= 65535: raise Rejected('port range')
    return name+':'+str(port)


def parse(line, headers):
    if not line.endswith(b'\r\n') or len(line)>MAX_LINE: raise Rejected('request line')
    try: text = line[:-2].decode('ascii')
    except UnicodeDecodeError: raise Rejected('nonascii line')
    if any(ord(c)<32 or ord(c)==127 for c in text): raise Rejected('control')
    parts = text.split(' ')
    if len(parts)!=3 or parts[2] not in ('HTTP/1.0','HTTP/1.1'): raise Rejected('version/spacing')
    method, target, version = parts
    if method not in ('GET','HEAD','POST','CONNECT'): raise Rejected('method')
    if method=='CONNECT':
        dest = authority(target); path = None
    else:
        if not target.startswith('http://') or '#' in target or '\\' in target: raise Rejected('URI')
        raw_authority = target[7:].split('/',1)[0].split('?',1)[0]
        dest = authority(raw_authority,80)
        parsed = urlsplit(target)
        path = (parsed.path or '/') + ('?'+parsed.query if parsed.query else '')
    fields = []; seen = set(); length = 0
    if sum(map(len,headers))>MAX_HEADERS: raise Rejected('headers too large')
    for raw in headers:
        if not raw.endswith(b'\r\n') or raw.startswith((b' ',b'\t')): raise Rejected('folding/newline')
        try: key, value = raw[:-2].decode('ascii').split(':',1)
        except (UnicodeDecodeError,ValueError): raise Rejected('header')
        if not TOKEN.fullmatch(key) or any(ord(c)<32 or ord(c)==127 for c in value): raise Rejected('header syntax')
        key = key.lower(); value = value.strip()
        if key in seen: raise Rejected('duplicate header')
        seen.add(key)
        if key in ('transfer-encoding','upgrade','expect','trailer'): raise Rejected('unsupported framing')
        if key=='host' and authority(value,80)!=dest: raise Rejected('host mismatch')
        if key=='content-length':
            if not value.isascii() or not value.isdigit() or len(value)>7: raise Rejected('content length')
            length = int(value)
            if length>1048576: raise Rejected('body too large')
        if key not in ('host','connection','proxy-connection','proxy-authorization','content-length'):
            fields.append((key,value))
    if method in ('CONNECT','GET','HEAD') and length: raise Rejected('unexpected body')
    return method, dest, path, fields, length
