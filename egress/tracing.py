"""Parse host strace connect records, independent of gateway decisions."""
import re


def connects(text):
    records = []
    for line in text.splitlines():
        if 'connect(' not in line or 'sa_family=AF_INET' not in line: continue
        timestamp = re.search(r'(\d+\.\d+)\s+connect\(',line)
        ipv6 = 'sa_family=AF_INET6' in line
        ip = re.search(r'inet_pton\(AF_INET6, "([^"]+)"',line) if ipv6 else re.search(r'inet_addr\("([^"]+)"\)',line)
        port = re.search(r'sin6_port=htons\((\d+)\)',line) if ipv6 else re.search(r'sin_port=htons\((\d+)\)',line)
        if not (timestamp and ip and port): raise ValueError('unparsed network connect trace: '+line)
        records.append({'t':float(timestamp.group(1)), 'ip':ip.group(1), 'port':int(port.group(1)), 'protocol':'tcp', 'raw':line})
    return records


def check(records, decisions, policy):
    allowed = {(ip,port) for ip,port in policy['allow'].values()}
    permits = [d for d in decisions if d.get('decision')=='allow']
    remaining = list(permits); errors = []
    for r in records:
        if (r['ip'],r['port']) not in allowed: errors.append('gateway syscall to forbidden peer')
        matches = [d for d in remaining if d['ip']==r['ip'] and d['port']==r['port'] and d['t']<=r['t']]
        if not matches: errors.append('gateway connect without preceding permit')
        else: remaining.remove(matches[0])
    if remaining: errors.append('permit without independently traced connect')
    return errors
