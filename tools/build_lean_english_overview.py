#!/usr/bin/env python3
"""Assemble docs/LEAN-CLAIMS-IN-PLAIN-ENGLISH.md (per-scenario summary tables) from docs/lean-english/part-g*.md.
The part files hold the full per-claim blocks; this script only extracts headers and first sentences, so the overview cannot say more than they do."""
import re
import sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
PREAMBLE=ROOT/'docs/lean-english/OVERVIEW-PREAMBLE.md'

def sections(text):
    return re.split(r'\n(?=#{1,2} (?:Scenario )?(?:SC-\d+|DEPLOY))',text)[1:]

def build():
    out=[];total=0
    for p in sorted((ROOT/'docs/lean-english').glob('part-g*.md')):
        for sec in sections(p.read_text()):
            head,*blocks=re.split(r'\n(?=### )',sec)
            title=re.sub(r'^#+ (Scenario )?','',head.splitlines()[0]);title=re.sub(r'\s*\(status:.*\)','',title)
            harm=re.search(r'\*\*Harm[^*]*\*\*\s*(.*)',head);tog=re.search(r'\*\*What the Lean claims[^*]*\*\*\s*(.*)',head)
            out.append('## '+title+'\n')
            if harm:out.append('**Harm.** '+harm.group(1).strip()+'\n')
            if tog:out.append('**In short.** '+tog.group(1).strip()+'\n')
            out.append('| Lean claim | In plain English (first sentence) | Kind |\n|---|---|---|')
            for b in blocks:
                m=re.match(r'### `?([^`\n—]+?)`?\s*(?:—|$)',b.splitlines()[0])
                if not m:continue
                says=re.search(r'\*\*Says[^*]*\*\*\s*(.*)',b);kind=re.search(r'\*\*Kind:?\*\*:?\s*(.*)',b)
                first=re.split(r'(?<=[.!?])\s',says.group(1).strip())[0] if says else ''
                k=re.sub(r'\s*[\(—].*','',kind.group(1)).strip('` *') if kind else '?'
                out.append('| `'+m.group(1).strip().replace('ControlStack.','')+'` | '+first.replace('|','/')+' | '+k+' |');total+=1
            out.append('')
    return total,'\n'.join(out)

if __name__=='__main__':
    total,body=build()
    pre=PREAMBLE.read_text().replace('{TOTAL}',str(total))
    text=pre+'\n'+body+'\n'
    target=ROOT/'docs/LEAN-CLAIMS-IN-PLAIN-ENGLISH.md'
    if '--check' in sys.argv:
        if not target.exists() or target.read_text()!=text:raise SystemExit('stale overview: run tools/build_lean_english_overview.py')
        print('overview consistent:',total,'claims')
    else:target.write_text(text);print('wrote',target,total,'claims')
