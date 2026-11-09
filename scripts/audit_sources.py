#!/usr/bin/env python3
"""Static policy scan only. NOT a Lean parser, compiler, or axiom dependency audit."""
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parents[1]

def strip_comments_and_strings(s: str) -> str:
    out=[]
    i=0
    depth=0
    while i<len(s):
        if depth:
            if s.startswith('/-',i): depth+=1; i+=2
            elif s.startswith('-/',i): depth-=1; i+=2
            else:
                if s[i]=='\n': out.append('\n')
                i+=1
        elif s.startswith('/-',i): depth=1; out.append(' '); i+=2
        elif s.startswith('--',i):
            j=s.find('\n',i)
            i=len(s) if j==-1 else j
        elif s[i]=='"':
            out.append(' ')
            i+=1
            while i<len(s):
                if s[i]=='\\': i+=2
                elif s[i]=='"': i+=1; break
                else: i+=1
        else: out.append(s[i]); i+=1
    if depth:
        raise ValueError('Unclosed block comment')
    return ''.join(out)

def main():
    results=[]
    bad=re.compile(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|run_tac)\b|debug\.skipKernelTC')
    files=[ROOT/'Zagreb004.lean',ROOT/'Audit.lean',*sorted((ROOT/'Zagreb004').glob('*.lean'))]
    for p in files:
        s=strip_comments_and_strings(p.read_text())
        hits=[m.group() for m in bad.finditer(s)]
        results.append({'file':str(p.relative_to(ROOT)),'forbidden_tokens':hits})
    output={'status':'PASS_STATIC_SCAN_ONLY' if all(not r['forbidden_tokens'] for r in results) else 'FAIL',
            'lean_executed':False,'semantic_axiom_audit_performed':False,'files':results}
    print(json.dumps(output,indent=2))
    if output['status']=='FAIL': raise SystemExit(1)

if __name__=='__main__': main()
