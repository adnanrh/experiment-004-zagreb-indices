#!/usr/bin/env python3
"""Read the actual generated Lean polynomial text and cross-check it with SymPy.
This checks arithmetic data, NOT Lean syntax, elaboration, or kernel acceptance.
"""
from pathlib import Path
import json
import re
import sympy as sp
ROOT=Path(__file__).resolve().parents[1]
text=(ROOT/'Zagreb004/Profiles.lean').read_text()
names=['order60','profileSize','profileM1','profileM2','penaltyA60','penaltyB60','penaltyC60']
fields=['e22','e23','e24','e25','e33','e34','e35','e44','e45','e55']
syms=dict(zip(fields,sp.symbols(' '.join(fields))))
expr={}
for name in names:
    pattern=rf'def {name} \(c : Counts\) : ℕ :=\n(.*?)(?=\n\n)'
    match=re.search(pattern,text,re.S)
    if not match: raise ValueError(f'Missing definition {name}')
    raw=match.group(1).replace('c.','').strip()
    if re.search(r'[^0-9a-z+*\s]',raw): raise ValueError('Unexpected expression character')
    expr[name]=sp.sympify(raw,locals=syms)
a,b=syms['e25'],syms['e33']
left=60*expr['profileSize']*expr['profileM1']-expr['order60']*expr['profileM2']
right=2*a*b-expr['penaltyA60']*a-expr['penaltyB60']*b-expr['penaltyC60']
if sp.expand(left-right)!=0: raise ValueError('Generated polynomial identity is false')
canonical={syms[f]:0 for f in fields}
canonical.update({syms['e23']:1,a:35,b:31})
observed={name:int(e.subs(canonical)) for name,e in expr.items()}
expected={'order60':2760,'profileSize':67,'profileM1':436,'profileM2':635,'penaltyA60':32,'penaltyB60':30,'penaltyC60':0}
if observed!=expected: raise ValueError((observed,expected))
case2={syms[f]:0 for f in fields if f not in ['e25','e33']}
case2[syms['e24']]=3
case2[syms['e34']]=1
if sp.expand(expr['penaltyC60'].subs(case2)-120)!=0: raise ValueError('Wrong pattern II cost')
print(json.dumps({'status':'PASS_SYMBOLIC_CHECK_NOT_LEAN',
    'arbitrary_profile_polynomial_identity':True,
    'patternII_constant_scaled60':120,'canonical_profile_values':observed},indent=2))
