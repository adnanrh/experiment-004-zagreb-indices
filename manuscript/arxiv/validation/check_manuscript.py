"""Exact checks of the manuscript's coefficients and labeled constructions.
No Lean source, graph certificate, or historical artifact is changed.
Run from any directory with Python 3.10+; only the standard library is used.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import combinations
from collections import Counter
import ast, json, re
R=Path(__file__).resolve().parents[3]

def edge(u,v):
    assert u != v
    return tuple(sorted((u,v)))

def lean_edges(text):
    block=re.search(r'def edgeList.*?:=\s*(\[.*?\])', text, re.S).group(1)
    es=ast.literal_eval(block)
    result={edge(*e) for e in es}
    assert len(es)==len(result)
    return result

def invariants(n,es):
    adj=[set() for _ in range(n)]
    for u,v in es:
        assert 0<=u<v<n
        adj[u].add(v); adj[v].add(u)
    seen={0}; stack=[0]
    while stack:
        for w in adj[stack.pop()]-seen:
            seen.add(w); stack.append(w)
    assert len(seen)==n
    ds=list(map(len,adj))
    assert min(ds)==2 and max(ds)==5
    m=len(es); m1=sum(d*d for d in ds); m2=sum(ds[u]*ds[v] for u,v in es)
    profile=Counter(tuple(sorted((ds[u],ds[v]))) for u,v in es)
    return (n,m,m1,m2,m*m1-n*m2), profile

# Exactly the labeled construction in manuscript Section 5.
hubs=[e for e in combinations(range(7),2) if e not in [(0,1),(0,2),(3,4),(5,6)]]
witness=set()
for x,(u,v) in enumerate(hubs,7): witness.update([edge(u,x),edge(v,x)])
witness.update([edge(0,24),edge(24,45)])
for base in (25,35):
    witness.update(edge(base+i,base+(i+1)%10) for i in range(10))
witness.update(edge(i,i+10) for i in range(25,35))
witness.remove(edge(25,26)); witness.update([edge(25,45),edge(45,26)])
assert witness==lean_edges((R/'Zagreb004/Witness.lean').read_text())
wi,wp=invariants(46,witness)
assert wi==(46,67,436,635,2)
assert wp=={(2,5):35,(3,3):31,(2,3):1}

# Section 6 core labels match both actual finite Lean cores exactly.
cores={}
source=(R/'Zagreb004/Cores.lean').read_text()
for k in (5,7):
    es=set()
    for i in range(k):
        for epsilon in (0,1):
            x=k+2*i+epsilon
            es.update([edge(i,x),edge((i+1)%k,x)])
    for j in range(1,(k-1)//2+1):
        y=3*k+j-1; es.update([edge(2*j-1,y),edge(2*j,y)])
    u=(7*k-1)//2; es.add(edge(0,u))
    assert es==lean_edges(source.split('namespace Core'+str(k))[1])
    cores[k]=es

orders=list(range(46,301))+[1000,1001,10000,10001]
for n in orders:
    k=7 if n%2==0 else 5
    l=(n-26)//2 if k==7 else (n-19)//2
    c=(7*k+1)//2; u=c-1; w=c+2*l
    es=set(cores[k])
    for i in range(l):
        for b in (0,1): es.add(edge(c+2*i+b,c+2*((i+1)%l)+b))
        if i: es.add(edge(c+2*i,c+2*i+1))
    es.update([edge(c,w),edge(c+1,w),edge(u,w)])
    inv,profile=invariants(n,es)
    assert profile=={(2,5):5*k,(3,3):3*l+1,(2,3):1}
    assert inv==(n,5*k+3*l+2,35*k+18*l+11,50*k+27*l+15,(k*l-5*k-3*l-1)//2)
    assert inv[-1]==(n-44 if k==7 else (n-45)//2)>0

# All coefficients: computed from the defining Zagreb sums, then compared
# to the actual Lean A, B, C polynomial coefficients, not historical tables.
types=list(combinations(range(2,6),2))+[(i,i) for i in range(2,6)]
def psi(t,u):
    qt=t[0]*t[1]; qu=u[0]*u[1]
    rt=Q(1,t[0])+Q(1,t[1]); ru=Q(1,u[0])+Q(1,u[1])
    return (qt-qu)*(ru-rt)
assert [set(p) for p in combinations(types,2) if psi(*p)<0]==[{(2,5),(3,3)}]
f=[(2,2),(2,3),(2,4),(3,4),(3,5),(4,4),(4,5),(5,5)]
A=[int(60*psi((2,5),t)) for t in f]; B=[int(60*psi((3,3),t)) for t in f]
assert A==[108,32,6,14,50,72,150,270]
assert B==[100,30,5,15,48,70,143,256]
assert psi((2,4),(3,4))==Q(2,3)
s=(R/'Zagreb004/Profiles.lean').read_text()
for label,coeffs in [('A',A),('B',B)]:
    body=s.split('def penalty'+label+'60')[1].split('\ndef ')[0]
    parsed={t:int(v) for v,t in re.findall(r'(\d+)\s*\*\s*c\.e(\d\d)',body)}
    assert parsed=={str(i)+str(j):v for (i,j),v in zip(f,coeffs)}
body=s.split('def penaltyC60')[1].split('/--')[0]
parsed={(t,u):int(v) for v,t,u in re.findall(r'(\d+)\s*\*\s*c\.e(\d\d)\s*\*\s*c\.e(\d\d)',body)}
assert parsed=={(str(t[0])+str(t[1]),str(u[0])+str(u[1])):int(60*psi(t,u)) for t,u in combinations(f,2)}
# The three rows of the final integrality argument.
for a,b,n in [(25,43,47),(35,31,46),(45,25,49)]:
    assert a%10==5 and b%3==1
    assert a*b>16*a+15*b
    assert a*(b-3)<=16*a+15*(b-3)
    assert 21*a+20*b+25==30*n
print(json.dumps({'status':'PASS','witness_matches_Lean_edge_list':True,'witness_invariants':wi,
    'both_fixed_core_edge_lists_match_Lean':True,'family_orders_checked':len(orders),
    'all_scaled_penalty_coefficients_match_Lean':True,'integrality_table':'PASS',
    'scope':'Exact manuscript consistency checks, not a new formal proof or external peer review.'},indent=2))
