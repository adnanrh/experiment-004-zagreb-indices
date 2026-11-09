#!/usr/bin/env python3
"""Independent integer adjacency-matrix and coefficient audit (NOT Lean).
Does not import any verifier or constructor from the supplied package.
"""
from __future__ import annotations
from collections import Counter
from fractions import Fraction
from itertools import combinations, combinations_with_replacement
from pathlib import Path
import json
import zipfile

ROOT = Path(__file__).resolve().parents[1]


def main() -> None:
    with zipfile.ZipFile(ROOT / 'input/original_verification.zip') as z:
        names = [n for n in z.namelist() if n.endswith('/example_certificates.json')]
        if len(names) != 1:
            raise ValueError('Expected a unique certificate file')
        data = json.loads(z.read(names[0]))
    results = []
    for cert in data['certificates']:
        n = cert['n']
        if type(n) is not int or n < 1:
            raise ValueError('Invalid vertex count')
        mat = [[0] * n for _ in range(n)]
        for edge in cert['edges']:
            if len(edge) != 2 or any(type(v) is not int for v in edge):
                raise ValueError('Invalid edge')
            u, v = edge
            if not (0 <= u < n and 0 <= v < n) or u == v or mat[u][v]:
                raise ValueError('Invalid or duplicate edge')
            mat[u][v] = mat[v][u] = 1
        deg = [sum(row) for row in mat]
        m = sum(deg) // 2
        first = sum(x*x for x in deg)
        twice_second = sum(deg[u]*mat[u][v]*deg[v]
                           for u in range(n) for v in range(n))
        assert twice_second % 2 == 0
        second = twice_second // 2
        # Warshall transitive closure, with bitsets as an independent algorithm.
        reach = [sum(row[j] << j for j in range(n)) | (1 << i)
                 for i, row in enumerate(mat)]
        for k in range(n):
            for i in range(n):
                if (reach[i] >> k) & 1:
                    reach[i] |= reach[k]
        connected = all(mask == (1 << n) - 1 for mask in reach)
        counts = Counter(tuple(sorted((deg[u], deg[v])))
                         for u in range(n) for v in range(u+1, n) if mat[u][v])
        result = {'id': cert['id'], 'n': n, 'm': m, 'M1': first, 'M2': second,
                  'gap': m*first - n*second, 'connected': connected,
                  'minimum_degree': min(deg), 'maximum_degree': max(deg),
                  'edge_types': {f'{i},{j}': v for (i,j),v in sorted(counts.items())}}
        for key in ('n','m','M1','M2','gap','connected','minimum_degree','maximum_degree','edge_types'):
            assert result[key] == cert['expected'][key], (cert['id'], key)
        assert connected and min(deg) == 2 and max(deg) == 5 and result['gap'] > 0
        results.append(result)
    types = list(combinations_with_replacement(range(2,6),2))
    def q(t): return t[0]*t[1]
    def r(t): return Fraction(1,t[0])+Fraction(1,t[1])
    table = [(a,b,(q(a)-q(b))*(r(b)-r(a))) for a,b in combinations(types,2)]
    negative = [(a,b,str(x)) for a,b,x in table if x < 0]
    assert negative == [((2,5),(3,3),'-1/30')]
    assert all(x != 0 for _,_,x in table)
    output = {'status':'PASS_PYTHON_NOT_LEAN', 'method':'integer adjacency matrix and bitset Warshall closure',
              'certificate_count':len(results), 'certificates':results,
              'coefficient_pairs':len(table), 'negative_coefficients':negative,
              'positive_coefficient_count':sum(x>0 for _,_,x in table)}
    # Optional independent symbolic test of all 45 pair coefficients together.
    try:
        import sympy as sp
        x = sp.symbols('x0:10')
        conv = lambda f: sp.Rational(f.numerator,f.denominator)
        N = sum(conv(r(t))*v for t,v in zip(types,x))
        M = sum(x)
        M1 = sum(sum(t)*v for t,v in zip(types,x))
        M2 = sum(q(t)*v for t,v in zip(types,x))
        decomposition = -sum(conv((q(types[i])-q(types[j]))*(r(types[j])-r(types[i])))*x[i]*x[j]
                             for i in range(10) for j in range(i+1,10))
        assert sp.expand(M*M1-N*M2-decomposition) == 0
        k,l = sp.symbols('k l')
        n = (7*k+4*l+3)/2
        m = 5*k+3*l+2
        assert sp.expand(m*(35*k+18*l+11)-n*(50*k+27*l+15)-(k*l-5*k-3*l-1)/2) == 0
        output['symbolic_identity'] = 'PASS (SymPy; not a Lean proof)'
    except ImportError:
        output['symbolic_identity'] = 'NOT_RUN: SymPy not installed'
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()
