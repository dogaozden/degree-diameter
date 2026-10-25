#!/usr/bin/env python3
"""c8 (round 2): build Omega-B1 with B1 = incidence graph of H(7), from thesis pp. 44-45 (Figs 2.21a, 2.21b).

Vertices: copies (g,c,x): group g in 0..G-1, copy c in Z5, base vertex x of B1 (points 0..n-1, lines n..2n-1).
          new vertices (p,x): p in Z5 (5 new vertices per base vertex x).
Group type (each group of 5 copies is Fig 2.21a 'A' or Fig 2.21b 'B'):
  A: point-type new vertex (p,x), x a point, joins copies {p-1,p+1} (pentagram chords);
     line-type (p,x) joins copies {p+2,p+3} (pentagon sides).
  B: line-type (p,x) joins copies {p-1,p+1} (chords); point-type (p,x) joins copies {p+3,p+4}.
Each new vertex gets 2 neighbours per group (degree 2G); each copy vertex gets 2 new neighbours (degree 8+2=10).
usage: mk_om7.py TYPES [OUTFILE]   e.g. TYPES=AAAAA
"""
import sys
import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import shortest_path
sys.path.insert(0, '/home/user/degree-diameter/research/d12D8/tools')
from hexlib import load_hex

types = sys.argv[1] if len(sys.argv) > 1 else 'AAAAA'
out = sys.argv[2] if len(sys.argv) > 2 else \
    f'/home/user/degree-diameter/research/squads/d12D8_r2/c8/om7_{types}.txt'
q = 7
n, lines = load_hex(q)
N1 = 2 * n
pts = lines.reshape(-1).astype(np.int64)
lns = np.repeat(np.arange(n, dtype=np.int64), q + 1) + n
E1 = np.stack([pts, lns], axis=1)
assert (np.bincount(E1.ravel(), minlength=N1) == q + 1).all()
assert len(np.unique(E1[:, 0] * N1 + E1[:, 1])) == len(E1)

# B1 sanity: diameter (expect 6); points and lines are each one orbit for H(q), so a few sources suffice
A = csr_matrix((np.ones(len(E1)), (E1[:, 0], E1[:, 1])), shape=(N1, N1))
A = (A + A.T).tocsr()
d = shortest_path(A, unweighted=True, indices=[0, n, 12345, n + 777])
print('B1: n_points', n, 'N1', N1, 'ecc of sources (point0, line0, ...):', d.max(axis=1), flush=True)

G = len(types)
C = 5
NC = G * C
V = (NC + 5) * N1
def copy_off(g, c): return (g * C + c) * N1
def new_off(p): return NC * N1 + p * N1

def pattern(T, is_line, p):
    chord = (T == 'A') != is_line          # A&point -> chord, B&line -> chord
    if chord:
        return ((p - 1) % 5, (p + 1) % 5)
    if T == 'A':                            # line in A
        return ((p + 2) % 5, (p + 3) % 5)
    return ((p + 3) % 5, (p + 4) % 5)       # point in B

ptsv = np.arange(n, dtype=np.int64)
lnsv = np.arange(n, 2 * n, dtype=np.int64)
parts = [E1 + k * N1 for k in range(NC)]
for g, T in enumerate(types):
    assert T in 'AB'
    for p in range(5):
        for is_line, ids in ((False, ptsv), (True, lnsv)):
            for c in pattern(T, is_line, p):
                parts.append(np.stack([new_off(p) + ids, copy_off(g, c) + ids], axis=1))
E = np.concatenate(parts)
del parts
m = len(E)
print('V', V, 'E', m, 'expected E', V * 10 // 2, flush=True)

deg = np.bincount(E.ravel(), minlength=V)
print('degree min/max', deg.min(), deg.max(), 'all 10:', bool((deg == 10).all()), flush=True)
keys = np.minimum(E[:, 0], E[:, 1]) * V + np.maximum(E[:, 0], E[:, 1])
print('simple (no multi-edges):', len(np.unique(keys)) == m, flush=True)
del keys
# bipartition: copy vertices coloured by point(0)/line(1); a new vertex is opposite to its neighbours
v = np.arange(V, dtype=np.int64)
col = np.zeros(V, dtype=np.int8)
cp = v < NC * N1
col[cp] = ((v[cp] % N1) >= n).astype(np.int8)
nw = ~cp
xb = (v[nw] - NC * N1) % N1
col[nw] = (xb < n).astype(np.int8)           # point-type new vertex -> colour 1, line-type -> colour 0
print('bipartite (explicit 2-colouring valid):', bool((col[E[:, 0]] != col[E[:, 1]]).all()), flush=True)

with open(out, 'w') as f:
    f.write(f"{V}\n")
    np.savetxt(f, E, fmt='%d')
print('wrote', out, flush=True)
print('sources: new(p0,point0)=', new_off(0) + 0, ' new(p0,line0)=', new_off(0) + n,
      ' copy(g0,c0,point0)=', copy_off(0, 0) + 0, ' copy(g0,c0,line0)=', copy_off(0, 0) + n, flush=True)
