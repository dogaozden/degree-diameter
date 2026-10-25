#!/usr/bin/env python3
"""c8: independent check (scipy Dijkstra with unit weights) of eccentricities and of the claim:
a new vertex v = x_p (x a base vertex) is at distance >= 9 from every vertex opposite x (distance 6 in B1)
lying in a copy of a group that v is NOT adjacent to. usage: check_claim.py EDGEFILE TYPES"""
import sys
import numpy as np
from scipy.sparse import csr_matrix
from scipy.sparse.csgraph import shortest_path
sys.path.insert(0, '/home/user/degree-diameter/research/d12D8/tools')
from hexlib import load_hex

path, types = sys.argv[1], sys.argv[2]
n, lines = load_hex(7)
N1 = 2 * n
pts = lines.reshape(-1).astype(np.int64)
lns = np.repeat(np.arange(n, dtype=np.int64), 8) + n
E1 = np.stack([pts, lns], axis=1)
B = csr_matrix((np.ones(len(E1)), (E1[:, 0], E1[:, 1])), shape=(N1, N1))
B = (B + B.T).tocsr()
dB = shortest_path(B, unweighted=True, indices=[0, n])          # from point 0 and from line 0
print('B1 ecc(point0), ecc(line0):', dB.max(axis=1), ' #opposite points of point0:', int((dB[0] == 6).sum()),
      ' #opposite lines of line0:', int((dB[1] == 6).sum()), flush=True)
opp_pt = np.where(dB[0] == 6)[0]     # points at distance 6 from point 0
opp_ln = np.where(dB[1] == 6)[0]     # lines at distance 6 from line 0

data = np.loadtxt(path, dtype=np.int64, skiprows=1)
V = int(open(path).readline())
G = len(types); C = 5; NC = G * C
A = csr_matrix((np.ones(len(data)), (data[:, 0], data[:, 1])), shape=(V, V))
A = (A + A.T).tocsr()
print('loaded V', V, 'edges', len(data), flush=True)

def pattern(T, is_line, p):
    chord = (T == 'A') != is_line
    if chord:
        return ((p - 1) % 5, (p + 1) % 5)
    if T == 'A':
        return ((p + 2) % 5, (p + 3) % 5)
    return ((p + 3) % 5, (p + 4) % 5)

def copy_vertex(g, c, x):
    return (g * C + c) * N1 + x

for name, v, is_line, opp in (('new point-type (p0,point0)', 0 * N1 + NC * N1 + 0, False, opp_pt),
                              ('new line-type (p0,line0)', NC * N1 + n, True, opp_ln)):
    d = shortest_path(A, unweighted=True, indices=[v])[0]
    d = d.astype(np.int64)
    cnt = np.bincount(d)
    print(f'{name}: vertex {v}: ecc {d.max()}, counts by distance {cnt.tolist()}', flush=True)
    x = 0 if not is_line else n
    x_is_line = is_line
    # v = new(p=0, x): adjacent copies per group
    res = []
    for g, T in enumerate(types):
        adj = set(pattern(T, x_is_line, 0))
        nonadj = [c for c in range(C) if c not in adj]
        dn = min(int(d[copy_vertex(g, c, y)]) for c in nonadj for y in opp)
        da = min(int(d[copy_vertex(g, c, y)]) for c in adj for y in opp)
        res.append((g, T, sorted(adj), dn, da))
    for g, T, adj, dn, da in res:
        print(f'  group {g} type {T}: adjacent copies {adj}; min dist to opposite vertices in NON-adjacent copies = {dn}; '
              f'in adjacent copies = {da}', flush=True)
    print(f'  overall min over non-adjacent copies: {min(r[3] for r in res)}', flush=True)
