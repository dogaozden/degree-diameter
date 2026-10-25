#!/usr/bin/env python3
"""Per-edge charts that are backtrack-complete at EVERY base vertex (frame gauge, legs.py; EDGECHART.md).
Edge e between A-vertex y (apex index i) and B-vertex w (apex index j) needs a collineation g of PG(2,3) with
g(S) = T_j(w) and g(T_i(y)) = S (S = frame triangle; quotient coordinates = the 3 coordinates other than the apex).
Precomputed triangle compatibility + numpy forward checking over the 1,920 complete assignments per vertex.
usage: python3 csp3.py BASE NSOL SEED OUTPREFIX REPS -> OUTPREFIX_<sol>_<rep>.echart (REPS free-row variants per CSP solution)"""
import itertools, pickle, random, sys, os
import numpy as np
here = '/home/user/degree-diameter/research/d12D5/diag'
D = pickle.load(open(os.path.join(here, 'complete.pkl'), 'rb'))
TRI, SOLS = D['TRI'], D['sols']
def norm3(v):
    v = tuple(x % 3 for x in v)
    for x in v:
        if x: return tuple((y * x) % 3 for y in v)
def drop(p, i): return tuple(p[k] for k in range(4) if k != i)
S3 = {(1, 0, 0), (0, 1, 0), (0, 0, 1)}
def apply(M, v): return norm3(tuple(sum(M[r][c] * v[c] for c in range(3)) for r in range(3)))
def maps_S_to(T):
    out = []
    for perm in itertools.permutations(T):
        for al in itertools.product((1, 2), repeat=2):
            a = (1,) + al
            out.append([[(a[c] * perm[c][r]) % 3 for c in range(3)] for r in range(3)])
    return out
def compat_maps(Ty, Tw): return [g for g in maps_S_to(Tw) if {apply(g, q) for q in Ty} == S3]
T3 = sorted({frozenset(drop(p, i) for p in T) for i in range(4) for T in TRI[i]}, key=sorted)
TID = {t: n for n, t in enumerate(T3)}
C = np.zeros((len(T3), len(T3)), dtype=bool)
for a, ta in enumerate(T3):
    for b, tb in enumerate(T3): C[a, b] = bool(compat_maps(tuple(ta), tuple(tb)))
print('triangles', len(T3), 'compatible pairs', int(C.sum()), flush=True)
tri_of = np.array([[TID[frozenset(drop(p, i) for p in TRI[i][s[i]])] for i in range(4)] for s in SOLS])
base = open(sys.argv[1]).read().split(); k = int(base[0])
EA = [int(base[1 + 2 * t]) for t in range(4 * k)]; EB = [int(base[2 + 2 * t]) for t in range(4 * k)]; ne = 4 * k
idxA = {}; idxB = {}; cA = [0] * k; cB = [0] * k
for e in range(ne):
    idxA[e] = cA[EA[e]]; cA[EA[e]] += 1; idxB[e] = cB[EB[e]]; cB[EB[e]] += 1
nsol, seed, out, REPS = int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], int(sys.argv[5])
rng = random.Random(seed); np.random.seed(seed)
N = len(SOLS)
Me = [C[np.ix_(tri_of[:, idxA[e]], tri_of[:, idxB[e]])] for e in range(ne)]   # Me[e][sy, sw]
VARS = [('A', y) for y in range(k)] + [('B', w) for w in range(k)]
def edges_between(v, u):
    (sv, a), (su, b) = v, u
    if sv == su: return []
    if sv == 'A': return [(e, False) for e in range(ne) if EA[e] == a and EB[e] == b]
    return [(e, True) for e in range(ne) if EB[e] == a and EA[e] == b]
found = 0
def emit(assign):
    global found
    for rep in range(REPS): emit1(assign, rep)
    found += 1
def emit1(assign, rep):
    lines = []
    for e in range(ne):
        i, j = idxA[e], idxB[e]
        Ty = tuple(drop(p, i) for p in TRI[i][SOLS[assign[('A', EA[e])]][i]])
        Tw = tuple(drop(p, j) for p in TRI[j][SOLS[assign[('B', EB[e])]][j]])
        g = rng.choice(compat_maps(Ty, Tw))
        A = [[0] * 4 for _ in range(4)]; A[j][i] = 1
        oi = [x for x in range(4) if x != i]; oj = [x for x in range(4) if x != j]
        for c, ic in enumerate(oi):
            for r, jr in enumerate(oj): A[jr][ic] = g[r][c]
            A[j][ic] = rng.randrange(3)
        b = [int(x == j) for x in range(4)]
        lines.append(' '.join(str(A[r][c]) for r in range(4) for c in range(4)) + ' ' + ' '.join(map(str, b)))
    fn = f'{out}_{found}_{rep}.echart'; open(fn, 'w').write('\n'.join(lines) + '\n'); print('wrote', fn, flush=True)
def solve(assign, doms):
    if found >= nsol: return
    free = [v for v in VARS if v not in assign]
    if not free: emit(assign); return
    v = min(free, key=lambda x: doms[x].sum())
    cand = np.flatnonzero(doms[v]); np.random.shuffle(cand)
    for s in cand[:300]:
        nd = {}; dead = False
        for u in free:
            if u == v: continue
            d = doms[u].copy()
            for e, vB in edges_between(v, u):
                d &= Me[e][:, s] if vB else Me[e][s, :]
            if not d.any(): dead = True; break
            nd[u] = d
        if dead: continue
        assign[v] = s; solve(assign, nd); del assign[v]
        if found >= nsol: return
solve({}, {v: np.ones(N, dtype=bool) for v in VARS})
print('solutions', found)
