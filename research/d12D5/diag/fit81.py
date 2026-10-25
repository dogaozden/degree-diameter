#!/usr/bin/env python3
"""Fit a backtrack-complete chart to a FIXED controller (voltages over a cyclic group, base K33m-type).
State: a complete leg-triangle assignment per base vertex (legs.py, 1,920 choices) and a collineation g per edge
(compatible with the triangles at its two ends, csp2.py).  The singular 4-walks follow from the state alone (two legs
from different apexes at the middle vertex meet), so the cost = number of (orbit, target) controller pairs whose
covering 4-walks are all singular is computed without building the chart.  Annealing over vertex moves (a new
assignment compatible with the current neighbours) and edge moves (another valid g).
usage: python3 fit81.py BASE N VOLTS SECONDS SEED OUT.echart"""
import itertools, pickle, random, sys, os, time, math
import numpy as np
here = os.path.dirname(os.path.abspath(__file__))
D = pickle.load(open(os.path.join(here, 'complete.pkl'), 'rb'))
TRI, SOLS = D['TRI'], D['sols']
def norm3(v):
    v = tuple(x % 3 for x in v)
    for x in v:
        if x: return tuple((y * x) % 3 for y in v)
def drop(p, i): return tuple(p[k] for k in range(4) if k != i)
def lift_pt(q, i):  # 3-coord point of quotient at apex i -> 4-vector with 0 at i
    out = list(q); out.insert(i, 0); return tuple(out)
S3 = [(1, 0, 0), (0, 1, 0), (0, 0, 1)]
def apply(M, v): return norm3(tuple(sum(M[r][c] * v[c] for c in range(3)) for r in range(3)))
def maps_S_to(T):
    out = []
    for perm in itertools.permutations(T):
        for al in itertools.product((1, 2), repeat=2):
            a = (1,) + al
            out.append([[(a[c] * perm[c][r]) % 3 for c in range(3)] for r in range(3)])
    return out
def compat_maps(Ty, Tw): return [g for g in maps_S_to(Tw) if {apply(g, q) for q in Ty} == set(S3)]
def rank(vs):
    rows = [list(v) for v in vs]; r = 0
    for c in range(4):
        piv = next((k for k in range(r, len(rows)) if rows[k][c] % 3), None)
        if piv is None: continue
        rows[r], rows[piv] = rows[piv], rows[r]; inv = rows[r][c] % 3
        rows[r] = [(x * inv) % 3 for x in rows[r]]
        for k in range(len(rows)):
            if k != r and rows[k][c] % 3:
                f = rows[k][c]; rows[k] = [(x - f * y) % 3 for x, y in zip(rows[k], rows[r])]
        r += 1
    return r
T3 = sorted({frozenset(drop(p, i) for p in T) for i in range(4) for T in TRI[i]}, key=sorted)
TID = {t: n for n, t in enumerate(T3)}
tri_of = np.array([[TID[frozenset(drop(p, i) for p in TRI[i][s[i]])] for i in range(4)] for s in SOLS])
MAPS = {}
C = np.zeros((len(T3), len(T3)), dtype=bool)
for a, ta in enumerate(T3):
    for b, tb in enumerate(T3):
        ms = compat_maps(tuple(sorted(ta)), tuple(sorted(tb)))
        if ms: C[a, b] = True; MAPS[(a, b)] = ms
base = open(sys.argv[1]).read().split(); k = int(base[0])
EA = [int(base[1 + 2 * t]) for t in range(4 * k)]; EB = [int(base[2 + 2 * t]) for t in range(4 * k)]; ne = 4 * k
idxA = {}; idxB = {}; cA = [0] * k; cB = [0] * k
for e in range(ne):
    idxA[e] = cA[EA[e]]; cA[EA[e]] += 1; idxB[e] = cB[EB[e]]; cB[EB[e]] += 1
atA = [[e for e in range(ne) if EA[e] == y] for y in range(k)]; atB = [[e for e in range(ne) if EB[e] == w] for w in range(k)]
n = int(sys.argv[2]); V = list(map(int, sys.argv[3].split(','))); secs = float(sys.argv[4]); rng = random.Random(int(sys.argv[5])); out = sys.argv[6]
np.random.seed(int(sys.argv[5]))
# coverage sets for the fixed controller (cyclic group, additive voltages)
need = []   # list of sets of walk keys (side, e1, e2, e3, e4)
for side in 'AB':
    for i in range(k):
        cov = {}; d2 = set()
        st = atA[i] if side == 'A' else atB[i]
        for e1 in st:
            mid1 = EB[e1] if side == 'A' else EA[e1]
            for e2 in (atB[mid1] if side == 'A' else atA[mid1]):
                if e2 == e1: continue
                y = EA[e2] if side == 'A' else EB[e2]
                d2.add((y, (V[e1] - V[e2]) % n if side == 'A' else (V[e2] - V[e1]) % n))
                for e3 in (atA[y] if side == 'A' else atB[y]):
                    if e3 == e2: continue
                    mid2 = EB[e3] if side == 'A' else EA[e3]
                    for e4 in (atB[mid2] if side == 'A' else atA[mid2]):
                        if e4 == e3: continue
                        end = EA[e4] if side == 'A' else EB[e4]
                        x = (V[e1] - V[e2] + V[e3] - V[e4]) % n if side == 'A' else (-V[e1] + V[e2] - V[e3] + V[e4]) % n
                        cov.setdefault((end, x), set()).add((side, e1, e2, e3, e4))
        for j in range(k):
            for x in range(n):
                if (j, x) == (i, 0) or (j, x) in d2: continue
                need.append(cov.get((j, x), set()))
print('pairs needing a 4-walk', len(need), 'uncoverable', sum(1 for s in need if not s), flush=True)
walk_pairs = {}
for t, s in enumerate(need):
    for w in s: walk_pairs.setdefault(w, []).append(t)
# state
def tri(v_side, v, s, apex): return tri_of[s, apex]
def edge_tris(e, asg):
    return tri_of[asg[('A', EA[e])], idxA[e]], tri_of[asg[('B', EB[e])], idxB[e]]
def label_maps(e, g, asg):
    """A-side: point of T_i(y) (4-vec) -> edge at w; B-side: point of T_j(w) -> edge at y."""
    i, j = idxA[e], idxB[e]; w, y = EB[e], EA[e]
    Ty = [lift_pt(q, i) for q in sorted(T3[edge_tris(e, asg)[0]])]
    edges_w = {idxB[l]: l for l in atB[w]}; edges_y = {idxA[l]: l for l in atA[y]}
    labA = {}
    oj = [x for x in range(4) if x != j]; oi = [x for x in range(4) if x != i]
    for p in Ty:
        q = apply(g, drop(p, i))                     # frame point of w's quotient
        jj = oj[q.index(1)] if q.count(0) == 2 else None
        labA[p] = edges_w[jj]
    labB = {}
    for c in range(3):                               # g maps frame point oi[c] of y to column c
        q = norm3(tuple(g[r][c] for r in range(3)))
        labB[lift_pt(q, j)] = edges_y[oi[c]]
    return labA, labB
LEGINT = {}
def legs_meet(a, p, b, q):
    key = (a, p, b, q)
    if key not in LEGINT:
        E = [tuple(int(r == x) for r in range(4)) for x in range(4)]
        LEGINT[key] = rank([E[a], p, E[b], q]) < 4
    return LEGINT[key]
def singular_set(asg, G):
    labs = {e: label_maps(e, G[e], asg) for e in range(ne)}
    S = set()
    for y in range(k):   # A-side walks with middle y
        legs = [(idxA[e], p, labs[e][0][p], e) for e in atA[y] for p in labs[e][0]]
        for (a, p, l1, e2), (b, q, l4, e3) in itertools.combinations(legs, 2):
            if a != b and legs_meet(a, p, b, q):
                S.add(('A', l1, e2, e3, l4)); S.add(('A', l4, e3, e2, l1))
    for w in range(k):
        legs = [(idxB[e], p, labs[e][1][p], e) for e in atB[w] for p in labs[e][1]]
        for (a, p, l1, e2), (b, q, l4, e3) in itertools.combinations(legs, 2):
            if a != b and legs_meet(a, p, b, q):
                S.add(('B', l1, e2, e3, l4)); S.add(('B', l4, e3, e2, l1))
    return S
def cost_of(S): return sum(1 for s in need if s <= S)
# initial state: a random CSP solution (forward checking as in csp2)
VARS = [('A', y) for y in range(k)] + [('B', w) for w in range(k)]
Me = [C[np.ix_(tri_of[:, idxA[e]], tri_of[:, idxB[e]])] for e in range(ne)]
def solve_random():
    def edges_between(v, u):
        (sv, a), (su, b) = v, u
        if sv == su: return []
        if sv == 'A': return [(e, False) for e in range(ne) if EA[e] == a and EB[e] == b]
        return [(e, True) for e in range(ne) if EB[e] == a and EA[e] == b]
    def rec(assign, doms):
        free = [v for v in VARS if v not in assign]
        if not free: return dict(assign)
        v = min(free, key=lambda x: doms[x].sum()); cand = np.flatnonzero(doms[v]); np.random.shuffle(cand)
        for s in cand[:200]:
            nd = {}; dead = False
            for u in free:
                if u == v: continue
                d = doms[u].copy()
                for e, vB in edges_between(v, u): d &= Me[e][:, s] if vB else Me[e][s, :]
                if not d.any(): dead = True; break
                nd[u] = d
            if dead: continue
            assign[v] = s; r = rec(assign, nd); del assign[v]
            if r: return r
        return None
    return rec({}, {v: np.ones(len(SOLS), dtype=bool) for v in VARS})
asg = solve_random()
G = {e: rng.choice(MAPS[tuple(int(t) for t in edge_tris(e, asg))]) for e in range(ne)}
S = singular_set(asg, G); c = cost_of(S); best = (c, dict(asg), dict(G)); t0 = time.time(); it = 0
print('start cost', c, 'singular', len(S), flush=True)
while time.time() - t0 < secs and best[0] > 0:
    it += 1; T = 1.5 * (1 - (time.time() - t0) / secs) + 0.05
    na, nG = dict(asg), dict(G)
    r = rng.random()
    if r < 0.5:      # edge move
        e = rng.randrange(ne); nG[e] = rng.choice(MAPS[tuple(int(t) for t in edge_tris(e, asg))])
    elif r < 0.9:    # vertex move
        v = rng.choice(VARS); side, x = v
        es = atA[x] if side == 'A' else atB[x]
        ok = np.ones(len(SOLS), dtype=bool)
        for e in es:
            if side == 'A': ok &= C[tri_of[:, idxA[e]], tri_of[na[('B', EB[e])], idxB[e]]]
            else: ok &= C[tri_of[na[('A', EA[e])], idxA[e]], tri_of[:, idxB[e]]]
        cand = np.flatnonzero(ok)
        if len(cand) < 2: continue
        na[v] = int(rng.choice(list(cand)))
        for e in es: nG[e] = rng.choice(MAPS[tuple(int(t) for t in edge_tris(e, na))])
    else:            # restart from a fresh random solution if stuck badly
        if c <= best[0] + 2: continue
        na = solve_random(); nG = {e: rng.choice(MAPS[tuple(int(t) for t in edge_tris(e, na))]) for e in range(ne)}
    S2 = singular_set(na, nG); c2 = cost_of(S2)
    if c2 <= c or math.exp((c - c2) / T) > rng.random():
        asg, G, c = na, nG, c2
        if c < best[0]: best = (c, dict(asg), dict(G)); print(f'it {it} t {time.time() - t0:.0f}s cost {c}', flush=True)
c, asg, G = best
print('best_cost', c, 'iters', it, flush=True)
# write the chart: A_e e_i = e_j, other columns from g plus a random e_j row
lines = []
for e in range(ne):
    i, j = idxA[e], idxB[e]; g = G[e]
    A = [[0] * 4 for _ in range(4)]; A[j][i] = 1
    oi = [x for x in range(4) if x != i]; oj = [x for x in range(4) if x != j]
    for cc, ic in enumerate(oi):
        for rr, jr in enumerate(oj): A[jr][ic] = g[rr][cc]
        A[j][ic] = rng.randrange(3)
    b = [int(x == j) for x in range(4)]
    lines.append(' '.join(str(A[r][cc]) for r in range(4) for cc in range(4)) + ' ' + ' '.join(map(str, b)))
open(out, 'w').write('\n'.join(lines) + '\n'); print('wrote', out)
