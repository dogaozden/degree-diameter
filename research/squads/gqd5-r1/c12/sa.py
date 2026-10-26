"""c12: k copies of the AS(3) incidence graph (GQ(2,4), 72 vertices each), alternating colour types H/D;
every line has 2 spare stubs (degree 3 -> 5); spare stubs of H-lines are matched to spare stubs of D-lines.
Simulated annealing over the stub matching, cost = #ordered pairs at distance > 5 + 50 * #multi-edges.
Usage: python3 sa.py k iters seed out_prefix"""
import sys, os, math, random
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import gqlib

k, iters, seed, outp = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
random.seed(seed); np.random.seed(seed)
G = gqlib.AS(3)
NP, NL = G.np, G.nl          # 27, 45
SZ = NP + NL                 # 72
base_edges = []              # within-copy incidences, global ids
Hlines, Dlines = [], []      # global ids of spare-bearing lines of H / D copies
for c in range(k):
    o = c * SZ
    typ = 'H' if c % 2 == 0 else 'D'
    for l in range(NL):
        for p in G.lines[l]:
            if typ == 'H':
                base_edges.append((o + p, o + NP + l))
            else:
                base_edges.append((o + NL + 0 * 0 + l, o + NL + 0) if False else None)
    # redo D copy cleanly below
    if typ == 'D':
        base_edges = [e for e in base_edges if e is not None]
        # for D copies: lines are first NL ids, points next NP ids
        for l in range(NL):
            for p in G.lines[l]:
                base_edges.append((o + l, o + NL + p))
        Dlines += [o + l for l in range(NL)]
    else:
        Hlines += [o + NP + l for l in range(NL)]
base_edges = [e for e in base_edges if e is not None]
N = k * SZ
# stubs: each spare-bearing line has 2 stubs
hstub = [v for v in Hlines for _ in range(2)]
dstub = [v for v in Dlines for _ in range(2)]
S = len(hstub)
assert S == len(dstub)

def adjacency(perm):
    A = np.zeros((N, N), dtype=np.float32)
    for u, v in base_edges:
        A[u, v] = A[v, u] = 1
    dup = 0
    for i in range(S):
        u, v = hstub[i], dstub[perm[i]]
        if A[u, v]:
            dup += 1
        A[u, v] = A[v, u] = 1
    return A, dup

def cost(perm):
    A, dup = adjacency(perm)
    R = np.eye(N, dtype=np.float32)
    for _ in range(5):
        R = np.minimum(R + R @ A, 1.0)
    bad = int(N * N - np.count_nonzero(R))
    return bad + 50 * dup, bad, dup

perm = list(range(S)); random.shuffle(perm)
cur, bad, dup = cost(perm)
best = (cur, bad, dup, list(perm))
T0, T1 = 3.0, 0.05
for it in range(iters):
    T = T0 * (T1 / T0) ** (it / max(1, iters - 1))
    i, j = random.randrange(S), random.randrange(S)
    if i == j:
        continue
    perm[i], perm[j] = perm[j], perm[i]
    new, nb, nd = cost(perm)
    if new <= cur or random.random() < math.exp(-(new - cur) / T):
        cur = new
        if cur < best[0]:
            best = (cur, nb, nd, list(perm))
            if cur == 0:
                break
    else:
        perm[i], perm[j] = perm[j], perm[i]
    if it % 200 == 0:
        print('it', it, 'cur', cur, 'best', best[0], 'bad', best[1], 'dup', best[2], flush=True)

cst, nb, nd, bp = best
print('FINAL k', k, 'n', N, 'cost', cst, 'bad_pairs', nb, 'dup', nd, flush=True)
# write edge file
A, dup = adjacency(bp)
edges = set()
for u, v in base_edges:
    edges.add((min(u, v), max(u, v)))
for i in range(S):
    u, v = hstub[i], dstub[bp[i]]
    edges.add((min(u, v), max(u, v)))
with open(outp + '.edges', 'w') as f:
    f.write('%d\n' % N)
    for u, v in sorted(edges):
        f.write('%d %d\n' % (u, v))
print('edges', len(edges), 'written', outp + '.edges')
