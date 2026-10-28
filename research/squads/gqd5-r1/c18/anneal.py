"""Simulated annealing for level graphs with L levels (some pairs unjoined), objective = # ordered pairs at distance > 5.
Usage: python3 anneal.py q e L iters seed"""
import sys, os, random, math, itertools
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
sys.path.insert(0, '/home/user/degree-diameter/research/squads/gqd5-r1/c18')
import gqlib
from unjoined import check

q, e, L, iters, seed = map(int, sys.argv[1:6])
G = gqlib.W(q); rng = random.Random(seed)
S = (q+1)*(q*q+1); per = G.np + G.nl
inc = [(p, G.np + l) for l, pts in enumerate(G.lines) for p in pts]
base_edges = [(j*per + a, j*per + b) for j in range(L) for (a, b) in inc]

def state_to_edges(st):
    types, arcs, perms = st
    edges = list(base_edges)
    for idx, (j, j2) in enumerate(arcs):
        A = list(range(G.np)) if types[j] == 'H' else list(range(G.np, per))
        B = list(range(G.np, per)) if types[j2] == 'H' else list(range(G.np))
        for i in range(S):
            edges.append((j*per + A[i], j2*per + B[perms[idx][i]]))
    return edges

def cost(st):
    n = L*per
    edges = state_to_edges(st)
    nb = [[] for _ in range(n)]
    for a, b in edges:
        nb[a].append(b); nb[b].append(a)
    D = q+1+e
    if max(len(x) for x in nb) > D: return 10**9
    nbr = np.array([x + [i]*(D-len(x)) for i, x in enumerate(nb)], dtype=np.int64)
    R = np.zeros((n, (n+7)//8), dtype=np.uint8)
    idx = np.arange(n)
    R[idx, idx//8] = (1 << (7 - idx % 8)).astype(np.uint8)
    for _ in range(5):
        R = R | np.bitwise_or.reduce(R[nbr], axis=1)
    return int(n*n - np.unpackbits(R, axis=1)[:, :n].sum())

def random_orient():
    pairs = list(itertools.combinations(range(L), 2)); rng.shuffle(pairs)
    out = [0]*L; inn = [0]*L; arcs = []
    for a, b in pairs:
        opts = []
        if out[a] < e and inn[b] < e: opts.append((a, b))
        if out[b] < e and inn[a] < e: opts.append((b, a))
        if opts:
            x, y = rng.choice(opts); arcs.append((x, y)); out[x] += 1; inn[y] += 1
    return arcs

types = [rng.choice('HD') for _ in range(L)]
arcs = random_orient()
perms = [rng.sample(range(S), S) for _ in arcs]
st = (types, arcs, perms)
c = cost(st); best = (c, st); T0 = 3.0
print('init cost', c, 'arcs', len(arcs), flush=True)
for it in range(iters):
    T = T0 * (1 - it/iters) + 0.05
    types, arcs, perms = st
    types2 = list(types); arcs2 = list(arcs); perms2 = [list(p) for p in perms]
    mv = rng.random()
    if mv < 0.6 and arcs2:
        k = rng.randrange(len(arcs2)); i, j = rng.sample(range(S), 2)
        perms2[k][i], perms2[k][j] = perms2[k][j], perms2[k][i]
    elif mv < 0.75:
        j = rng.randrange(L); types2[j] = 'D' if types2[j] == 'H' else 'H'
    else:
        if arcs2 and rng.random() < 0.5:
            k = rng.randrange(len(arcs2)); del arcs2[k]; del perms2[k]
        else:
            out = [0]*L; inn = [0]*L
            for (x, y) in arcs2: out[x] += 1; inn[y] += 1
            joined = {frozenset(a) for a in arcs2}
            cand = []
            for a, b in itertools.combinations(range(L), 2):
                if frozenset((a, b)) in joined: continue
                if out[a] < e and inn[b] < e: cand.append((a, b))
                if out[b] < e and inn[a] < e: cand.append((b, a))
            if cand:
                arcs2.append(rng.choice(cand)); perms2.append(rng.sample(range(S), S))
    st2 = (types2, arcs2, perms2)
    c2 = cost(st2)
    if c2 <= c or rng.random() < math.exp(-(c2 - c)/max(T, 1e-6)):
        st, c = st2, c2
        if c < best[0]: best = (c, st)
    if best[0] == 0: break
print('q=%d e=%d L=%d seed=%d iters=%d best_bad_pairs=%d arcs=%d' % (q, e, L, seed, it+1, best[0], len(best[1][1])), flush=True)
if best[0] == 0:
    st = best[1]
    edges = state_to_edges(st)
    path = '/home/user/degree-diameter/research/squads/gqd5-r1/c18/found_q%d_e%d_L%d_s%d.txt' % (q, e, L, seed)
    ok, out = check(L*per, edges, q+1+e, path)
    print('apsp', ok, out.splitlines()[-1], flush=True)
    print('types', st[0], 'arcs', st[1], flush=True)
