#!/usr/bin/env python3
"""Diagnose a route-chart lift: controller edge list ("a b" per line, A-vertex a, B-vertex b, 4m lines; coloured by
build_lift_general.colour) + chart file (chart_search.c text format or chart_u*.json).  BFS in the lifted graph from
sources (u, x) for a sample of controller vertices u and fiber points x; every same-side lifted vertex at distance > 4
is reported by the controller distance d_C(u, v) of its controller vertex v and by whether some nonbacktracking walk
u -> v of length 4 has a nonsingular matrix.  Prediction for a pencil-complete chart: no misses with d_C = 2.
usage: python3 lift_check.py ctrl.edges chart nsrc_ctrl nsrc_fiber [seed]"""
import sys, json, itertools, random
import numpy as np
from collections import deque
from chart import mat_vec, MUL, vid, mat_inv
import build_lift_general as blg

def load_chart(fn):
    if fn.endswith('.json'):
        ch = json.load(open(fn)); return ch['A'], [tuple(v) for v in ch['b']]
    rows = [list(map(int, l.split())) for l in open(fn) if l.strip()]
    A = [[r[4 * i:4 * i + 4] for i in range(4)] for r in rows[:4]]
    b = [tuple(r) for r in rows[4:8]]
    return A, b

def rank(vecs):
    rows = [list(v) for v in vecs]; r = 0
    INV = [None, 1, 3, 2]
    for col in range(4):
        piv = next((i for i in range(r, len(rows)) if rows[i][col]), None)
        if piv is None: continue
        rows[r], rows[piv] = rows[piv], rows[r]
        iv = INV[rows[r][col]]; rows[r] = [MUL[iv][x] for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][col]:
                f = rows[i][col]; rows[i] = [x ^ MUL[f][y] for x, y in zip(rows[i], rows[r])]
        r += 1
    return r

def main():
    cfile, chfile, ns_c, ns_f = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    seed = int(sys.argv[5]) if len(sys.argv) > 5 else 1
    rng = random.Random(seed)
    rows = [tuple(map(int, l.split())) for l in open(cfile) if l.strip()]
    edges = [r[:2] for r in rows]
    m = max(a for a, b in edges) + 1
    col = [tuple(r[:3]) for r in rows] if all(len(r) >= 3 for r in rows) else blg.colour(m, edges)
    A, bv = load_chart(chfile)
    Ai = [mat_inv(M) for M in A]
    # controller adjacency with colours: node a (A side) = a, node b (B side) = m + b
    cadj = [[] for _ in range(2 * m)]
    for a, b, c in col:
        cadj[a].append((m + b, c)); cadj[m + b].append((a, c))
    # controller distances
    def cdist(s):
        d = [-1] * (2 * m); d[s] = 0; dq = deque([s])
        while dq:
            x = dq.popleft()
            for y, c in cadj[x]:
                if d[y] < 0: d[y] = d[x] + 1; dq.append(y)
        return d
    # lifted graph CSR
    vecs = list(itertools.product(range(4), repeat=4)); nA = m * 256; N = 2 * nA
    nbr = [[] for _ in range(N)]
    for a, b, c in col:
        for x in vecs:
            y0 = mat_vec(A[c], x)
            for lam in range(4):
                y = tuple(p ^ MUL[lam][q] for p, q in zip(y0, bv[c]))
                u, w = a * 256 + vid(x), nA + b * 256 + vid(y)
                nbr[u].append(w); nbr[w].append(u)
    nbr = np.array(nbr, dtype=np.int64)
    assert nbr.shape[1] == 16
    # nonsingular NB-4 walk existence per controller pair (A side sources only)
    def nb4_ok(u, v):
        for (b1, c1) in cadj[u]:
            for (w, c2) in cadj[b1]:
                if c2 == c1: continue
                for (b2, c3) in cadj[w]:
                    if c3 == c2: continue
                    for (t, c4) in cadj[b2]:
                        if c4 == c3 or t != v: continue
                        vv = [mat_vec(Ai[c2], bv[c1]), mat_vec(Ai[c2], bv[c2]), mat_vec(Ai[c3], bv[c3]), mat_vec(Ai[c3], bv[c4])]
                        if rank(vv) == 4: return True
        return False
    miss = {}
    srcs_c = rng.sample(range(m), min(ns_c, m))
    maxd = 0
    for u in srcs_c:
        dC = cdist(u)
        for xi in rng.sample(range(256), min(ns_f, 256)):
            s = u * 256 + xi
            d = np.full(N, -1, dtype=np.int64); d[s] = 0; frontier = np.array([s])
            lvl = 0
            while frontier.size:
                lvl += 1
                nb = np.unique(nbr[frontier].ravel()); nb = nb[d[nb] < 0]
                d[nb] = lvl; frontier = nb
            maxd = max(maxd, int(d.max()))
            far = np.nonzero(d[:nA] > 4)[0]
            for t in far:
                v = int(t) // 256
                key = (dC[v], nb4_ok(u, v) if dC[v] in (0, 2, 4) else None)
                miss[key] = miss.get(key, 0) + 1
    print(f'controller m={m}, lift {N} vertices; sources {len(srcs_c)} x {ns_f}; max distance seen {maxd}')
    print('same-side lifted targets at distance > 4, by (controller distance, has nonsingular NB-4 walk):', miss if miss else 'none')

if __name__ == '__main__':
    main()
