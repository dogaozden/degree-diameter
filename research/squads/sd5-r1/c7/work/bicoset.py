#!/usr/bin/env python3
"""Bi-coset graphs B(G;H,K;S) with |H|=|K|=3, degree d, diameter test D.

A-vertices: left cosets xH; B-vertices: left cosets yK; xH ~ yK iff x^-1 y in S,
where S is a union of double cosets HgK with |S| = 3d (so |S|/|K| = d on both sides).
G acts transitively on A and on B, so the diameter = max(ecc(A0), ecc(B0)).
Usage: bicoset.py TABLE D [maxgroupsS] [outdir]
"""
import sys, os, time
from collections import deque

def load(path):
    txt = open(path).read().replace('\\\n', '')
    pos = txt.index('SUBS')
    toks = txt[:pos].split()
    n = int(toks[0]); e = int(toks[1]) - 1
    vals = [int(x) - 1 for x in toks[2:2 + n * n]]
    assert len(vals) == n * n
    table = [vals[i * n:(i + 1) * n] for i in range(n)]
    rest = txt[pos:].split('\n')
    ns = int(rest[0].split()[1])
    subs = []
    for t in range(ns):
        parts = list(map(int, rest[1 + t].split()))
        subs.append([x - 1 for x in parts[1:]])
    return n, e, table, subs

def run(path, D, d, outdir, maxcands=10**9, tag=''):
    n, e, T, subs = load(path)
    inv = [0] * n
    for g in range(n):
        for h in range(n):
            if T[g][h] == e:
                inv[g] = h; break
    if len(subs) == 0:
        print('no order-3 subgroups'); return None
    def cosets(H):
        idx = [-1] * n; reps = []
        for x in range(n):
            if idx[x] < 0:
                c = len(reps); reps.append(x)
                for h in H:
                    idx[T[x][h]] = c
        return idx, reps
    best = None
    found = []
    total_tested = 0
    t0 = time.time()
    for H in subs:
        idxA, repA = cosets(H)
        for K in subs:
            idxB, repB = cosets(K)
            nA, nB = len(repA), len(repB)
            # double cosets H g K
            seen = [False] * n
            dcs = []
            for g in range(n):
                if seen[g]:
                    continue
                dc = set(T[T[h][g]][k] for h in H for k in K)
                for x in dc:
                    seen[x] = True
                dcs.append(frozenset(dc))
            # only double cosets of size dividing 9 with size<=3d are useful
            dcs = [c for c in dcs if len(c) <= 3 * d]
            # precompute neighbour maps
            BA = [[idxB[T[x][s]] for s in range(n)] for x in repA]      # A-vertex i, element s -> B index
            AB = [[idxA[T[y][inv[s]]] for s in range(n)] for y in repB]  # B-vertex j, element s -> A index
            sizes = [len(c) for c in dcs]
            # enumerate subsets of dcs with total size 3d
            cand = []
            m = len(dcs)
            def rec(start, tot, chosen):
                if tot == 3 * d:
                    cand.append(list(chosen)); return
                for t in range(start, m):
                    if tot + sizes[t] <= 3 * d:
                        chosen.append(t); rec(t + 1, tot + sizes[t], chosen); chosen.pop()
            rec(0, 0, [])
            for ch in cand:
                if total_tested >= maxcands:
                    break
                total_tested += 1
                S = [s for t in ch for s in dcs[t]]
                adjA = []
                for i in range(nA):
                    row = BA[i]
                    adjA.append(sorted(set(row[s] for s in S)))
                adjB = []
                for j in range(nB):
                    row = AB[j]
                    adjB.append(sorted(set(row[s] for s in S)))
                if any(len(a) != d for a in adjA) or any(len(b) != d for b in adjB):
                    continue  # should not happen
                V = nA + nB
                adj = [None] * V
                for i in range(nA):
                    adj[i] = [nA + j for j in adjA[i]]
                for j in range(nB):
                    adj[nA + j] = adjB[j]
                cost = 0; ok = True
                for src in (0, nA):
                    dist = [-1] * V; dist[src] = 0; q = deque([src])
                    while q:
                        u = q.popleft()
                        du = dist[u] + 1
                        for w in adj[u]:
                            if dist[w] < 0:
                                dist[w] = du; q.append(w)
                    bad = sum(1 for x in dist if x < 0 or x > D)
                    cost = max(cost, bad)
                if cost == 0:
                    found.append((V, H, K, ch))
                    if outdir:
                        fn = os.path.join(outdir, 'edges_%s_n%d_%d.txt' % (tag, V, len(found)))
                        with open(fn, 'w') as f:
                            f.write('%d\n' % V)
                            for u in range(V):
                                for w in adj[u]:
                                    if u < w:
                                        f.write('%d %d\n' % (u, w))
                        print('VALID', V, fn, flush=True)
                    if best is None or V > best[0]:
                        best = (V, cost)
                else:
                    if best is None or (best[0] == -1 and cost < best[1]) or (best[0] != -1 and False):
                        pass
                    cand_cost = cost
                    if 'mincost' not in globals() or cand_cost < globals()['mincost']:
                        globals()['mincost'] = cand_cost
                        globals()['mincost_info'] = (nA + nB, len(ch), tuple(sorted(sizes[t] for t in ch)))
            if total_tested >= maxcands:
                break
    el = time.time() - t0
    print('groupfile', path, 'tested', total_tested, 'valid', len(found), 'time %.1f' % el,
          'mincost', globals().get('mincost'), 'info', globals().get('mincost_info'), flush=True)
    return found

if __name__ == '__main__':
    path = sys.argv[1]; D = int(sys.argv[2]); d = int(sys.argv[3])
    outdir = sys.argv[4] if len(sys.argv) > 4 else None
    maxc = int(sys.argv[5]) if len(sys.argv) > 5 else 10**9
    tag = os.path.basename(path).replace('.txt', '')
    run(path, D, d, outdir, maxc, tag)
