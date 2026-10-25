#!/usr/bin/env python3
"""pcolour.py (card c5): exhaustive test of colour-structured voltages for the point-hub condition (P).
phi(e) = a[colour(e)] in Z_m for the 4 perfect-matching colours of H(3). For each m in {2,3,4} all a in Z_m^4
are tried; a choice passes (P) if every opposite point pair has its 4 geodesic sums covering Z_m."""
import sys, itertools, time
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/d12D8/tools')
from hexlib import load_hex
n, lines = load_hex(3)
col = np.load('/home/user/degree-diameter/research/d12D8/hex/col_q3_s1.npy')   # col[l,k] colour of edge (lines[l][k], l)
colour = col.reshape(-1).astype(np.int64)                                        # edge e = l*4+k
NB = 2 * n
adj = [[] for _ in range(NB)]
for l in range(n):
    for pos in range(4):
        p = int(lines[l][pos]); e = l * 4 + pos
        adj[p].append((n + l, e, +1)); adj[n + l].append((p, e, -1))
PE, PS, PID = [], [], []
t0 = time.time()
for t in range(n):
    dist = [-1] * NB; dist[t] = 0; order = [t]; preds = [[] for _ in range(NB)]
    for x in order:
        for (y, e, s) in adj[x]:
            if dist[y] < 0: dist[y] = dist[x] + 1; order.append(y)
            if dist[y] == dist[x] + 1: preds[y].append((x, e, s))
    for v in range(n):
        if dist[v] != 6: continue
        stack = [(v, [], [])]; found = []
        while stack:
            x, es, ss = stack.pop()
            if x == t: found.append((es, ss)); continue
            for (x2, e, s) in preds[x]: stack.append((x2, es + [e], ss + [s]))
        assert len(found) == 4
        for es, ss in found:
            PE.append(es[::-1]); PS.append(ss[::-1]); PID.append(t * n + v)
PE = np.array(PE, dtype=np.int64); PS = np.array(PS, dtype=np.int64); PID = np.array(PID)
o = np.argsort(PID, kind='stable'); PE = PE[o]; PS = PS[o]
P = PE.shape[0] // 4
print(f"paths={PE.shape[0]} pairs={P} ({time.time()-t0:.1f}s)", flush=True)
np.savez_compressed('/home/user/degree-diameter/research/squads/d12D8_r2/c5/geod_q3.npz', PE=PE.astype(np.int16), PS=PS.astype(np.int8))
CE = colour[PE]                                                                  # colour of each path edge
for m in (2, 3, 4):
    best = None
    for a in itertools.product(range(m), repeat=4):
        phi = np.array(a, dtype=np.int64)[colour]                                 # phi per base edge
        s = ((phi[PE] * PS).sum(axis=1) % m).reshape(P, 4)
        cov = np.zeros(P, dtype=np.int64)
        for r in range(m): cov += (s == r).any(axis=1)
        F = int((cov < m).sum())
        if best is None or F < best[0]: best = (F, a)
        if F == 0: print(f"m={m} a={a} PASSES (P)", flush=True)
    print(f"m={m}: best colour pattern a={best[1]} failing pairs={best[0]} of {P}", flush=True)
