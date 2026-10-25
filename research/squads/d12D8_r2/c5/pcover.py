#!/usr/bin/env python3
"""pcover.py (card c5): necessary condition for the hub design with classes mod m.
For a point t and opposite point v (distance 6) the hub of t reaches copy (v,z) within 8 only through the
4 geodesics, so their voltage sums mod m must cover Z_m. Local search over phi in Z_m^E (E = 1456) minimising
the number of opposite (t,v) pairs whose 4 sums miss a class. usage: pcover.py m iters seed"""
import sys, random, time
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/d12D8/tools')
from hexlib import load_hex
m, iters, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
rng = random.Random(seed)
n, lines = load_hex(3)
NB = 2 * n
# base edge e = l*4 + pos joins point lines[l][pos] and line n+l
adj = [[] for _ in range(NB)]
for l in range(n):
    for pos in range(4):
        p = int(lines[l][pos]); e = l * 4 + pos
        adj[p].append((n + l, e, +1))      # traversing point -> line adds phi
        adj[n + l].append((p, e, -1))      # line -> point subtracts phi
paths_e, paths_s, pairs = [], [], []
t0 = time.time()
for t in range(n):
    dist = [-1] * NB; dist[t] = 0; order = [t]; preds = [[] for _ in range(NB)]
    for x in order:
        for (y, e, s) in adj[x]:
            if dist[y] < 0:
                dist[y] = dist[x] + 1; order.append(y)
            if dist[y] == dist[x] + 1:
                preds[y].append((x, e, s))
    # enumerate all geodesics from t to each opposite point v (dist 6)
    for v in range(n):
        if dist[v] != 6: continue
        # all shortest paths t->v via predecessor DAG (expected 4)
        stack = [(v, [], [])]
        found = []
        while stack:
            x, es, ss = stack.pop()
            if x == t:
                found.append((es, ss)); continue
            for (x2, e, s) in preds[x]:
                stack.append((x2, es + [e], ss + [s]))
        assert len(found) == 4, len(found)
        for es, ss in found:
            paths_e.append(es[::-1]); paths_s.append(ss[::-1]); pairs.append(t * n + v)
PE = np.array(paths_e, dtype=np.int64); PS = np.array(paths_s, dtype=np.int64)
pair_ids = np.array(pairs, dtype=np.int64)
order = np.argsort(pair_ids, kind='stable')
PE = PE[order]; PS = PS[order]
P = PE.shape[0] // 4
assert PE.shape[0] == 4 * P
print(f"paths={PE.shape[0]} opposite pairs={P} built in {time.time()-t0:.1f}s", flush=True)
E = 4 * n
phi = np.array([rng.randrange(m) for _ in range(E)], dtype=np.int64)

def fails(phi):
    s = (phi[PE] * PS).sum(axis=1) % m          # (4P,)
    s = s.reshape(P, 4)
    cov = np.zeros((P,), dtype=np.int64)
    for r in range(m):
        cov += (s == r).any(axis=1)
    return np.nonzero(cov < m)[0]

bad = fails(phi); F = len(bad)
print(f"init F={F}", flush=True)
acc = 0
for it in range(1, iters + 1):
    if F == 0: break
    pr = bad[rng.randrange(len(bad))]
    cand = PE[4 * pr + rng.randrange(4)]
    e = int(cand[rng.randrange(6)])
    old = phi[e]; new = (old + rng.randrange(1, m)) % m
    phi[e] = new
    bad2 = fails(phi); F2 = len(bad2)
    if F2 <= F:
        F, bad = F2, bad2; acc += 1
    else:
        phi[e] = old
    if it % 500 == 0:
        print(f"it {it} F={F} acc={acc}", flush=True)
print(f"RESULT m={m} iters={it} F={F} accepted={acc}", flush=True)
if F == 0:
    np.savetxt(f'/home/user/degree-diameter/research/squads/d12D8_r2/c5/phi_m{m}_s{seed}.txt', phi, fmt='%d')
    print("saved phi")
