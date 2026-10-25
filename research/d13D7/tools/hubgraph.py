#!/usr/bin/env python3
"""Random d-regular bipartite hub graph between hubs v_0..v_{m-1} and u_0..u_{m-1} (union of d random perfect
matchings, no repeated edges) such that every two v's and every two u's are within distance 6 inside it.
usage: hubgraph.py m d seed out.txt   (out: lines "j k" meaning v_j ~ u_k)"""
import sys, random
from collections import deque
m, d, seed, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
rng = random.Random(seed)
for attempt in range(50):
    adjv = [set() for _ in range(m)]
    ok = True
    for t in range(d):
        for _ in range(200):
            perm = list(range(m)); rng.shuffle(perm)
            if all(perm[j] not in adjv[j] for j in range(m)): break
        else:
            ok = False; break
        for j in range(m): adjv[j].add(perm[j])
    if not ok: continue
    adju = [set() for _ in range(m)]
    for j in range(m):
        for k in adjv[j]: adju[k].add(j)
    def ecc_ok(start_side):
        A, Bn = (adjv, adju) if start_side == 'v' else (adju, adjv)
        for s in range(m):
            dist_same = {s: 0}; frontier = [s]; dist = 0; seen_other = set()
            while frontier and dist < 6:
                nxt = set()
                for x in frontier:
                    for y in A[x]:
                        if y not in seen_other: seen_other.add(y); nxt.add(y)
                dist += 1
                f2 = []
                for y in nxt:
                    for z in Bn[y]:
                        if z not in dist_same: dist_same[z] = dist + 1; f2.append(z)
                dist += 1; frontier = f2
            if len(dist_same) < m: return False
        return True
    if ecc_ok('v') and ecc_ok('u'):
        with open(out, 'w') as f:
            for j in range(m):
                for k in sorted(adjv[j]): f.write(f'{j} {k}\n')
        print(f'attempt {attempt}: hub graph OK (m={m}, d={d}), all same-side distances <= 6'); break
else:
    sys.exit('failed')
