#!/usr/bin/env python3
"""Random connected DELTA-regular bipartite multigraph with k vertices per side (configuration model), as a vl base.
usage: rand_base.py k DELTA SEED OUT [MAXMULT]   (MAXMULT: largest allowed edge multiplicity, default DELTA)"""
import random, sys
k, d, seed, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
mm = int(sys.argv[5]) if len(sys.argv) > 5 else d
rng = random.Random(seed)
while True:
    stubs = [j for j in range(k) for _ in range(d)]
    rng.shuffle(stubs)
    E = [(i, k + stubs[i * d + t]) for i in range(k) for t in range(d)]
    mult = {}
    for e in E: mult[e] = mult.get(e, 0) + 1
    if max(mult.values()) > mm: continue
    adj = {v: set() for v in range(2 * k)}
    for a, c in E: adj[a].add(c); adj[c].add(a)
    seen = {0}; st = [0]
    while st:
        x = st.pop()
        for y in adj[x]:
            if y not in seen: seen.add(y); st.append(y)
    if len(seen) == 2 * k: break
with open(out, 'w') as f:
    f.write(f"{2 * k} {len(E)}\n" + " ".join(['0'] * k + ['1'] * k) + "\n")
    for a, c in E: f.write(f"{a} {c}\n")
