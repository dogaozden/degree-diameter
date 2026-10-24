"""Random d-regular bipartite base graphs (union of d random perfect matchings, simple), written in polygons.py's
format (P, then for each B-vertex the list of its A-neighbours), with their diameter.  Used to test the
cover theorems of REGULARITIES.md §1.3 on bases that are not generalized polygons.
usage: python3 randbase.py P d seed OUT"""
import sys, random
from collections import deque
P, d, seed, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
rng = random.Random(seed)
while True:
    nb = [set() for _ in range(P)]   # B-vertex -> A-neighbours
    ok = True
    for _ in range(d):
        perm = list(range(P)); rng.shuffle(perm)
        for b, a in enumerate(perm):
            if a in nb[b]: ok = False
            nb[b].add(a)
    if ok: break
adj = [[] for _ in range(2 * P)]
for b in range(P):
    for a in nb[b]: adj[a].append(P + b); adj[P + b].append(a)
ecc = 0
for s in range(2 * P):
    dist = [-1] * (2 * P); dist[s] = 0; dq = deque([s])
    while dq:
        u = dq.popleft()
        for w in adj[u]:
            if dist[w] < 0: dist[w] = dist[u] + 1; dq.append(w)
    ecc = max(ecc, max(dist))
with open(out, 'w') as f:
    f.write(f"{P}\n")
    for b in range(P): f.write(' '.join(map(str, sorted(nb[b]))) + '\n')
print(f"random {d}-regular bipartite base, 2x{P} vertices, diameter {ecc}")
