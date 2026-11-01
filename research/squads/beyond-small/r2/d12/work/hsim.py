# Fraction of same-side hub pairs at distance <= 4 in a random bipartite 5-regular hub graph H (m per side).
import random, sys
def run(m, d=5, trials=3, seed=1):
    rnd = random.Random(seed); fr = []
    for _ in range(trials):
        # configuration model with retries for simple graphs
        while True:
            A = [v for v in range(m) for _ in range(d)]
            B = [v for v in range(m) for _ in range(d)]
            rnd.shuffle(B)
            edges = set(zip(A, B))
            if len(edges) == m * d: break
        adj = [[] for _ in range(2 * m)]
        for a, b in edges:
            adj[a].append(m + b); adj[m + b].append(a)
        tot = ok = 0
        for s in range(m):
            dist = {s: 0}; frontier = [s]
            for step in range(4):
                nxt = []
                for u in frontier:
                    for w in adj[u]:
                        if w not in dist: dist[w] = step + 1; nxt.append(w)
                frontier = nxt
            tot += m - 1
            ok += sum(1 for t in range(m) if t != s and t in dist)
        fr.append(ok / tot)
    return sum(fr) / len(fr)
for m in [100, 150, 200, 250, 300]:
    print("m per side", m, "same-side pairs within H-distance 4: %.3f" % run(m))
