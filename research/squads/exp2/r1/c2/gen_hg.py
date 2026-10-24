#!/usr/bin/env python3
"""gen_hg.py K seed deg: random sparse bipartite hub graph for d7hex mode 3 (exp2 squad, card c2).

Line-side hubs j = 0..K-1 and point-side hubs k = 0..K-1. The edge set is the union of `deg` random perfect
matchings between the two sides (repeated edges dropped), so every hub has degree <= deg (deg = q-1 = 4 for q = 5).
A candidate is kept only if, in the hub graph alone, every two same-side hubs are within distance 6 and every
line-hub / point-hub pair is within distance 5 (BFS). Up to 200 candidates are tried.
Writes hg{K}.hg in the current directory: "K m", then m lines "j k"; summary on stdout."""
import random
import sys
from collections import deque


def bfs(adj, s):
    dist = [-1] * len(adj)
    dist[s] = 0
    dq = deque([s])
    while dq:
        v = dq.popleft()
        for w in adj[v]:
            if dist[w] < 0:
                dist[w] = dist[v] + 1
                dq.append(w)
    return dist


def main():
    K, seed, deg = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    n = 2 * K
    for attempt in range(1, 201):
        edges = set()
        for _ in range(deg):
            perm = list(range(K))
            rng.shuffle(perm)
            for j in range(K):
                edges.add((j, perm[j]))
        adj = [[] for _ in range(n)]
        for j, k in edges:
            adj[j].append(K + k)
            adj[K + k].append(j)
        ok = True
        worst_same = worst_cross = 0
        for s in range(n):
            d = bfs(adj, s)
            for t in range(n):
                if t == s:
                    continue
                if d[t] < 0:
                    ok = False
                    break
                if (s < K) == (t < K):
                    worst_same = max(worst_same, d[t])
                    if d[t] > 6:
                        ok = False
                        break
                else:
                    worst_cross = max(worst_cross, d[t])
                    if d[t] > 5:
                        ok = False
                        break
            if not ok:
                break
        if not ok:
            continue
        hub_deg = [len(a) for a in adj]
        with open(f"hg{K}.hg", "w") as f:
            f.write(f"{K} {len(edges)}\n")
            for j, k in sorted(edges):
                f.write(f"{j} {k}\n")
        print(f"K={K} seed={seed} deg={deg} attempt={attempt} m={len(edges)} "
              f"max_hub_deg={max(hub_deg)} min_hub_deg={min(hub_deg)} "
              f"max_same_side_dist={worst_same} max_cross_dist={worst_cross} -> hg{K}.hg")
        return
    print(f"K={K} seed={seed}: no hub graph passed in 200 attempts", file=sys.stderr)
    sys.exit(1)


if __name__ == "__main__":
    main()
