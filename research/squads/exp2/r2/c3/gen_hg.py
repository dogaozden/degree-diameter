#!/usr/bin/env python3
"""Random bipartite hub graph for card c3 (round 2, exp2 squad).

K line-side hubs (index j) and K point-side hubs (index k); edge "j k" joins line-side hub j to point-side hub k.
Every hub has degree <= D = 4 (q - 1 for q = 5). Accepted only if, by BFS in the hub graph:
  every two same-side hubs are within distance 6, every line-side/point-side pair within distance 5,
  and the hub graph is connected.
Usage: gen_hg.py SEED OUTFILE
"""
import random
import sys
from collections import deque

K = 28
D = 4


def random_union_of_matchings(rng):
    edges = set()
    for _ in range(D):
        for _attempt in range(10000):
            perm = list(range(K))
            rng.shuffle(perm)
            new = [(j, perm[j]) for j in range(K)]
            if all(e not in edges for e in new):
                edges.update(new)
                break
        else:
            return None
    return sorted(edges)


def check(edges):
    n = 2 * K  # line-side hub j -> j, point-side hub k -> K + k
    adj = [[] for _ in range(n)]
    for j, k in edges:
        adj[j].append(K + k)
        adj[K + k].append(j)
    maxdeg = max(len(a) for a in adj)
    if maxdeg > D:
        return None
    worst_same = 0
    worst_cross = 0
    for s in range(n):
        dist = [-1] * n
        dist[s] = 0
        dq = deque([s])
        while dq:
            v = dq.popleft()
            for w in adj[v]:
                if dist[w] < 0:
                    dist[w] = dist[v] + 1
                    dq.append(w)
        for t in range(n):
            if t == s:
                continue
            if dist[t] < 0:
                return None
            if (s < K) == (t < K):
                worst_same = max(worst_same, dist[t])
            else:
                worst_cross = max(worst_cross, dist[t])
    if worst_same > 6 or worst_cross > 5:
        return None
    return maxdeg, worst_same, worst_cross


def main():
    seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    out = sys.argv[2] if len(sys.argv) > 2 else "k28.hg"
    rng = random.Random(seed)
    tries = 0
    while True:
        tries += 1
        edges = random_union_of_matchings(rng)
        if edges is None:
            continue
        stats = check(edges)
        if stats is None:
            continue
        with open(out, "w") as f:
            f.write(f"{K} {len(edges)}\n")
            for j, k in edges:
                f.write(f"{j} {k}\n")
        maxdeg, worst_same, worst_cross = stats
        print(f"wrote {out}: K={K} m={len(edges)} maxdeg={maxdeg} "
              f"max same-side dist={worst_same} max cross dist={worst_cross} (after {tries} draws)")
        return


if __name__ == "__main__":
    main()
