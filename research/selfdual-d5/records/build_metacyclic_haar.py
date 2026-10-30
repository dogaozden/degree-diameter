#!/usr/bin/env python3
"""Build the Haar graph H(G, S) of a metacyclic group G = C_m : C_k = <x, y | x^m = y^k = 1, y x y^-1 = x^r>
from its formula alone (no GAP, no tables), write the edge list and check the diameter by BFS from every vertex.

Elements are pairs (i, j) = x^i y^j, i mod m, j mod k, with product (i, j)(a, b) = (i + r^j a, j + b).
Haar graph: vertices (g, A) and (g, B); (g, A) ~ (s g, B) for s in S.  Vertex numbering: (i, j) on side A is
i*k + j, on side B it is m*k + i*k + j.

usage: build_metacyclic_haar.py m k r "i,j i,j ..." OUT.edges [D]
"""
import sys
from collections import deque


def main():
    m, k, r = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    S = [tuple(int(t) for t in p.split(",")) for p in sys.argv[4].split()]
    out = sys.argv[5]
    D = int(sys.argv[6]) if len(sys.argv) > 6 else 5
    assert pow(r, k, m) == 1, "y^k must act trivially: r^k = 1 mod m"
    rp = [pow(r, j, m) for j in range(k)]

    def mul(g, h):
        return ((g[0] + rp[g[1]] * h[0]) % m, (g[1] + h[1]) % k)

    n = m * k
    idx = lambda g: g[0] * k + g[1]
    elems = [(i, j) for i in range(m) for j in range(k)]
    adj = [[] for _ in range(2 * n)]
    edges = []
    for g in elems:
        for s in S:
            a, b = idx(g), n + idx(mul(s, g))
            edges.append((a, b))
            adj[a].append(b)
            adj[b].append(a)
    with open(out, "w") as f:
        f.write(f"{2 * n}\n")
        for a, b in edges:
            f.write(f"{a} {b}\n")
    # checks: simple, regular, bipartite by construction, diameter by BFS from every vertex
    for v in range(2 * n):
        assert len(set(adj[v])) == len(adj[v]), f"repeated edge at {v}"
    degs = {len(a) for a in adj}
    diam = 0
    for s0 in range(2 * n):
        dist = [-1] * (2 * n)
        dist[s0] = 0
        q = deque([s0])
        while q:
            u = q.popleft()
            for w in adj[u]:
                if dist[w] < 0:
                    dist[w] = dist[u] + 1
                    q.append(w)
        if min(dist) < 0:
            print("DISCONNECTED")
            return 1
        diam = max(diam, max(dist))
    ok = degs == {len(S)} and diam == D
    print(f"vertices {2 * n} edges {len(edges)} degrees {sorted(degs)} diameter {diam} -> "
          f"{'VALID' if ok else 'INVALID'} (Delta={len(S)}, D={D})")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
