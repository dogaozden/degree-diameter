"""bcheck.py: independent check of a bi-Cayley (K orbits per side) lift found by bc2.

Builds the explicit bipartite graph from the group table and the solution file, then checks, with no symmetry
argument: simple, regular of degree Delta, bipartite by construction, connected, and diameter <= D by an
all-pairs BFS over every vertex.
usage: python3 -I bcheck.py GROUPFILE SOLFILE
"""
import sys
from collections import deque


def load_group(path):
    with open(path) as f:
        m = int(f.readline())
        rows = [list(map(int, f.readline().split())) for _ in range(m)]
    return m, rows


def load_solution(path):
    with open(path) as f:
        K, n, D, Delta = map(int, f.readline().split())
        sets = {}
        for i in range(K):
            for j in range(K):
                parts = list(map(int, f.readline().split()))
                d, elems = parts[0], parts[1:]
                assert len(elems) == d, "bad set size"
                assert len(set(elems)) == d, "repeated voltage (multi-edge)"
                sets[(i, j)] = elems
    return K, n, D, Delta, sets


def main(groupfile, solfile):
    n_g, T = load_group(groupfile)
    K, n, D, Delta, sets = load_solution(solfile)
    assert n_g == n, "group order mismatch"
    V = 2 * K * n
    adj = [[] for _ in range(V)]
    def vid(side, i, g):
        return (side * K + i) * n + g
    for (i, j), S in sets.items():
        for t in S:
            for g in range(n):
                a = vid(0, i, g)
                b = vid(1, j, T[g][t])
                adj[a].append(b)
                adj[b].append(a)
    deg_bad = [v for v in range(V) if len(adj[v]) != Delta]
    assert not deg_bad, f"degree != {Delta} at {len(deg_bad)} vertices"
    for v in range(V):
        assert len(set(adj[v])) == len(adj[v]), "multi-edge"
    # all-pairs BFS
    diam = 0
    for s in range(V):
        dist = [-1] * V
        dist[s] = 0
        q = deque([s])
        seen = 1
        while q:
            x = q.popleft()
            dx = dist[x]
            for y in adj[x]:
                if dist[y] < 0:
                    dist[y] = dx + 1
                    seen += 1
                    q.append(y)
        if seen != V:
            print(f"DISCONNECTED from {s}: {V - seen} unreached")
            return 1
        diam = max(diam, max(dist))
    status = "VALID" if diam <= D else "FAILS"
    print(f"{status}: K={K} n={n} vertices={V} Delta={Delta} diameter={diam} (target D={D})")
    return 0 if diam <= D else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1], sys.argv[2]))
