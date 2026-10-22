"""Build a record JSON for a Haar graph from a haar_search3 solution file (Round 4).

  python3 research/d5/make_haar_r4.py SOLFILE OUT.json

SOLFILE: header "d N 1 1 tables/NAME.txt", then d lines "g 0" (g = table index of s_i).
Vertices: (g, A) = g, (g, B) = N + g; edges (g, A) ~ (s g, B) for s in S.
Writes JSON with the fields of graphs/haar_d9_n2662.json (case, value, output, construction).
Also re-checks 9/10-regularity, bipartiteness and the diameter by BFS before writing.
The group is read from the table file the solution names (groups.py output).
"""
import json
import sys
from collections import deque


def load_table(path):
    with open(path) as f:
        N = int(f.readline())
        T = [list(map(int, f.readline().split())) for _ in range(N)]
    return N, T


def main(sol, out):
    with open(sol) as f:
        d, N, _, _, table = f.readline().split()
        d, N = int(d), int(N)
        S = [int(f.readline().split()[0]) for _ in range(d)]
    _, T = load_table(table if table.startswith("/") else "/home/user/degree-diameter/research/d5/" + table)
    assert len(T) == N
    n = 2 * N
    edges = []
    for g in range(N):
        for s in S:
            edges.append([g, N + T[s][g]])
    # BFS diameter from every vertex (n = 2N up to ~4400; cheap enough for one bipartite check)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    assert all(len(a) == d for a in adj), "not d-regular"
    diam = 0
    for s0 in range(n):
        dist = [-1] * n
        dist[s0] = 0
        q = deque([s0])
        while q:
            x = q.popleft()
            for y in adj[x]:
                if dist[y] < 0:
                    dist[y] = dist[x] + 1
                    q.append(y)
        assert min(dist) >= 0, "disconnected"
        diam = max(diam, max(dist))
    print(f"n={n} d={d} diameter={diam}")
    assert diam <= 5
    rec = {
        "case": f"d{d}D5",
        "value": n,
        "output": [n, edges],
        "construction": {"group_table": table, "S_indices": S,
                         "rule": "Haar graph: (g,A)~(s*g,B) for s in S; table from groups.py"},
    }
    with open(out, "w") as f:
        json.dump(rec, f)
    print("wrote", out)


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
