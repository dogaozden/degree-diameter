"""Build SA start matrices for the (16,3) search.

A bipartite graph has diameter <= 3 exactly when any two vertices on the same side share a neighbour.
So we search an R x C 0/1 matrix M (rows = one side, cols = other side) with row and column sums <= 16,
MM^T and M^TM off-diagonal >= 1.

Usage:
  python3 d16_prep.py json GRAPH.json R C OUT.txt     # start from a graph, padded to R x C
  python3 d16_prep.py pg Q R C OUT.txt                # start from PG(2,Q) incidence, padded to R x C
Writes text: "R C" then one "r c" line per 1-entry.
"""
import json, sys
from collections import deque
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))


def side_split(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v); adj[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] >= 0: continue
        col[s] = 0; dq = deque([s])
        while dq:
            x = dq.popleft()
            for y in adj[x]:
                if col[y] < 0: col[y] = 1 - col[x]; dq.append(y)
                else: assert col[y] != col[x], 'not bipartite'
    return col


def from_json(path):
    d = json.load(open(path))
    n, edges = d['output'][0], d['output'][1]
    col = side_split(n, edges)
    rows = [v for v in range(n) if col[v] == 0]
    cols = [v for v in range(n) if col[v] == 1]
    ri = {v: i for i, v in enumerate(rows)}; ci = {v: i for i, v in enumerate(cols)}
    ones = []
    for u, v in edges:
        if col[u] == 1: u, v = v, u
        ones.append((ri[u], ci[v]))
    return len(rows), len(cols), ones


def from_pg(q):
    from singer import singer_plane
    points, lines = singer_plane(q)
    pi = {p: i for i, p in enumerate(points)}
    ones = [(j, pi[p]) for j, L in enumerate(lines) for p in L]
    return len(lines), len(points), ones


def main():
    mode = sys.argv[1]
    if mode == 'json':
        R0, C0, ones = from_json(sys.argv[2]); R, C = int(sys.argv[3]), int(sys.argv[4]); out = sys.argv[5]
    else:
        R0, C0, ones = from_pg(int(sys.argv[2])); R, C = int(sys.argv[3]), int(sys.argv[4]); out = sys.argv[5]
    assert R >= R0 and C >= C0, (R0, C0)
    with open(out, 'w') as f:
        f.write(f'{R} {C}\n')
        for r, c in ones: f.write(f'{r} {c}\n')
    deg_r = [0] * R; deg_c = [0] * C
    for r, c in ones: deg_r[r] += 1; deg_c[c] += 1
    print(f'wrote {out}: start {R0}x{C0} padded to {R}x{C}, ones={len(ones)}, max row deg={max(deg_r)}, max col deg={max(deg_c)}')


if __name__ == '__main__':
    main()
