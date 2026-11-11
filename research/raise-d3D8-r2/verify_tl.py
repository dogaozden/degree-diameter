"""Independent check of a tlift solution: rebuild the lift from the group table and the voltages, then all-pairs BFS.

Usage: python3 verify_tl.py GROUPFILE GROUP_N GROUP_INDEX SOLFILE [EDGEOUT]
  GROUPFILE  : the export file (G header lines, then N rows of N codes; identity code 0)
  SOLFILE    : tlift solution ("k K E", then "x y voltage" per base edge; x white, y black)
Prints: n, edges, degree range, simple, bipartite, connected, diameter, VALID/INVALID (diameter <= 8)
"""
import sys
from collections import deque


def load_group(path, want_n, want_i):
    toks = None
    with open(path) as f:
        lines = f.read().split("\n")
    i = 0
    while i < len(lines):
        parts = lines[i].split()
        if len(parts) == 4 and parts[0] == "G":
            n, idx, N = int(parts[1]), int(parts[2]), int(parts[3])
            # table: N rows of N ints, possibly wrapped; collect N*N tokens after the header
            vals = []
            j = i + 1
            while len(vals) < N * N:
                vals.extend(int(t) for t in lines[j].split())
                j += 1
            if n == want_n and idx == want_i:
                toks = (N, vals[: N * N])
                break
            i = j
        else:
            i += 1
    if toks is None:
        raise SystemExit("group not found")
    N, vals = toks
    M = [[vals[a * N + b] for b in range(N)] for a in range(N)]
    inv = [None] * N
    for a in range(N):
        for b in range(N):
            if M[a][b] == 0:
                inv[a] = b
    return N, M, inv


def main():
    gpath, gn, gi, solpath = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    N, M, inv = load_group(gpath, gn, gi)
    with open(solpath) as f:
        rows = [l.split() for l in f if l.strip() and not l.startswith("#")]
    k, E = int(rows[0][1]), int(rows[0][3])
    edges = [(int(r[0]), int(r[1]), int(r[2])) for r in rows[1:]]
    assert len(edges) == E
    n = k * N
    adj = [[] for _ in range(n)]
    for x, y, a in edges:
        for g in range(N):
            u = x * N + g
            v = y * N + M[a][g]
            adj[u].append(v)
            adj[v].append(u)
    degs = [len(a) for a in adj]
    simple = all(len(set(a)) == len(a) for a in adj)
    # bipartite: colour by base colour (white vertices are the x's); check every lift edge joins white to black
    whites = set(x for x, _, _ in edges)
    blacks = set(y for _, y, _ in edges)
    bip = whites.isdisjoint(blacks)
    diam = 0
    conn = True
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
        if min(dist) < 0:
            conn = False
            break
        diam = max(diam, max(dist))
    cubic = min(degs) == max(degs) == 3
    valid = cubic and simple and bip and conn and diam <= 8
    print(f"n {n} edges {n*3//2} degrees {min(degs)}..{max(degs)} simple {simple} bipartite {bip} connected {conn} diameter {diam}")
    print("VALID" if valid else "INVALID")
    if len(sys.argv) > 5:
        with open(sys.argv[5], "w") as o:
            o.write(f"{n} {sum(degs)//2}\n")
            seen = set()
            for u in range(n):
                for v in adj[u]:
                    if (min(u, v), max(u, v)) not in seen:
                        seen.add((min(u, v), max(u, v)))
                        o.write(f"{u} {v}\n")


if __name__ == "__main__":
    main()
