"""Delorme's nested duplication (Delorme 1985, Europ. J. Combin. 6, Sec. 7) as a level lift (table-audit).

Base graph G (bipartite), levels lev: V -> {-1, 0, 1, 2, ...} with |lev(x) - lev(y)| <= 1 on every edge.
A vertex of level k >= 0 gets b^(k+1) versions (strings of length k+1 over b letters), a level -1 vertex keeps one
(the empty string); (x, a) ~ (y, c) iff x ~ y in G and one of a, c is a prefix of the other.
b = 2 is Delorme's "dedoublement" of A0 = {lev >= 0}, then A1 = {lev >= 1} in A0 and its copy, ...;
b = 3 is his "detriplement" (degree + 2). The order grows by (b-1)(|A0| + b|A1| + b^2|A2| + ...).

Graph I/O: edge list "n" then "u v" lines (the format of research/lifts/coordinator_check/apsp.c)."""
import itertools


def read_edges(path):
    with open(path) as f:
        n = int(f.readline())
        E = [tuple(map(int, line.split())) for line in f if line.strip()]
    return n, E


def write_edges(path, n, E):
    with open(path, 'w') as f:
        f.write(f'{n}\n')
        f.writelines(f'{u} {v}\n' for u, v in E)


def lift(n, E, lev, b):
    for u, v in E:
        assert abs(lev[u] - lev[v]) <= 1, (u, v, lev[u], lev[v])
    words = {}
    base = []          # base[x] = first new index of x's versions
    idx = 0
    for x in range(n):
        k = lev[x]
        ws = [()] if k < 0 else list(itertools.product(range(b), repeat=k + 1))
        words[x] = {w: idx + i for i, w in enumerate(ws)}
        idx += len(ws)
    out = []
    for u, v in E:
        if lev[u] > lev[v]:
            u, v = v, u
        # lev[u] <= lev[v]; a version a of u and c of v are adjacent iff a is a prefix of c
        for c, j in words[v].items():
            a = c[:lev[u] + 1] if lev[u] >= 0 else ()
            out.append((words[u][a], j))
    return idx, out
