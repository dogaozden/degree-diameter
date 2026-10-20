"""The lift (hat) construction on a bipartite graph, and helpers for GQ incidence graphs.

lift(adj_edges, n, C): copy every vertex of C. A copy v' is joined to u' for each neighbour u of v in C, and to u for
each neighbour u of v outside C. Originals keep all their edges. So an outside vertex w gains |N(w) & C|, and every
vertex of C and every copy keeps its old degree.

A hat in the sense of Araujo-Pardo--Lopez is the copy X' of a point X on a line l that is itself copied: X' is joined
to l' (the new line M) instead of l.

Run with PYTHONDONTWRITEBYTECODE=1.
"""
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / 'problems' / 'bipartite_dd'))
sys.path.insert(0, str(ROOT / 'research' / 'gq4'))
import lib  # noqa: E402


def gq_edges(npts, lines):
    """Incidence graph: points 0..npts-1, line j is vertex npts+j."""
    return [(p, npts + j) for j, L in enumerate(lines) for p in L]


def lift(n, edges, C):
    C = sorted(set(C))
    cid = {v: n + i for i, v in enumerate(C)}
    out = list(edges)
    for u, v in edges:
        if u in cid and v in cid:
            out.append((cid[u], cid[v]))
        elif u in cid:
            out.append((cid[u], v))
        elif v in cid:
            out.append((u, cid[v]))
    return n + len(C), out


def star_forest(n, edges, C):
    """True iff the subgraph induced by C has no path with 3 edges (every component is a star)."""
    C = set(C)
    adj = {v: [] for v in C}
    for u, v in edges:
        if u in C and v in C:
            adj[u].append(v)
            adj[v].append(u)
    return all(not (len(adj[u]) > 1 and len(adj[v]) > 1) for u in C for v in adj[u])


def max_degree(n, edges):
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return max(deg), deg


def diameter(n, edges):
    from collections import deque
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    best = 0
    for s in range(n):
        dist = [-1] * n
        dist[s] = 0
        dq = deque([s])
        while dq:
            x = dq.popleft()
            for y in adj[x]:
                if dist[y] < 0:
                    dist[y] = dist[x] + 1
                    dq.append(y)
        if min(dist) < 0:
            return float('inf')
        best = max(best, max(dist))
    return best
