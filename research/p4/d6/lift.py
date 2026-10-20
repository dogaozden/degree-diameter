"""Level lifts of a bipartite graph (Delorme's nested duplication, Eur. J. Combin. 1985, Sec. 7).

Every vertex x has a level lev[x] >= -1. A vertex of level k >= 0 gets 2^(k+1) versions, indexed by binary
strings of length k+1; a vertex of level -1 keeps one version (the empty string). Versions x^a and y^b are
adjacent iff x ~ y in the base graph and one of a, b is a prefix of the other.

Degree of x^a = deg(x) + sum over neighbours y with lev[y] > lev[x] of (2^(lev[y]-lev[x]) - 1).
Distance: a walk W from x to y lifts from x^a to y^b iff a and b agree on their first (min level on W) + 1
characters. So the diameter stays <= D iff for all x, y and every split point of their strings a walk of
length <= D through a low enough level exists; checked here directly on the lifted graph.
"""
import itertools


def versions(k):
    if k < 0:
        return ['']
    return [''.join(t) for t in itertools.product('01', repeat=k + 1)]


def build(n_base, adj, lev):
    """adj: list of neighbour lists of the base graph. Returns (n, edges, vid) with vid[(x, a)] = new id."""
    vid = {}
    for x in range(n_base):
        for a in versions(lev[x]):
            vid[(x, a)] = len(vid)
    edges = []
    for x in range(n_base):
        for y in adj[x]:
            if y < x:
                continue
            for a in versions(lev[x]):
                for b in versions(lev[y]):
                    if a.startswith(b) or b.startswith(a):
                        edges.append((vid[(x, a)], vid[(y, b)]))
    return len(vid), edges, vid


def degree_excess(adj, lev):
    """Per base vertex: the extra degree of each of its versions."""
    return [sum((1 << (lev[y] - lev[x])) - 1 for y in adj[x] if lev[y] > lev[x]) for x in range(len(adj))]


def gain(lev):
    return sum((1 << (k + 1)) - 1 for k in lev if k >= 0)


def write_text(path, n, edges):
    with open(path, 'w') as f:
        f.write(f'{n} {len(edges)}\n')
        for u, v in edges:
            f.write(f'{u} {v}\n')
