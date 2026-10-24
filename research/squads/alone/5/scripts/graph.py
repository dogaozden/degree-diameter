# shared helpers: load edge list into adjacency lists; A = 0..nA-1, B = nA..2nA-1 for the flag graph
import sys
def load(path):
    with open(path) as f:
        n = int(f.readline())
        adj = [[] for _ in range(n)]
        E = []
        for line in f:
            u, v = map(int, line.split())
            adj[u].append(v); adj[v].append(u); E.append((u, v))
    return n, adj, E
def ball_side(adj, src, radius):
    """vertices at distance <= radius from src, as a set"""
    seen = {src}; fr = [src]
    for _ in range(radius):
        nf = []
        for x in fr:
            for y in adj[x]:
                if y not in seen:
                    seen.add(y); nf.append(y)
        fr = nf
    return seen
