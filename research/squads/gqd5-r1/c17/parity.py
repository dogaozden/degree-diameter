"""Bipartiteness check of the level graph (hub vertices removed) and of the full hub graph."""
import sys
from collections import deque
def read(p):
    L = open(p).read().split('\n'); n = int(L[0]); E = [tuple(map(int, l.split())) for l in L[1:] if l.strip()]
    return n, E
def colour_conflicts(n, E):
    adj = [[] for _ in range(n)]
    for a, b in E: adj[a].append(b); adj[b].append(a)
    col = [-1] * n; bad = []
    for s in range(n):
        if col[s] >= 0: continue
        col[s] = 0; dq = deque([s])
        while dq:
            u = dq.popleft()
            for v in adj[u]:
                if col[v] < 0: col[v] = 1 - col[u]; dq.append(v)
                elif col[v] == col[u]: bad.append((u, v))
    return bad
if __name__ == '__main__':
    n, E = read(sys.argv[1]); nv = int(sys.argv[2])
    lev = [(a, b) for a, b in E if a < nv and b < nv]
    print('level graph only: conflicts =', len(colour_conflicts(nv, lev)))
    bad = colour_conflicts(n, E)
    print('full graph: conflicts =', len(bad), 'example', bad[:2])
