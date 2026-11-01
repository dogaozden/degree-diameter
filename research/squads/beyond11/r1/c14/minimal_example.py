# c14: smallest one-sided example (e in S, t = 1 or 2), exhaustive over small non-abelian groups,
# with BFS diameter of the Haar graph H(G,S) as an independent check.
import itertools
from collections import deque
from check_sets import perm_mul, quat_mul, sl23_mul, closure_group
from search_onesided import dihedral, sym

def setup(G, mul):
    n = len(G); idx = {g: i for i, g in enumerate(G)}
    M = [[idx[mul(a, b)] for b in G] for a in G]
    ident = next(i for i in range(n) if all(M[i][j] == j for j in range(n)))
    inv = [next(j for j in range(n) if M[i][j] == ident) for i in range(n)]
    return n, M, ident, inv

def sm(M, X, Y): return {M[x][y] for x in X for y in Y}

def haar_diam(n, M, S):
    N = 2*n; adj = [[] for _ in range(N)]
    for g in range(n):
        for s in S:
            h = M[s][g]; adj[g].append(n+h); adj[n+h].append(g)
    best = 0
    for v in range(N):
        dist = [-1]*N; dist[v] = 0; dq = deque([v])
        while dq:
            x = dq.popleft()
            for y in adj[x]:
                if dist[y] < 0: dist[y] = dist[x]+1; dq.append(y)
        if min(dist) < 0: return None
        best = max(best, max(dist))
    return best

def find(name, G, mul, tmax=2, kmax=6):
    n, M, ident, inv = setup(G, mul)
    for k in range(2, kmax+1):
        for rest in itertools.combinations([i for i in range(n) if i != ident], k-1):
            S = (ident,)+rest
            X = sm(M, {inv[s] for s in S}, set(S)); Y = sm(M, set(S), {inv[s] for s in S})
            Xt = {ident}; Yt = {ident}
            for t in range(1, tmax+1):
                Xt = sm(M, Xt, X); Yt = sm(M, Yt, Y)
                if (len(Xt) == n) != (len(Yt) == n):
                    d = haar_diam(n, M, S)
                    return dict(group=name, order=n, t=t, D=2*t+1, k=k, S=[G[i] for i in S],
                                S_inv_S_covers=len(Xt) == n, S_Sinv_covers=len(Yt) == n,
                                sizes=(len(Xt), len(Yt)), bfs_diameter=d)
    return None

if __name__ == '__main__':
    cands = {
        'S3': (closure_group([(1,0,2),(1,2,0)], perm_mul, (0,1,2)), perm_mul),
        'D4': (dihedral(4), perm_mul),
        'Q8': (closure_group([(1,'i'),(1,'j')], quat_mul, (1,'1')), quat_mul),
        'D6': (dihedral(6), perm_mul),
        'A4': (closure_group([(1,2,0,3),(1,0,3,2)], perm_mul, (0,1,2,3)), perm_mul),
    }
    for name, (G, mul) in cands.items():
        r = find(name, G, mul)
        print(name, r)
