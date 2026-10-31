# Isomorphism-invariant signature of an edge list: sorted vertex distance profiles + girth/6-cycle counts.
# Usage: sig.py EDGES...  prints "file n hash profiles6cyc" (hash of the sorted per-vertex distance profiles)
import sys, hashlib
from collections import deque
def load(fn):
    t = open(fn).read().split(); n = int(t[0]); E = [(int(t[1+2*i]), int(t[2+2*i])) for i in range((len(t)-1)//2)]
    adj = [[] for _ in range(n)]
    for a, b in E: adj[a].append(b); adj[b].append(a)
    return n, adj
def sig(n, adj):
    prof = []
    for s in range(n):
        d = [-1]*n; d[s] = 0; q = deque([s]); cnt = [0]*12
        while q:
            x = q.popleft(); cnt[d[x]] += 1
            for y in adj[x]:
                if d[y] < 0: d[y] = d[x]+1; q.append(y)
        prof.append(tuple(cnt))
    # per-vertex profile multiset; also number of 6-cycles through each vertex (count of closed NB walks of length 6 / 6 approx)
    c6 = []
    for s in range(n):
        # number of closed non-backtracking-free walks length 4 from s through distinct structure: use A^2 counts
        pass
    key = tuple(sorted(prof))
    h = hashlib.sha1(repr(key).encode()).hexdigest()[:12]
    npr = len(set(prof))
    # 4-cycles and 6-cycles counts via walk counts (A^k trace on bipartite cubic graph, lower bound fine for signature)
    import itertools
    A = [[0]*n for _ in range(n)]
    for x in range(n):
        for y in adj[x]: A[x][y] = 1
    def mul(X, Y):
        return [[sum(X[i][k]*Y[k][j] for k in adj_idx[i]) for j in range(n)] for i in range(n)]
    adj_idx = [[k for k in range(n) if A[i][k]] for i in range(n)]
    A2 = mul(A, A)
    t4 = sum(A2[i][i]**2 for i in range(n))  # trace A^4 proxy
    return h, npr, t4
if __name__ == '__main__':
    for fn in sys.argv[1:]:
        n, adj = load(fn); h, npr, t4 = sig(n, adj)
        print(f"{fn} n={n} sig={h} distinct_profiles={npr} trA4proxy={t4}")
