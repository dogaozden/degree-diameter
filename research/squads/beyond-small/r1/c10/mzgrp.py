# metacyclic group Z_n : Z_k, elements (i,j) = x^i y^j, index g = i*k+j
# product (i,j)(a,b) = (i + r^j a, j + b);  beta(i,j) = (u i, v j)
from collections import deque
class Grp:
    def __init__(s, n, k, r, u=1, v=1):
        s.n, s.k, s.r, s.u, s.v = n, k, r, u, v
        s.N = n*k
        s.rp = [pow(r, j, n) for j in range(k)]
        s.rinv = pow(r, -1, n)
        s.rinvp = [pow(s.rinv, j, n) for j in range(k)]
    def mul(s, g, h):
        n, k = s.n, s.k
        i, j = divmod(g, k); a, b = divmod(h, k)
        return ((i + s.rp[j]*a) % n)*k + (j+b) % k
    def inv(s, g):
        n, k = s.n, s.k
        i, j = divmod(g, k)
        b = (-j) % k
        a = (-i*s.rinvp[j]) % n
        return a*k + b
    def beta(s, g):
        i, j = divmod(g, s.k)
        return ((s.u*i) % s.n)*s.k + (s.v*j) % s.k
    def psi(s, g):
        return s.inv(s.beta(g))
def valid(n, k, r, u, v):
    from math import gcd
    if gcd(r, n) != 1 or pow(r, k, n) != 1: return False
    if gcd(u, n) != 1 or gcd(v, k) != 1: return False
    if (u*u) % n != 1 or (v*v) % k != 1: return False
    if pow(r, v, n) != r % n: return False
    return True
def haar_edges_ok(G, S, D=5):
    # BFS from (e,0) in H(G,S): vertices g (side 0), N+g (side 1); (g,0)~(s g,1)
    N = G.N; S = list(S)
    adj = [[] for _ in range(2*N)]
    for g in range(N):
        for s in S:
            h = G.mul(s, g)
            adj[g].append(N+h); adj[N+h].append(g)
    e = 0
    dist = [-1]*(2*N); dist[e] = 0; q = deque([e])
    while q:
        x = q.popleft()
        for y in adj[x]:
            if dist[y] < 0: dist[y] = dist[x]+1; q.append(y)
    return max(dist), (min(dist) >= 0)
def XX_uncovered(G, S):
    inv = {s: G.inv(s) for s in S}
    X = set(G.mul(inv[s], t) for s in S for t in S)
    Z = set(G.mul(x, y) for x in X for y in X)
    return G.N - len(Z)
