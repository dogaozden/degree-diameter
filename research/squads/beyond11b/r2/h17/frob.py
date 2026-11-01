# Frobenius group G = Z_p x|_r Z_k, element x = a*k + j  (a in Z_p, j in Z_k), (a,j)(b,l) = (a + r^j b, j+l).
# Haar graph H(G,S): (g,A) ~ (s g,B). Memory ~ N bytes per bitset; N = p*k <= 1e6 here.
import numpy as np, sys

class Frob:
    def __init__(self, p, k, r):
        self.p, self.k, self.r = p, k, r
        self.N = p * k
        self.R = np.array([pow(r, j, p) for j in range(k)], dtype=np.int64)       # r^j
        self.Rinv = np.array([pow(pow(r, j, p), p - 2, p) for j in range(k)], dtype=np.int64)
        # check r has order k
        assert pow(r, k, p) == 1 and all(pow(r, i, p) != 1 for i in range(1, k)), "r must have order k"
        self.a = np.arange(self.N) // k
        self.j = np.arange(self.N) % k

    def mul(self, x, y):
        """elementwise product of index arrays x, y (numpy int arrays or scalars)"""
        x = np.asarray(x); y = np.asarray(y)
        ax, jx = x // self.k, x % self.k
        ay, jy = y // self.k, y % self.k
        a = (ax + self.R[jx] * ay) % self.p
        return a * self.k + (jx + jy) % self.k

    def inv(self, x):
        x = np.asarray(x)
        ax, jx = x // self.k, x % self.k
        jj = (self.k - jx) % self.k
        b = (-(self.Rinv[jx] * ax)) % self.p      # (a,j)^{-1} = (-r^{-j} a, -j)
        # check: b must satisfy a_x + r^{j} b = 0 -> b = -r^{-j} a_x; r^{-j} = Rinv[j]
        return b * self.k + jj

    def ident(self):
        return 0

def ball_exact(G, S, h, side):
    """Exact set X = U^h (contains e since e in S), U = {s^-1 t} (side A) or {s t^-1} (side B).
    Returns boolean array over G."""
    S = [int(s) for s in S]
    if side == 'A':
        U = sorted({int(G.mul(G.inv(s), t)) for s in S for t in S})
    else:
        U = sorted({int(G.mul(s, G.inv(t))) for s in S for t in S})
    cur = np.zeros(G.N, dtype=bool); cur[0] = True
    for _ in range(h):
        idx = np.nonzero(cur)[0]
        new = cur.copy()
        for u in U:
            new[G.mul(idx, u)] = True
        cur = new
    return cur, U

def covers(G, S, D):
    """True iff diameter <= D (D odd = 2h+1): both same-side balls of radius 2h are everything."""
    h = (D - 1) // 2
    XA, _ = ball_exact(G, S, h, 'A')
    XB, _ = ball_exact(G, S, h, 'B')
    return XA, XB

def nb_counts(G, S, L):
    """Non-backtracking walks of length L from (e,A) in H(G,S); returns counts on A-side (length N, float64).
    Vertex ids: A-element g -> g ; B-element h -> N+h. Letter i: A g -> B (s_i g) ; B h -> A (s_i^-1 h).
    cnt[v,i] = walks arriving at v via letter i. A walk may not use letter i twice in a row (backtrack)."""
    N = G.N; S = [int(s) for s in S]; d = len(S)
    g = np.arange(N)
    T = np.zeros((2 * N, d), dtype=np.int64)
    for i, s in enumerate(S):
        T[:N, i] = N + G.mul(s, g)                      # A -> B
        T[N:, i] = G.mul(int(G.inv(s)), g)              # B -> A
    cnt = np.zeros((2 * N, d), dtype=np.float64)
    for i in range(d):
        cnt[T[0, i], i] += 1.0
    for _ in range(L - 1):
        tot = cnt.sum(axis=1)
        new = np.zeros_like(cnt)
        for i in range(d):
            new[:, i] = np.bincount(T[:, i], weights=tot - cnt[:, i], minlength=2 * N)
        cnt = new
    return cnt.sum(axis=1)[:N]
