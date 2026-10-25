"""c3: cyclic-torus orbit search for partial ovoids of Q(6,q) (hexfam_r1 card c3).

Models (prime q, odd):
  A: V = GF(q^6) + GF(q), Q(x,t) = Tr_{q^6/q}-form Tr(c N(x)) + a t^2, c in GF(q)*, a in GF(q)*.
     cyclic group x -> lam x (lam of order q^3+1); Frobenius x -> x^q (t fixed).
  B: V = GF(q^3) + GF(q^3) + GF(q), Q(x,y,t) = Tr(x y) + a t^2.
     cyclic group (x,y) -> (mu x, mu^-1 y), mu of order q^3-1; Frobenius (x,y)->(x^q,y^q).
Every abstract isometry g (7x7 over GF(q), preserving the polar Gram) is conjugated to our coordinates by
T from Geo.to_std(Gram), then turned into a point permutation with Geo.perm.
"""
import sys, random, time
import numpy as np
TOOLS = '/home/user/degree-diameter/research/projects/hexagon-family/tools'
sys.path.insert(0, TOOLS)
from q6lib import Geo, A7, orbits, inv_mod
from mwc import max_weight_clique


def trim(a):
    while a and a[-1] == 0:
        a.pop()
    return a


def pmul(a, b, q):
    if not a or not b:
        return []
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] = (r[i + j] + x * y) % q
    return trim(r)


def pmod(a, b, q):
    a = trim([x % q for x in a]); b = trim([x % q for x in b])
    inv = pow(b[-1], q - 2, q); db = len(b) - 1
    while a and len(a) - 1 >= db:
        c = (a[-1] * inv) % q; sh = len(a) - 1 - db
        for i in range(db + 1):
            a[sh + i] = (a[sh + i] - c * b[i]) % q
        trim(a)
    return a


def pgcd(a, b, q):
    a = trim([x % q for x in a]); b = trim([x % q for x in b])
    while b:
        a, b = b, pmod(a, b, q)
    if a:
        inv = pow(a[-1], q - 2, q); a = [(x * inv) % q for x in a]
    return a


def ppow(a, e, f, q):
    r = [1]; base = pmod(a, f, q)
    while e:
        if e & 1:
            r = pmod(pmul(r, base, q), f, q)
        base = pmod(pmul(base, base, q), f, q)
        e >>= 1
    return r


def factor(n):
    ps = []; d = 2
    while d * d <= n:
        if n % d == 0:
            ps.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        ps.append(n)
    return ps


def is_irred(f, q, n):
    x = [0, 1]; Xs = {}; Xk = x
    for k in range(1, n + 1):
        Xk = ppow(Xk, q, f, q); Xs[k] = Xk
    def diff(A):
        m = max(len(A), 2)
        return trim([((A[i] if i < len(A) else 0) - (x[i] if i < len(x) else 0)) % q for i in range(m)])
    if diff(Xs[n]) != []:
        return False
    for r in factor(n):
        if len(pgcd(f, diff(Xs[n // r]), q)) != 1:
            return False
    return True


class GF:
    """GF(q^n) for prime q as polynomials mod an irreducible monic f (coefficient lists, length n)."""
    def __init__(self, q, n, seed=1):
        self.q, self.n = q, n
        rng = random.Random(seed)
        while True:
            f = [rng.randrange(q) for _ in range(n)] + [1]
            if f[0] and is_irred(f, q, n):
                break
        self.f = f

    def pad(self, a):
        return (list(a) + [0] * self.n)[:self.n]

    def mul(self, a, b):
        return self.pad(pmod(pmul(a, b, self.q), self.f, self.q))

    def pw(self, a, e):
        return self.pad(ppow(a, e, self.f, self.q))

    def basis(self, i):
        return [0] * i + [1]

    def mulmat(self, w):
        M = np.zeros((self.n, self.n), dtype=np.int64)
        for j in range(self.n):
            M[:, j] = self.mul(w, self.basis(j))
        return M

    def tr(self, w):
        return int(np.trace(self.mulmat(w)) % self.q)

    def frobmat(self, k):
        M = np.zeros((self.n, self.n), dtype=np.int64)
        for j in range(self.n):
            M[:, j] = self.pw(self.basis(j), self.q ** k)
        return M

    def elem_of_order(self, N, rng):
        Q = self.q ** self.n - 1
        assert Q % N == 0
        one = self.pad([1])
        while True:
            g = [rng.randrange(self.q) for _ in range(self.n)]
            if not any(g):
                continue
            h = self.pw(g, Q // N)
            if self.pw(h, N) != one:
                continue
            if all(self.pw(h, N // r) != one for r in factor(N)):
                return h


def model_A(q, c, a, seed=1, ordseed=2):
    F = GF(q, 6, seed)
    Q3 = [F.pw(F.basis(i), q ** 3) for i in range(6)]
    G = np.zeros((7, 7), dtype=np.int64)
    for i in range(6):
        for j in range(6):
            G[i, j] = F.tr(F.mul(F.mul([c], Q3[i]), F.basis(j)))
    G[6, 6] = (2 * a) % q
    lam = F.elem_of_order(q ** 3 + 1, random.Random(ordseed))
    def blk(M6):
        M = np.eye(7, dtype=np.int64); M[:6, :6] = M6; return M
    gens = {'cyc': blk(F.mulmat(lam)), 'frob': blk(F.frobmat(1))}
    return G, gens, q ** 3 + 1


def model_B(q, a, seed=1, ordseed=2):
    F = GF(q, 3, seed)
    G = np.zeros((7, 7), dtype=np.int64)
    for i in range(3):
        for j in range(3):
            t = F.tr(F.mul(F.basis(i), F.basis(j)))
            G[i, 3 + j] = t; G[3 + j, i] = t
    G[6, 6] = (2 * a) % q
    mu = F.elem_of_order(q ** 3 - 1, random.Random(ordseed))
    mui = F.pw(mu, q ** 3 - 2)
    M = np.eye(7, dtype=np.int64)
    M[0:3, 0:3] = F.mulmat(mu); M[3:6, 3:6] = F.mulmat(mui)
    Fr = np.eye(7, dtype=np.int64)
    Fr[0:3, 0:3] = F.frobmat(1); Fr[3:6, 3:6] = F.frobmat(1)
    Sw = np.eye(7, dtype=np.int64)
    Sw[0:3, 0:3] = 0; Sw[3:6, 3:6] = 0
    for i in range(3):
        Sw[i, 3 + i] = 1; Sw[3 + i, i] = 1
    Sw[6, 6] = 1
    gens = {'cyc': M, 'frob': Fr, 'swap': Sw}
    return G, gens, q ** 3 - 1


def build_perms(geo, G7, gens):
    """conjugate abstract generators into our coordinates and return point permutations"""
    q = geo.q
    T = geo.to_std(G7)
    Ti = inv_mod(T, q)
    out = {}
    for k, M in gens.items():
        # isometry check of the abstract generator w.r.t. G7
        R = (M.T @ G7 @ M) % q
        assert (R == G7 % q).all(), ('abstract generator not an isometry', k)
        Mo = (T @ M @ Ti) % q
        Rq = (Mo.T @ A7 @ Mo) % q
        s = Rq[0, 4]
        assert ((Rq - s * A7) % q == 0).all(), ('ours not isometry', k)
        out[k] = geo.perm(Mo)
    return out


def perm_pow(p, k):
    res = np.arange(len(p)); base = p.copy()
    while k:
        if k & 1:
            res = base[res]
        base = base[base]
        k >>= 1
    return res


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]
