import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Group wrapper: right multiplication tables are cached lazily as numpy arrays,
# so a cover-graph evaluation costs a few vectorised BFS steps.
# ----------------------------------------------------------------------------

class _Grp:
    def __init__(self, n, ident, mulf, invf):
        self.n = n
        self.ident = ident
        self._mul = mulf
        self._inv = invf
        self._r = {}
        self._ri = {}

    def right(self, s):
        """Array g -> g*s over all group indices g."""
        arr = self._r.get(s)
        if arr is None:
            mul = self._mul
            arr = np.array([mul(g, s) for g in range(self.n)], dtype=np.int64)
            self._r[s] = arr
        return arr

    def right_inv(self, s):
        """Array h -> h*s^{-1}."""
        arr = self._ri.get(s)
        if arr is None:
            arr = self.right(self._inv(s))
            self._ri[s] = arr
        return arr


def _semidirect_group(n, rng):
    """Random semidirect product Z_m x| Z_k of order n (k = 1 gives a cyclic group)."""
    ks = [k for k in range(1, min(n, 16) + 1) if n % k == 0 and n // k >= 2]
    if not ks:
        return None
    k = rng.choice(ks)
    m = n // k
    if k == 1:
        r = 1
    else:
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not cands:
            return None
        r = rng.choice(cands)
    order, mul, inv = lib.semidirect_group(m, k, r)
    return _Grp(order, 0, mul, inv)


def _matrix_group(q, psl):
    """PSL(2,q) (psl=True, q odd or even) or PGL(2,q), as projective classes of 2x2 matrices over GF(q)."""
    F = lib.GF(q)

    def norm(M):
        for x in M:
            if x:
                iv = F.inv(x)
                return tuple(F.mul(iv, y) for y in M)
        return None

    def mm(A, B):
        a, b, c, d = A
        e, f, g, h = B
        return (F.add(F.mul(a, e), F.mul(b, g)), F.add(F.mul(a, f), F.mul(b, h)),
                F.add(F.mul(c, e), F.mul(d, g)), F.add(F.mul(c, f), F.mul(d, h)))

    def det(M):
        a, b, c, d = M
        return F.sub(F.mul(a, d), F.mul(b, c))

    sq = {F.mul(x, x) for x in range(1, q)}
    elems = set()
    for M in itertools.product(range(q), repeat=4):
        dt = det(M)
        if dt == 0:
            continue
        if psl and dt not in sq:
            continue
        elems.add(norm(M))
    E = sorted(elems)
    idx = {M: i for i, M in enumerate(E)}

    def mulf(g, s):
        return idx[norm(mm(E[g], E[s]))]

    def invf(s):
        a, b, c, d = E[s]
        return idx[norm((d, F.neg(b), F.neg(c), a))]

    return _Grp(len(E), idx[(1, 0, 0, 1)], mulf, invf)


# ----------------------------------------------------------------------------
# Bi-Cayley cover search.
#
# For a group G of order n and generators s_1..s_d (distinct), the bipartite graph
# A_g ~ B_{g s_i} is vertex-transitive on each side (left multiplication), so its
# diameter is at most D iff BFS from A_1 and from B_1 reaches everything in D steps.
# Cost = number of unreached (source, vertex) pairs; 0 means valid.
# ----------------------------------------------------------------------------

def _cover_cost(M, Mi, n, ident, D):
    total = 0
    empty = np.empty(0, dtype=np.int64)
    for side in (0, 1):
        visA = np.zeros(n, dtype=bool)
        visB = np.zeros(n, dtype=bool)
        if side == 0:
            visA[ident] = True
            fa = np.array([ident], dtype=np.int64)
            fb = empty
        else:
            visB[ident] = True
            fb = np.array([ident], dtype=np.int64)
            fa = empty
        for _ in range(D):
            if fa.size == 0 and fb.size == 0:
                break
            nbB = np.zeros(n, dtype=bool)
            if fa.size:
                nbB[M[fa].ravel()] = True
            nbB &= ~visB
            nbA = np.zeros(n, dtype=bool)
            if fb.size:
                nbA[Mi[fb].ravel()] = True
            nbA &= ~visA
            visB |= nbB
            visA |= nbA
            fa = np.flatnonzero(nbA)
            fb = np.flatnonzero(nbB)
        total += 2 * n - int(visA.sum()) - int(visB.sum())
    return total


def _anneal(G, d, D, rng, deadline, iters):
    """Search for d distinct generators giving cover cost 0. Returns the list or None."""
    n = G.n

    def ev(S):
        M = np.stack([G.right(s) for s in S], axis=1)
        Mi = np.stack([G.right_inv(s) for s in S], axis=1)
        return _cover_cost(M, Mi, n, G.ident, D)

    S = rng.sample(range(n), d)
    c = ev(S)
    T = 1.0
    for _ in range(iters):
        if c == 0 or time.monotonic() >= deadline:
            break
        i = rng.randrange(d)
        t = rng.randrange(n)
        if t in S:
            continue
        S2 = S[:]
        S2[i] = t
        c2 = ev(S2)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, c = S2, c2
        T = max(0.1, T * 0.998)
    return S if c == 0 else None


def _cover_graph(G, S):
    n = G.n
    edges = []
    for s in S:
        arr = G.right(s).tolist()
        edges.extend((g, n + arr[g]) for g in range(n))
    return 2 * n, edges


# ----------------------------------------------------------------------------
# Small classical fallbacks.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(min(d - 1, 23), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if not lib.is_valid(best_n, best_e, d, D):
        return 1, []

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Main search: bi-Cayley covers over groups of growing order.
    moore = lib._moore_bound(d, D)
    rng = random.Random(seed * 1000003 + d * 101 + D)
    best_half = best_n // 2
    matrix_specs = [(9, True), (8, True), (11, True), (9, False)]
    matrix_cache = {}

    while time.monotonic() < deadline:
        lo = max(best_half + 1, d, 3)
        if 2 * lo > moore:
            break
        hi = min(lo + 24, moore // 2)

        G = None
        if rng.random() < 0.2:
            spec = rng.choice(matrix_specs)
            if spec not in matrix_cache:
                matrix_cache[spec] = _matrix_group(spec[0], spec[1])
            G = matrix_cache[spec]
            if not (lo <= G.n <= moore // 2):
                G = None
        if G is None:
            if hi < lo:
                break
            G = _semidirect_group(rng.randint(lo, hi), rng)
            if G is None or G.n < lo or G.n > moore // 2:
                continue

        attempt_deadline = min(deadline, time.monotonic() + 2.5)
        S = None
        for _ in range(2):
            if time.monotonic() >= attempt_deadline:
                break
            S = _anneal(G, d, D, rng, attempt_deadline, 2500)
            if S is not None:
                break
        if S is None:
            continue

        n2, e2 = _cover_graph(G, S)
        if consider(n2, e2):
            best_half = G.n

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
