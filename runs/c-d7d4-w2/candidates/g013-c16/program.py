import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley (bipartite Cayley) search.
#
# Groups G = Z_m x| Z_k (element (a, b) coded as a*k + b, with r^k = 1 mod m),
# which includes cyclic and direct-product groups. Take a connection set S of
# d distinct group elements. The graph has vertices a_x and b_y for x, y in G,
# with a_x ~ b_{x*s} for s in S. Left multiplication is an automorphism that is
# transitive on each side, so the diameter is the larger eccentricity of a_e and
# b_e. Each candidate therefore costs two BFS runs over the group.
# ----------------------------------------------------------------------------

class _Group:
    def __init__(self, m, k, r):
        self.m, self.k, self.r = m, k, r
        self.N = m * k
        self.P = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
        ar = np.arange(self.N, dtype=np.int64)
        self.a_of = ar // k
        self.b_of = ar % k

    def mul_all(self, s):
        """Array of x * s over all group elements x (right multiplication)."""
        c, dd = divmod(s, self.k)
        a = (self.a_of + self.P[self.b_of] * c) % self.m
        b = (self.b_of + dd) % self.k
        return a * self.k + b

    def inv(self, s):
        """Inverse of element s = (a, b): (-r^(-b) a, -b)."""
        a, b = divmod(s, self.k)
        nb = (-b) % self.k
        na = (-pow(self.r, nb, self.m) * a) % self.m
        return na * self.k + nb


def _group_params(N, rng):
    """A few (m, k, r) parameters for groups of order N."""
    params = []
    for m in range(2, N + 1):
        if N % m:
            continue
        k = N // m
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
        if not rs:
            continue
        others = [r for r in rs if r != 1]
        picks = [1] if 1 in rs else []
        take = min(2 if picks else 3, len(others))
        picks += rng.sample(others, take)
        params += [(m, k, r) for r in picks]
    return params


def _reaches_all(NA, NB, N, D, side):
    """BFS from vertex 0 on `side` (0 = a-side, 1 = b-side); True if all vertices lie within D."""
    vis = [np.zeros(N, dtype=bool), np.zeros(N, dtype=bool)]
    front = [np.zeros(0, dtype=np.int64), np.zeros(0, dtype=np.int64)]
    vis[side][0] = True
    front[side] = np.array([0], dtype=np.int64)
    for _ in range(D):
        if front[0].size == 0 and front[1].size == 0:
            break
        cand_B = NA[front[0]].ravel()
        cand_A = NB[front[1]].ravel()
        newB = np.unique(cand_B[~vis[1][cand_B]])
        newA = np.unique(cand_A[~vis[0][cand_A]])
        vis[1][newB] = True
        vis[0][newA] = True
        front = [newA, newB]
    return bool(vis[0].all() and vis[1].all())


def _tables(g, S):
    NA = np.stack([g.mul_all(s) for s in S], axis=1)                 # a_x -> b_{x s}
    NB = np.stack([g.mul_all(g.inv(s)) for s in S], axis=1)          # b_y -> a_{y s^-1}
    return NA, NB


def _check(g, S, D):
    NA, NB = _tables(g, S)
    return _reaches_all(NA, NB, g.N, D, 0) and _reaches_all(NA, NB, g.N, D, 1)


def _graph_of(g, S):
    N = g.N
    NA = np.stack([g.mul_all(s) for s in S], axis=1)
    edges = [(x, N + int(y)) for x in range(N) for y in NA[x].tolist()]
    return 2 * N, edges


def _bicayley_search(d, D, hi, lo, deadline, rng, consider):
    """Descending search over orders N (graph order 2N), with iteratively growing time slices."""
    params_cache = {}
    best_N = lo - 1
    slice_t = 0.03
    while time.monotonic() < deadline and best_N < hi:
        for N in range(hi, best_N, -1):
            if time.monotonic() >= deadline:
                break
            if N not in params_cache:
                params_cache[N] = _group_params(N, rng)
            params = params_cache[N]
            if not params:
                continue
            groups = [_Group(*p) for p in params]
            end = min(deadline, time.monotonic() + slice_t)
            found = False
            while not found and time.monotonic() < end:
                g = rng.choice(groups)
                S = rng.sample(range(g.N), d)
                if _check(g, S, D):
                    n2, e2 = _graph_of(g, S)
                    consider(n2, e2)
                    found = True
            if found:
                best_N = N
                break
        slice_t *= 2


# ----------------------------------------------------------------------------
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    n0, e0 = lib.haar_graph(d, range(d))
    st = {"n": n0, "e": list(e0)}

    def consider(n, e):
        if n > st["n"] and lib.is_valid(n, e, d, D):
            st["n"], st["e"] = n, list(e)
            return True
        return False

    try:
        # Known constructions that are cheap to build (diameter 3 cases).
        if D >= 3:
            if lib.is_prime_power(d - 1):
                consider(*lib.projective_plane_incidence(d - 1))
            if d - 2 >= 3 and lib.is_prime_power(d - 2):
                try:
                    consider(*lib.araujo_lopez_graph(d - 2))
                except ValueError:
                    pass

        # Main search: bipartite Cayley graphs over small groups.
        moore = lib.moore_bound(d, D)
        hi = moore // 2
        lo = max(d, 2)
        if hi >= lo and time.monotonic() < deadline:
            _bicayley_search(d, D, hi, lo, deadline, rng, consider)
    except Exception:
        pass

    if not lib.is_valid(st["n"], st["e"], d, D):
        return lib.haar_graph(d, range(d))
    return st["n"], list(st["e"])
