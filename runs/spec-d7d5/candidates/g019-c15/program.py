import itertools
import math
import random
import time

import numpy as np

import lib


def _code(M, p):
    """Encode rows of 4-digit base-p matrices as integers."""
    return ((M[:, 0] * p + M[:, 1]) * p + M[:, 2]) * p + M[:, 3]


class _Group:
    """PSL(2,p) or PGL(2,p) as a permutation source: R_s[g] = index of g*s."""

    def __init__(self, p, kind):
        self.p = p
        self.kind = kind
        grid = np.array(list(itertools.product(range(p), repeat=4)), dtype=np.int64)
        det = (grid[:, 0] * grid[:, 3] - grid[:, 1] * grid[:, 2]) % p
        mask = (det == 1) if kind == "PSL" else (det != 0)
        codes = np.unique(self._canon(grid[mask]))
        self.G = len(codes)
        self.lookup = np.full(p ** 4, -1, dtype=np.int64)
        self.lookup[codes] = np.arange(self.G)
        self.mats = np.stack([(codes // p ** 3) % p, (codes // p ** 2) % p,
                              (codes // p) % p, codes % p], axis=1)
        self.ident = int(self.lookup[self._canon(np.array([[1, 0, 0, 1]], dtype=np.int64))[0]])
        self._perms = {}

    def _canon(self, M):
        p = self.p
        if self.kind == "PSL":
            return np.minimum(_code(M % p, p), _code((-M) % p, p))
        best = _code(M % p, p)
        for lam in range(2, p):
            best = np.minimum(best, _code((lam * M) % p, p))
        return best

    def perm(self, s):
        """Return (R, Rinv) with R[g] = index(g*s) and Rinv its inverse permutation."""
        if s not in self._perms:
            if len(self._perms) > 3000:
                self._perms.clear()
            p = self.p
            M = self.mats
            e, f, g, h = (int(x) for x in M[s])
            a, b, c, d = M[:, 0], M[:, 1], M[:, 2], M[:, 3]
            P = np.stack([(a * e + b * g) % p, (a * f + b * h) % p,
                          (c * e + d * g) % p, (c * f + d * h) % p], axis=1)
            R = self.lookup[self._canon(P)]
            Ri = np.empty_like(R)
            Ri[R] = np.arange(self.G)
            self._perms[s] = (R, Ri)
        return self._perms[s]


def _reached(rows, src, D, N):
    """Vertices reached from src within D steps; rows[j] gives the j-th neighbour of every vertex."""
    reached = np.zeros(N, dtype=bool)
    reached[src] = True
    front = np.array([src], dtype=np.int64)
    for _ in range(D):
        mark = np.zeros(N, dtype=bool)
        mark[rows[:, front].ravel()] = True
        mark &= ~reached
        if not mark.any():
            break
        reached |= mark
        front = np.flatnonzero(mark)
    return reached


def _cost(grp, rows, D):
    """Unreached pairs from A_id (all vertices) plus from B_id (B side). Zero means valid."""
    G = grp.G
    N = 2 * G
    ra = _reached(rows, grp.ident, D, N)
    rb = _reached(rows, G + grp.ident, D, N)
    return int(N - ra.sum()) + int(G - rb[G:].sum())


def _anneal(grp, d, D, rng, deadline):
    """Search for d generators whose bipartite Cayley-type lift has diameter <= D. Returns S or None."""
    G = grp.G

    def row_of(s):
        R, Ri = grp.perm(s)
        return np.concatenate([G + R, Ri])

    def fresh():
        S = rng.sample(range(G), d)
        return S, np.stack([row_of(s) for s in S])

    S, rows = fresh()
    cur = _cost(grp, rows, D)
    best, last, it = cur, 0, 0
    t_start = time.monotonic()
    span = max(1e-3, deadline - t_start)
    while cur > 0:
        now = time.monotonic()
        if now > deadline:
            return None
        it += 1
        if it - last > 600:
            S, rows = fresh()
            cur = _cost(grp, rows, D)
            best, last = cur, it
            continue
        j = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        rows2 = rows.copy()
        rows2[j] = row_of(new)
        c = _cost(grp, rows2, D)
        temp = max(0.2, 1.5 * (1.0 - (now - t_start) / span))
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            S[j] = new
            rows = rows2
            cur = c
            if cur < best:
                best, last = cur, it
    return S


def _edges(grp, S):
    """Bipartite graph: A_g (index g) joined to B_{g*s} (index G + g*s) for each s in S."""
    G = grp.G
    edges = []
    for s in S:
        R, _ = grp.perm(s)
        edges.extend((g, G + int(R[g])) for g in range(G))
    return 2 * G, edges


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    end = t0 + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and degree d.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best, best_n = (n, e), n
            return True
        return False

    # Exact projective-plane incidence graph for diameter 3.
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n, e = lib.projective_plane_incidence(q)
                consider(n, e)
                break
        if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
            return best

    rng = random.Random(seed)

    # Bold construction: bipartite lifts over PSL(2,p) / PGL(2,p) acting by right multiplication.
    cands = []
    for p in (5, 7, 11, 13, 17):
        for kind in ("PGL", "PSL"):
            G = p * (p * p - 1) if kind == "PGL" else p * (p * p - 1) // 2
            if d <= G <= 2700:
                cands.append((G, p, kind))
    cands.sort(reverse=True)

    for G, p, kind in cands:
        now = time.monotonic()
        if now >= end:
            break
        if 2 * G <= best_n:
            break
        share = (end - now) * 0.4
        grp = _Group(p, kind)
        S = _anneal(grp, d, D, rng, now + share)
        if S is not None:
            n, e = _edges(grp, S)
            if consider(n, e):
                break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
