import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact families (kept as exact fallbacks for the cases they cover).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d; diameter 3."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez graph of degree d (q = d - 2 a prime power >= 3); diameter 3."""
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    return lib.araujo_lopez_graph(q)


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New main construction: cyclic Haar graphs found by annealing a connection set.
#
# Haar graph H(m, S): A_x ~ B_{x+s} for s in S (|S| = d), order 2m, bipartite, degree d.
# Translating both sides by the same amount is an automorphism, so the diameter is
# at most D iff, starting from A_0, every A-vertex is reached within D steps and every
# B-vertex is reached within D steps. That is an O(D * d * m) numpy check.
#
# Search: for a candidate m, anneal the d-element set S to drive the number of
# unreached vertices to zero. Binary search over m, with a time budget per attempt.
# Every returned graph is re-checked with lib.is_valid, and the search falls back
# to the best exact construction (or K_{d,d}).
# ----------------------------------------------------------------------------

def _cost(m, S, D, ar):
    """Number of vertices NOT within distance D of A_0 in H(m, S) (0 means valid)."""
    idx_plus = (ar[None, :] + S[:, None]) % m    # A_x -> B_{x+s}, so A_x is hit from B_{x+s}
    idx_minus = (ar[None, :] - S[:, None]) % m   # B_y is hit from A_{y-s}
    A = np.zeros(m, dtype=bool)
    A[0] = True
    B = np.zeros(m, dtype=bool)
    for _ in range(D):
        nA = B[idx_plus].any(axis=0)
        nB = A[idx_minus].any(axis=0)
        A2 = A | nA
        B2 = B | nB
        if np.array_equal(A2, A) and np.array_equal(B2, B):
            break
        A, B = A2, B2
    return 2 * m - int(A.sum()) - int(B.sum())


def _anneal(m, d, D, rng, dl):
    """Anneal a d-element subset of Z_m until its Haar graph has diameter <= D. Returns the set or None."""
    ar = np.arange(m, dtype=np.int64)
    cur_list = rng.sample(range(m), d)
    cur = _cost(m, np.array(cur_list, dtype=np.int64), D, ar)
    t0 = time.monotonic()
    span = max(1e-3, dl - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= dl:
            break
        frac = (now - t0) / span
        temp = 0.6 * (1.0 - frac) + 0.05
        i = rng.randrange(d)
        new = rng.randrange(m)
        if new in cur_list:
            continue
        cand = cur_list.copy()
        cand[i] = new
        c2 = _cost(m, np.array(cand, dtype=np.int64), D, ar)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            cur_list, cur = cand, c2
    return cur_list if cur == 0 else None


def _haar_search(d, D, rng, deadline, lo, hi):
    """Binary search for the largest m with a valid Haar graph H(m, S). Returns (m, S) or None."""
    best = None
    while lo <= hi:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 0.3:
            break
        per = max(1.0, remaining / 3.0)
        att_dl = min(deadline, now + per)
        mid = (lo + hi) // 2
        S = _anneal(mid, d, D, rng, att_dl)
        if S is not None:
            best = (mid, S)
            lo = mid + 1
        else:
            hi = mid - 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        try:
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
        except Exception:
            pass

    # Exact constructions: return immediately when they are optimal.
    if D >= 3:
        try:
            pg = _best_pg(d)
        except Exception:
            pg = None
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

        if D == 3:
            try:
                aj = _araujo(d)
            except Exception:
                aj = None
            if aj is not None:
                consider(aj[0], aj[1])
                return best

    if D == 4 and time.monotonic() < deadline:
        try:
            gq = _best_gq(d)
        except Exception:
            gq = None
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: cyclic Haar graphs with an annealed connection set.
    if d >= 2 and time.monotonic() < deadline - 0.5:
        try:
            moore = lib.moore_bound(d, D)
            lo = max(d, best_n // 2 + 1)
            hi = max(lo, moore // 2)
            res = _haar_search(d, D, rng, deadline, lo, hi)
        except Exception:
            res = None
        if res is not None:
            m, S = res
            try:
                n_h, e_h = lib.haar_graph(m, S)
                consider(n_h, e_h)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
