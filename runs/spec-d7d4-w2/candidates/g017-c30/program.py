import itertools
import math
import random
import time

import numpy as np

import lib

# ----------------------------------------------------------------------------
# New construction: regular bipartite "semidirect Haar" (bi-Cayley) graphs.
#
# Group G of order N (cyclic Z_m, or Z_m x|_r Z_k), connection set S of size d.
# Vertices a_x and b_y (x, y in G); a_x ~ b_{x*s} for s in S. Each vertex has
# degree d, the graph is bipartite with 2N vertices, and left translations are
# automorphisms. Diameter <= D holds iff the walk-balls from a_e and from b_e
# cover G on both sides. A simulated-annealing search over S minimises the number
# of uncovered (side, element) pairs. Orders are tried in ascending order, and
# the largest verified graph is kept.
#
# Fallbacks, always valid: K_{d,d}; PG(2,q) incidence for D=3; the GQ W(q)
# incidence graph for D=4; Araujo-Lopez for D=3; the even cycle for d=2.
# ----------------------------------------------------------------------------

_BUDGET_PER_ORDER = 1.2  # seconds of annealing per candidate order N


def _semidirect_tables(m, k, r):
    """Multiplication and inverse tables for Z_m x|_r Z_k, element (a, b) coded as a*k+b."""
    N = m * k
    P = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    idx = np.arange(N, dtype=np.int64)
    a = idx // k
    b = idx % k
    MUL = ((a[:, None] + P[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    nb = (-b) % k
    INV = ((-(P[nb] * a)) % m) * k + nb
    return MUL, INV


def _groups(N, rng, limit=3):
    """Candidate (m, k, r) with m*k = N and a valid semidirect product (cyclic when k = 1)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not rs:
            continue
        rng.shuffle(rs)
        for r in rs[:2]:
            out.append((m, k, r))
    rng.shuffle(out)
    return out[:limit]


def _cost(S, MUL, INV, D):
    """Number of (side, element) pairs not within distance D of a_e (start 0) or b_e (start 1)."""
    N = MUL.shape[0]
    Sinv = INV[S]
    total = 0
    for start in (0, 1):
        A = np.zeros(N, dtype=bool)
        B = np.zeros(N, dtype=bool)
        if start == 0:
            A[0] = True
        else:
            B[0] = True
        for t in range(1, D + 1):
            if (start + t) % 2 == 1:
                src = np.flatnonzero(A)
                B[MUL[np.ix_(src, S)].ravel()] = True
            else:
                src = np.flatnonzero(B)
                A[MUL[np.ix_(src, Sinv)].ravel()] = True
        total += (N - int(A.sum())) + (N - int(B.sum()))
    return total


def _search(MUL, INV, d, D, deadline, rng):
    """Simulated annealing over connection sets S of size d; returns np.array or None."""
    N = MUL.shape[0]
    if N <= d:
        return None
    S = rng.sample(range(N), d)
    cur = _cost(np.array(S, dtype=np.int64), MUL, INV, D)
    best = cur
    T = 1.0
    stall = 0
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        i = rng.randrange(d)
        new = rng.randrange(N)
        if new in S:
            continue
        S2 = S[:]
        S2[i] = new
        c2 = _cost(np.array(S2, dtype=np.int64), MUL, INV, D)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            S, cur = S2, c2
        if cur < best:
            best = cur
            stall = 0
        else:
            stall += 1
        T = max(0.3, T * 0.999)
        if stall > 3000:
            S = rng.sample(range(N), d)
            cur = _cost(np.array(S, dtype=np.int64), MUL, INV, D)
            best = cur
            T = 1.0
            stall = 0
    return np.array(S, dtype=np.int64)


def _edges(N, S, MUL):
    """Bipartite edges a_x -- b_{x*s} for x in G, s in S."""
    xs = np.repeat(np.arange(N, dtype=np.int64), len(S))
    ys = MUL[xs, np.tile(S, N)]
    return [(int(x), int(N + y)) for x, y in zip(xs, ys)]


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (diameter 4, degree q+1).
# ----------------------------------------------------------------------------

def _gq_w(q):
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    deadline = start + max(0.3 * T, min(0.85 * T, T - 3.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2 or d == 1:
        return best
    if d == 2:
        consider(2 * D, [(i, (i + 1) % (2 * D)) for i in range(2 * D)])
        return best

    M = lib.moore_bound(d, D)
    if best[0] >= M:
        return best

    # Structured fallbacks.
    if D == 3:
        if lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
    if D == 4:
        q = next((q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)), None)
        if q is not None:
            try:
                consider(*_gq_w(q))
            except Exception:
                pass

    if best[0] >= M:
        return best

    # Main search: bi-Cayley graphs over small groups, orders tried ascending.
    Nmax = min(M // 2, 1500)
    N = max(d + 1, M // 6)
    while N <= Nmax and time.monotonic() < deadline:
        groups = _groups(N, rng)
        found = None
        for (m, k, r) in groups:
            now = time.monotonic()
            if now >= deadline:
                break
            MUL, INV = _semidirect_tables(m, k, r)
            dl = min(deadline, now + _BUDGET_PER_ORDER / max(1, len(groups)))
            S = _search(MUL, INV, d, D, dl, rng)
            if S is not None:
                found = (MUL, S)
                break
        if found is not None:
            MUL, S = found
            consider(2 * N, _edges(N, S, MUL))
        N += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
