import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Algebraic baselines (safe, instant): projective plane, Araujo-Pardo-Lopez,
# and generalized quadrangle W(q) for D >= 4.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            try:
                return _gq_w(q)
            except Exception:
                return None
    return None


# ----------------------------------------------------------------------------
# Bold new family: bi-Cayley graphs over NON-ABELIAN groups.
#
# Group G of order N acts regularly on each side. Vertices (g,0) and (h,1),
# with (g,0) ~ (g*s,1) for s in S, |S| = d. Left multiplication is an
# automorphism that is transitive on each side, so the graph has diameter <= D
# iff the eccentricities of (e,0) and (e,1) are <= D. A cost evaluation is
# therefore just two numpy BFS passes, and annealing over S is very fast.
# Non-abelian groups avoid the commutation collisions that stall cyclic (Haar)
# lifts.
# ----------------------------------------------------------------------------

def _group(N, rng):
    """Random non-abelian semidirect product Z_m x| Z_k of order N.

    Returns (mulT, inv) as numpy arrays (mulT[x, y] = x*y, inv[x] = x^-1), or None.
    Element (a, b) is coded a*k + b, identity is 0, matching lib.semidirect_group.
    """
    ks = [k for k in range(2, N) if N % k == 0 and N // k >= 3]
    rng.shuffle(ks)
    for k in ks[:8]:
        m = N // k
        rs = [r for r in range(2, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not rs:
            continue
        r = rng.choice(rs)
        pw = np.array([pow(r, bb, m) for bb in range(k)], dtype=np.int64)
        x = np.arange(N, dtype=np.int64)
        a = x // k
        b = x % k
        mulT = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k \
            + (b[:, None] + b[None, :]) % k
        inv = np.argmax(mulT == 0, axis=1)
        return mulT, inv
    return None


def _cost(mulT, inv, S, N, D):
    """Number of (vertex, reached) failures from (e,0) and (e,1) within radius D. Zero means diameter <= D."""
    nb0 = mulT[:, S]          # side-0 vertex g -> side-1 vertices g*s
    nb1 = mulT[:, inv[S]]     # side-1 vertex h -> side-0 vertices h*s^-1
    total = 0
    for start in (0, 1):
        vis = [np.zeros(N, dtype=bool), np.zeros(N, dtype=bool)]
        fr = np.zeros(N, dtype=bool)
        fr[0] = True
        vis[start] |= fr
        side = start
        for _ in range(D):
            nbr = nb0 if side == 0 else nb1
            tgt = np.zeros(N, dtype=bool)
            tgt[nbr[fr].ravel()] = True
            new = tgt & ~vis[1 - side]
            vis[1 - side] |= new
            fr = new
            side = 1 - side
            if not fr.any():
                break
        total += 2 * N - int(vis[0].sum()) - int(vis[1].sum())
    return total


def _anneal(mulT, inv, N, d, D, rng, deadline, iters):
    """Anneal the connection set S (|S| = d) to zero cost. Returns (S or None, cost)."""
    S = rng.sample(range(N), d)
    c = _cost(mulT, inv, np.array(S, dtype=np.int64), N, D)
    for it in range(iters):
        if c == 0:
            break
        if it % 32 == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        new = rng.randrange(N)
        if new in S:
            continue
        S2 = list(S)
        S2[i] = new
        c2 = _cost(mulT, inv, np.array(S2, dtype=np.int64), N, D)
        T = 1.5 * (1.0 - it / iters) + 0.05
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, c = S2, c2
    return (S if c == 0 else None), c


def _edges(mulT, S, N):
    """Full bi-Cayley graph: side 0 is 0..N-1, side 1 is N..2N-1."""
    E = []
    for s in S:
        col = mulT[:, s]
        for g in range(N):
            E.append((g, N + int(col[g])))
    return 2 * N, E


def _cayley_phase(best_n, moore, d, D, rng, deadline, consider):
    """Climb N = half the order, one feasible group/set pair at a time."""
    cur = max(best_n // 2, d)
    while time.monotonic() < deadline:
        N_try = cur + (1 if rng.random() < 0.6 else rng.randint(2, 4))
        if 2 * N_try > moore:
            break
        grp = _group(N_try, rng)
        if grp is None:
            continue
        mulT, inv = grp
        S, _ = _anneal(mulT, inv, N_try, d, D, rng, deadline, 1500)
        if S is None:
            continue
        n, e = _edges(mulT, S, N_try)
        if consider(n, e):
            cur = N_try


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    # Algebraic baselines (fast).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Bold phase: bi-Cayley over non-abelian groups, most of the budget.
    cay_deadline = start + 0.8 * time_limit
    if best_n < moore and d >= 2 and D >= 2:
        _cayley_phase(best_n, moore, d, D, rng, cay_deadline, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
