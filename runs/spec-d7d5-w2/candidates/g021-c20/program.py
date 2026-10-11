import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact constructions kept as safe, instant answers for the small-D calibration.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New construction: single-block bi-Cayley (Haar-type) graphs over finite groups.
#
# Group G = Z_m x| Z_k2 (order N), elements coded a*k2+b. Connection set S with |S| = d.
# Vertices A_g and B_h (g, h in G), with A_g ~ B_{g*s} for s in S. Every vertex has
# degree d, the graph is bipartite with 2N vertices.
#
# Left multiplication is an automorphism that is transitive on each side, so the
# diameter is at most D iff BFS from A_e and from B_e reaches every vertex within D.
# The search is simulated annealing over S, minimizing the number of unreached
# vertices. A ladder over the group order N (growth plus bisection) finds the
# largest N for which a valid S exists. Every accepted graph passes lib.is_valid.
# ----------------------------------------------------------------------------

def _group_tables(m, k2, r):
    """Return (R_all, Ri_all) with R_all[s, g] = g*s and Ri_all[s, h] = h*s^-1 for G = Z_m x| Z_k2."""
    N = m * k2
    x = np.arange(N, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    mul = ((a[:, None] + powers[b][:, None] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    inv = np.argmax(mul == 0, axis=1)  # the unique h with g*h = identity (index 0)
    R_all = np.ascontiguousarray(mul.T)
    Ri_all = np.ascontiguousarray(mul[:, inv].T)
    return R_all, Ri_all


def _cost(S, N, D, R_all, Ri_all):
    """Total number of vertices not reached within distance D from A_e and from B_e."""
    RS = R_all[S]
    RiS = Ri_all[S]
    total = 0
    for start_side in (0, 1):
        visA = np.zeros(N, dtype=bool)
        visB = np.zeros(N, dtype=bool)
        front = np.array([0], dtype=np.int64)
        if start_side == 0:
            visA[0] = True
        else:
            visB[0] = True
        side = start_side
        for _ in range(D):
            mask = np.zeros(N, dtype=bool)
            if side == 0:
                mask[RS[:, front].ravel()] = True
                new = mask & ~visB
                visB |= new
            else:
                mask[RiS[:, front].ravel()] = True
                new = mask & ~visA
                visA |= new
            front = np.flatnonzero(new)
            side ^= 1
            if front.size == 0:
                break
        total += 2 * N - int(visA.sum()) - int(visB.sum())
    return total


def _anneal(N, d, D, rng, iters, deadline, R_all, Ri_all):
    """Simulated annealing over connection sets S of size d. Returns S (cost 0) or None."""
    S = rng.sample(range(N), d)
    cur = _cost(np.array(S, dtype=np.int64), N, D, R_all, Ri_all)
    for it in range(iters):
        if cur == 0:
            return S
        if (it & 63) == 0 and time.monotonic() > deadline:
            break
        T = 1.0 * (1.0 - it / iters) + 0.05
        p = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        S2 = list(S)
        S2[p] = x
        c2 = _cost(np.array(S2, dtype=np.int64), N, D, R_all, Ri_all)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            S, cur = S2, c2
    return S if cur == 0 else None


def _attempt(N, d, D, rng, deadline):
    """Try several random group structures of order N until one yields a valid S."""
    while time.monotonic() < deadline:
        divs = [k for k in range(1, min(N, 24) + 1) if N % k == 0]
        k2 = rng.choice(divs)
        m = N // k2
        r = 1
        if k2 > 1 and m > 2:
            for _ in range(60):
                c = rng.randrange(2, m)
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
        R_all, Ri_all = _group_tables(m, k2, r)
        S = _anneal(N, d, D, rng, 3000, deadline, R_all, Ri_all)
        if S is not None:
            return S, R_all
    return None


def _to_graph(N, S, R_all):
    """Bipartite graph on 2N vertices: A_g = g, B_h = N + h, with edges (g, N + g*s) for s in S."""
    edges = []
    for s in S:
        row = R_all[s].tolist()
        edges.extend((g, N + row[g]) for g in range(N))
    return 2 * N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def accept(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return n <= best_n and n > 0 and lib.is_valid(n, e, d, D)

    # Exact constructions: return immediately where they are optimal.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            accept(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            accept(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Ladder search over the group order N (vertices per side).
    try:
        Nmax = lib.moore_bound(d, D) // 2
        lo = best_n // 2
        hi = None
        while time.monotonic() < deadline:
            if lo >= Nmax:
                break
            if hi is None:
                N = lo + max(1, lo // 16)
            else:
                if hi - lo <= 1:
                    break
                N = (lo + hi) // 2
            N = min(N, Nmax)
            if N < d:
                N = d
            now = time.monotonic()
            remaining = deadline - now
            att_deadline = min(deadline, now + max(2.0, 0.3 * remaining))
            res = _attempt(N, d, D, rng, att_deadline)
            ok = False
            if res is not None:
                S, R_all = res
                n2, e2 = _to_graph(N, S, R_all)
                ok = accept(n2, e2)
            if ok:
                lo = max(lo, N)
            else:
                hi = N
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
