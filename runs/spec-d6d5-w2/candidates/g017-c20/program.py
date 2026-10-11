import itertools
import math
import random
import time

import numpy as np

import lib


# Known record orders used only to set the search window (order > record/2 beats it).
RECORDS = {(6, 5): 684}


# ----------------------------------------------------------------------------
# Valid baseline families (diameter <= 3 and 4 graphs remain valid for larger D).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3 (diameter 3)."""
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
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over small groups G (order window just above the record).
#
# Vertices A_x = x and B_w = G + w. Connection set S (|S| = d, containing the
# identity WLOG, since relabelling B_y -> B_{y g} maps S to S g). Edge
# A_x ~ B_{x s}. Left multiplication is an automorphism, so the graph has
# diameter <= D iff A_1 and B_1 reach every vertex within D steps.
#
# Search: tabu search over connection sets with sampled single-element swaps,
# restarts on stagnation. This replaces the earlier annealed voltage search.
# ----------------------------------------------------------------------------

def _is_prime(p):
    if p < 2:
        return False
    i = 2
    while i * i <= p:
        if p % i == 0:
            return False
        i += 1
    return True


def _affine_mul(p):
    """Multiplication in AGL(1, p); element (u-1)*p + b encodes x -> u*x + b."""
    def mul(x, y):
        u, b = divmod(x, p)
        u += 1
        v, c = divmod(y, p)
        v += 1
        return (((u * v) % p) - 1) * p + (u * c + b) % p
    return mul


def _group_candidates(lo, hi, rng, cap=120):
    """Group specs with order in [lo, hi], ascending order."""
    out = []
    p0 = max(3, math.isqrt(lo))
    for p in range(p0, math.isqrt(hi) + 3):
        o = p * (p - 1)
        if _is_prime(p) and lo <= o <= hi:
            out.append((o, ("aff", p)))
    for k in range(1, 41):
        mlo = max(2, -(-lo // k))
        mhi = hi // k
        for m in range(mlo, mhi + 1):
            o = m * k
            if k == 1:
                rs = [1]
            else:
                rs = [r for r in range(1, m)
                      if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
                if len(rs) > 4:
                    rs = rng.sample(rs, 4)
            for r in rs:
                out.append((o, ("sd", m, k, r)))
    rng.shuffle(out)
    out.sort(key=lambda t: t[0])
    return out[:cap]


def _make_table(spec):
    if spec[0] == "aff":
        p = spec[1]
        G = p * (p - 1)
        mul = _affine_mul(p)
    else:
        _, m, k, r = spec
        G, mul, _ = lib.semidirect_group(m, k, r)
    M = np.empty((G, G), dtype=np.int64)
    for x in range(G):
        M[x] = [mul(x, y) for y in range(G)]
    ar = np.arange(G)
    if not (np.array_equal(M[0], ar) and np.array_equal(M[:, 0], ar)):
        return None
    return G, M


def _bc_cost(M, inv, G, S, D):
    """Unreached (vertex) count from A_1 and B_1 within D steps. Zero means valid."""
    Sa = np.asarray(S, dtype=np.int64)
    adj = np.vstack([G + M[:, Sa], M[:, inv[Sa]]])
    N = 2 * G
    total = 0
    for src in (0, G):
        seen = np.zeros(N, dtype=bool)
        seen[src] = True
        frontier = np.array([src], dtype=np.int64)
        cnt = 1
        for _ in range(D):
            nb = adj[frontier].ravel()
            nb = nb[~seen[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            seen[nb] = True
            cnt += nb.size
            frontier = nb
        total += N - cnt
    return total


def _tabu(M, inv, G, d, D, deadline, rng, K=12, tenure_len=7, patience=500):
    """Tabu search over connection sets S (containing 0). Returns S with cost 0 or None."""
    if d - 1 > G - 1:
        return None
    S = [0] + rng.sample(range(1, G), d - 1)
    c = _bc_cost(M, inv, G, S, D)
    best_c = c
    last_imp = 0
    tabu = {}
    it = 0
    while c > 0:
        if time.monotonic() >= deadline:
            return None
        it += 1
        if it - last_imp > patience:
            S = [0] + rng.sample(range(1, G), d - 1)
            c = _bc_cost(M, inv, G, S, D)
            best_c = c
            last_imp = it
            tabu.clear()
            continue
        Sset = set(S)
        cb, cT, cmove = None, None, None
        for _ in range(K):
            i = rng.randrange(1, d)
            x = rng.randrange(1, G)
            if x in Sset:
                continue
            T = S[:]
            T[i] = x
            ct = _bc_cost(M, inv, G, T, D)
            if tabu.get(x, -1) >= it and ct >= c:
                continue
            if cb is None or ct < cb:
                cb, cT, cmove = ct, T, (S[i], x)
        if cT is None:
            continue
        tabu[cmove[0]] = it + tenure_len
        S, c = cT, cb
        if c < best_c:
            best_c = c
            last_imp = it
    return S


def _bc_edges(M, S, G):
    E = [(x, G + int(M[x, s])) for x in range(G) for s in S]
    return 2 * G, E


def _bicayley_phase(d, D, lo, width, deadline, rng, consider):
    """Search bi-Cayley graphs with orders above the current best, smallest first."""
    best_G = lo - 1
    rnd = 0
    while time.monotonic() < deadline:
        budget = (1.5, 3.0, 6.0)[min(rnd, 2)]
        base = max(best_G + 1, lo)
        if base > 900:
            return
        hi = base + width + 8 * rnd
        cands = _group_candidates(base, min(hi, 900), rng)
        rnd += 1
        for o, spec in cands:
            if time.monotonic() >= deadline:
                return
            if o <= best_G:
                continue
            tab = _make_table(spec)
            if tab is None:
                continue
            G, M = tab
            inv = np.argmax(M == 0, axis=1)
            sub = min(deadline, time.monotonic() + budget)
            S = _tabu(M, inv, G, d, D, sub, rng)
            if S is None:
                continue
            n, e = _bc_edges(M, S, G)
            consider(n, e)
            best_G = max(best_G, G)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed * 1000003 + d * 131 + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

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

    # Bold change for D >= 5: tabu search over bi-Cayley graphs, targeting
    # group orders just above the record half (order > record/2 beats it).
    if D >= 5 and d >= 3:
        moore_half = lib.moore_bound(d, D) // 2
        lo = max(2 * d, best_n // 2 + 1, int(0.4 * moore_half),
                 RECORDS.get((d, D), 0) // 2 + 1)
        _bicayley_phase(d, D, lo, max(30, lo // 10), deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
