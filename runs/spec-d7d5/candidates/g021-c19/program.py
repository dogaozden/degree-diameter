import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact / safe baseline families (unchanged from the parent).
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


def _araujo_for(d):
    """Araujo-Pardo & Lopez record graph for d = q + 2 with q a prime power (D = 3 only)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# NEW family: bipartite Haar graphs over abelian groups Z_a x Z_b, with the
# connection set S (|S| = d) found by simulated annealing directly on the
# diameter defect.
#
# Vertices: A_g = g (0..G-1), B_h = G + h. Edge A_g ~ B_{g+s} for s in S.
# Translations are automorphisms, so distance (A_g, A_h) = dist(A_0, A_{h-g}),
# (A_g, B_h) = dist(A_0, B_{h-g}), (B_g, B_h) = dist(B_0, B_{h-g}).
# Hence it suffices to BFS from A_0 and from B_0. The defect is the number of
# unreached (start, vertex) pairs; zero means diameter <= D.
# ----------------------------------------------------------------------------

def _divisors(G):
    return [a for a in range(1, G + 1) if G % a == 0]


def _abel_shifts(G, a, b, S):
    """Return (Sp, Sn) with Sp[i, g] = g + S[i] and Sn[i, g] = g - S[i] in Z_a x Z_b."""
    ar = np.arange(G, dtype=np.int64)
    gx, gy = ar // b, ar % b
    sx, sy = S // b, S % b
    Sp = ((gx[None, :] + sx[:, None]) % a) * b + (gy[None, :] + sy[:, None]) % b
    Sn = ((gx[None, :] - sx[:, None]) % a) * b + (gy[None, :] - sy[:, None]) % b
    return Sp, Sn


def _abel_cost(G, a, b, S, D):
    """Number of unreached (start, vertex) pairs after D BFS rounds from A_0 and B_0."""
    Sp, Sn = _abel_shifts(G, a, b, S)
    RA = np.zeros((2, G), dtype=bool)  # RA[s, g]: A_g reached from start s
    RB = np.zeros((2, G), dtype=bool)  # RB[s, h]: B_h reached from start s
    RA[0, 0] = True                    # start 0 is A_0
    RB[1, 0] = True                    # start 1 is B_0
    for _ in range(D):
        nB = RB | RA[:, Sn].any(axis=1)  # B_h gets A_{h-s}
        nA = RA | RB[:, Sp].any(axis=1)  # A_g gets B_{g+s}
        if np.array_equal(nA, RA) and np.array_equal(nB, RB):
            break
        RA, RB = nA, nB
    return 4 * G - int(RA.sum()) - int(RB.sum())


def _abel_sa(G, a, b, d, D, rng, deadline):
    """Simulated annealing over the d-element connection set. Returns S (np array) or None."""
    if G < d:
        return None
    S = rng.sample(range(G), d)
    inS = set(S)
    cost = _abel_cost(G, a, b, np.array(S, dtype=np.int64), D)
    if cost == 0:
        return np.array(S, dtype=np.int64)
    T0 = max(1.0, 0.05 * cost)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    while time.monotonic() < deadline:
        frac = (time.monotonic() - t0) / span
        temp = max(0.2, T0 * (1.0 - frac))
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in inS:
            continue
        old = S[i]
        S[i] = new
        c2 = _abel_cost(G, a, b, np.array(S, dtype=np.int64), D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            inS.discard(old)
            inS.add(new)
            cost = c2
            if cost == 0:
                return np.array(S, dtype=np.int64)
        else:
            S[i] = old
    return None


def _abel_edges(G, a, b, S):
    """Edge list of the bipartite Haar graph over Z_a x Z_b with connection set S."""
    Sp, _ = _abel_shifts(G, a, b, S)
    edges = []
    for i in range(len(S)):
        row = Sp[i].tolist()
        for g in range(G):
            edges.append((g, G + row[g]))
    return edges


# ----------------------------------------------------------------------------
# Parent family kept as a hedge: bi-Cayley lifts over Z_m x| Z_k2.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                r = None
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e))."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _unreached(k, N, reach):
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    reach = _reach(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))
    best_cost = cost
    last_improve = 0

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last_improve > patience:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
                if cost < best_cost:
                    best_cost, last_improve = cost, t
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
            l = rng.randrange(d)
            if block < k:
                i = block
            else:
                i = layers[l].index(block - k)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        r2 = _reach(k, G, D, nbr, d)
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
            if cost < best_cost:
                best_cost, last_improve = cost, t
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    final_deadline = start + max(1.0, time_limit - 3.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
        if D == 3:
            ar = _araujo_for(d)
            if ar is not None:
                consider(ar[0], ar[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: abelian Haar-graph annealing (primary) plus the parent's
    # semidirect bi-Cayley search (hedge).
    if d >= 2 and time.monotonic() < deadline:
        bump = max(1, best_n // 100)
        attempt_sec = max(4.0, budget / 6.0)
        while time.monotonic() < deadline:
            att = min(deadline, time.monotonic() + attempt_sec)
            if rng.random() < 0.25:
                k = rng.choice(_KS)
                base = best_n // (2 * k)
                target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
                g = _sample_group(target, rng)
                if g is None:
                    continue
                m, k2, r = g
                G, Ts, Invs = _semidirect_tables(m, k2, r)
                if 2 * k * G <= best_n:
                    continue
                res = _search(d, D, k, G, Ts, Invs, rng, att, 4000, 1200)
                if res is not None:
                    consider(res[0], res[1])
            else:
                cur = best_n // 2
                G = cur + bump
                a = rng.choice(_divisors(G))
                b = G // a
                S = _abel_sa(G, a, b, d, D, rng, att)
                if S is not None:
                    consider(2 * G, _abel_edges(G, a, b, S))
                else:
                    bump = max(1, bump // 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
