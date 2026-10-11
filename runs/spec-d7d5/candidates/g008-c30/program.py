import itertools
import math
import random
import time

import numpy as np

import lib

# Candidate family for the weakest targets (d >= 5, D >= 3):
#   Bi-Cayley lifts over Z_m x| Z_k2 (k base vertices per side, group order G).
#   Construction differs from the previous annealer: each layer (a perfect matching
#   between the A and B sides) is chosen greedily from sampled candidates, scored by
#   how many (block representative, vertex) pairs are within distance D so far.
#   The greedy state is then repaired by time-bounded annealing over voltages and
#   B-side target swaps. Every returned graph is checked with lib.is_valid, and
#   K_{d,d} (diameter 2) is kept as the fallback.
# This code was not executed here, so its gains are unmeasured.

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4, 5, 6)
_SLICE = 8.0      # seconds per bi-Cayley trial
_CANDS = 24       # candidate layers sampled per greedy step


# ----------------------------------------------------------------------------
# Exact families (returned or used as candidates when they apply).
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
# Bi-Cayley machinery.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{p,h} = (k+p)*G + h.
# Layer l is a permutation perm[l] of range(k) plus voltages vol[l][i] in G:
#   A_{i,g} ~ B_{perm[l][i], g*vol[l][i]}.
# Left multiplication by a group element is an automorphism, so the reach
# cost only needs the identity of each of the 2k blocks as representatives.
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
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
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e)).

    Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h.
    """
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


def _fill_block(nbr, l, i, p, s, k, G, Ts, Invs):
    """Write layer l's darts for A block i (to B block p with voltage s) and the matching B block p."""
    nbr[l, i * G:(i + 1) * G] = (k + p) * G + Ts[s]
    nbr[l, (k + p) * G:(k + p + 1) * G] = i * G + Invs[s]


def _cost(k, G, D, nbr):
    """Unreached (block representative, vertex) pairs at distance > D; 0 means diameter <= D."""
    d, N = nbr.shape
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
    return 2 * k * N - int(_POP[reach].sum())


def _dups(perms, vols, k):
    """Number of repeated (i, perm, voltage) darts, which would create duplicate edges."""
    keys = set()
    count = 0
    for l in range(len(perms)):
        for i in range(k):
            key = (i, perms[l][i], vols[l][i])
            if key in keys:
                count += 1
            else:
                keys.add(key)
    return count


def _greedy(d, D, k, G, Ts, Invs, rng, deadline):
    """Build layers one at a time, keeping the sampled candidate with the lowest cost."""
    N = 2 * k * G
    nbr = np.empty((d, N), dtype=np.int64)
    perms, vols = [], []
    for l in range(d):
        best = None
        for _ in range(_CANDS):
            if time.monotonic() > deadline:
                break
            perm = rng.sample(range(k), k)
            vol = [rng.randrange(G) for _ in range(k)]
            for i in range(k):
                _fill_block(nbr, l, i, perm[i], vol[i], k, G, Ts, Invs)
            c = _cost(k, G, D, nbr[:l + 1]) + _PENALTY * _dups(perms + [perm], vols + [vol], k)
            if best is None or c < best[0]:
                best = (c, perm, vol)
        if best is None:
            return None
        _, perm, vol = best
        perms.append(perm)
        vols.append(vol)
        for i in range(k):
            _fill_block(nbr, l, i, perm[i], vol[i], k, G, Ts, Invs)
    return perms, vols


def _anneal(d, D, k, G, Ts, Invs, perms, vols, rng, deadline):
    """Time-bounded annealing over voltages and B-side target swaps. Returns (n, edges) or None."""
    N = 2 * k * G
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _fill_block(nbr, l, i, perms[l][i], vols[l][i], k, G, Ts, Invs)
    cost = _cost(k, G, D, nbr) + _PENALTY * _dups(perms, vols, k)
    c0 = float(max(cost, 1))
    start = time.monotonic()
    span = max(1e-3, deadline - start)

    while cost > 0:
        now = time.monotonic()
        if now > deadline:
            break
        frac = (now - start) / span
        temp = max(0.3, 0.02 * c0 * (1.0 - frac))
        l = rng.randrange(d)

        if k > 1 and rng.random() < 0.3:
            i1, i2 = rng.sample(range(k), 2)
            pl = perms[l]
            pl[i1], pl[i2] = pl[i2], pl[i1]
            _fill_block(nbr, l, i1, pl[i1], vols[l][i1], k, G, Ts, Invs)
            _fill_block(nbr, l, i2, pl[i2], vols[l][i2], k, G, Ts, Invs)
            c2 = _cost(k, G, D, nbr) + _PENALTY * _dups(perms, vols, k)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                pl[i1], pl[i2] = pl[i2], pl[i1]
                _fill_block(nbr, l, i1, pl[i1], vols[l][i1], k, G, Ts, Invs)
                _fill_block(nbr, l, i2, pl[i2], vols[l][i2], k, G, Ts, Invs)
        else:
            i = rng.randrange(k)
            old = vols[l][i]
            new = rng.randrange(G)
            if new == old:
                continue
            vols[l][i] = new
            _fill_block(nbr, l, i, perms[l][i], new, k, G, Ts, Invs)
            c2 = _cost(k, G, D, nbr) + _PENALTY * _dups(perms, vols, k)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                vols[l][i] = old
                _fill_block(nbr, l, i, perms[l][i], old, k, G, Ts, Invs)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
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
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bi-Cayley search with a bandit over the number k of base vertices per side.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline - 0.5:
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        slice_end = min(deadline, time.monotonic() + _SLICE)
        state = _greedy(d, D, k, G, Ts, Invs, rng, slice_end)
        if state is None:
            continue
        perms, vols = state
        res = _anneal(d, D, k, G, Ts, Invs, perms, vols, rng, slice_end)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
