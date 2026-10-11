import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Strategy (bold change): the parent searched bi-Cayley graphs over groups by
# annealing with a Python-level BFS, which was slow for orders near 342 and
# spent most of its time on near-miss voltage lifts. This version switches to:
#
#   * Vectorised group-table construction (affine AGL(1,p) and semidirect
#     Z_m x| Z_k) with associativity spot checks, so many groups can be tried.
#   * Bi-Cayley graphs B(G, S) with |S| = d and identity forced into S
#     (WLOG by relabelling B-vertices), searched by annealing with a numpy
#     BFS from the two orbit representatives A_1 and B_1.
#   * Orders searched strictly upward from the best known order, in
#     escalating time rounds, so every success raises the bar.
#
# Safe fallbacks: K_{d,d} (diameter 2), projective-plane incidence and the
# Araujo-Pardo-Lopez graph for D = 3. Every candidate passes lib.is_valid
# before it is accepted.
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


def _affine_table(p):
    """Multiplication table of AGL(1, p); element x encodes x -> u*x + b with u = x//p + 1, b = x % p."""
    G = p * (p - 1)
    idx = np.arange(G, dtype=np.int64)
    U = idx // p + 1
    B = idx % p
    M = (((U[:, None] * U[None, :]) % p) - 1) * p + (U[:, None] * B[None, :] + B[:, None]) % p
    return G, M


def _semidirect_table(m, k, r):
    """Multiplication table of Z_m x| Z_k with (a, b) * (c, d) = (a + r^b c, b + d)."""
    G = m * k
    idx = np.arange(G, dtype=np.int64)
    a = idx // k
    b = idx % k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    M = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    return G, M


def _valid_table(G, M):
    """Identity check plus randomized associativity check."""
    if M.shape != (G, G):
        return False
    ar = np.arange(G)
    if not (np.array_equal(M[0], ar) and np.array_equal(M[:, 0], ar)):
        return False
    rng = np.random.default_rng(1)
    x, y, z = rng.integers(0, G, (3, 300))
    return bool(np.array_equal(M[M[x, y], z], M[x, M[y, z]]))


def _make(spec):
    try:
        if spec[0] == "aff":
            G, M = _affine_table(spec[1])
        else:
            _, m, k, r = spec
            G, M = _semidirect_table(m, k, r)
        if not _valid_table(G, M):
            return None
        inv = np.argmax(M == 0, axis=1).astype(np.int64)
        return G, M, inv
    except Exception:
        return None


def _candidates(lo, hi):
    """Group specs with order in [lo, hi], ascending by order; affine first, then cyclic, then semidirect."""
    specs = []
    for p in range(3, hi + 2):
        o = p * (p - 1)
        if lo <= o <= hi and _is_prime(p):
            specs.append((o, 0, ("aff", p)))
    for o in range(max(lo, 3), hi + 1):
        specs.append((o, 3, ("sd", o, 1, 1)))
        for k in range(2, o):
            if o % k:
                continue
            m = o // k
            if m < 2:
                continue
            rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            for r in rs[:2]:
                specs.append((o, 1, ("sd", m, k, r)))
    specs.sort(key=lambda t: (t[0], t[1]))
    return [(o, s) for o, _, s in specs]


def _cost(M, inv, S, G, D):
    """Unreached (vertex) count from A_1 and B_1 within D steps; zero means diameter <= D."""
    Sa = np.array(S, dtype=np.int64)
    adj = np.vstack([G + M[:, Sa], M[:, inv[Sa]]])
    N = 2 * G
    total = 0
    for src in (0, G):
        seen = np.zeros(N, dtype=bool)
        seen[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            nb = adj[frontier].ravel()
            nb = nb[~seen[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            seen[nb] = True
            frontier = nb
        total += N - int(np.count_nonzero(seen))
    return total


def _search(M, inv, G, d, D, rng, deadline):
    """Annealed search over S (|S| = d, 0 in S) with restarts until cost 0 or deadline."""
    if G - 1 < d - 1 or d < 2:
        return None
    while time.monotonic() < deadline:
        S = [0] + rng.sample(range(1, G), d - 1)
        c = _cost(M, inv, S, G, D)
        T = 1.0
        for _ in range(600):
            if c == 0 or time.monotonic() >= deadline:
                break
            i = rng.randrange(1, d)
            x = rng.randrange(1, G)
            if x in S:
                continue
            T2 = S[:]
            T2[i] = x
            c2 = _cost(M, inv, T2, G, D)
            if c2 <= c or rng.random() < math.exp((c - c2) / T):
                S, c = T2, c2
            T = max(0.05, T * 0.995)
        if c == 0:
            return S
    return None


def _bc_edges(M, S, G):
    """Edges A_x ~ B_{x*s}; no duplicates since right multiplication by distinct s is injective."""
    E = [(x, G + int(M[x, s])) for x in range(G) for s in S]
    return 2 * G, E


def _best_pg(d):
    for q in range(d - 1, 1, -1):
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
    rng = random.Random(seed)

    if d < 1:
        return 1, []
    if D <= 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    if D == 2:
        return best

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    moore = lib.moore_bound(d, D)
    if best_n >= moore or d < 3:
        return best

    # Bi-Cayley search over groups, ordered upward from the best known order.
    moore_half = moore // 2
    lo0 = max(2 * d, best_n // 2 + 1, int(0.44 * moore_half))
    span = max(40, lo0 // 4)
    best_G = best_n // 2
    rnd = 0
    while time.monotonic() < deadline:
        lo = max(lo0, best_G + 1)
        hi = lo + span
        specs = _candidates(lo, hi)
        if not specs:
            span *= 2
            continue
        budget = 0.25 * (1.6 ** min(rnd, 6))
        rnd += 1
        for o, spec in specs:
            if time.monotonic() >= deadline:
                break
            if o <= best_G or o < lo0:
                continue
            grp = _make(spec)
            if grp is None:
                continue
            G, M, inv = grp
            if G - 1 < d - 1:
                continue
            dl = min(deadline, time.monotonic() + budget)
            S = _search(M, inv, G, d, D, rng, dl)
            if S is not None:
                n, e = _bc_edges(M, S, G)
                if consider(n, e):
                    best_G = max(best_G, G)
        if best_n >= moore:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
