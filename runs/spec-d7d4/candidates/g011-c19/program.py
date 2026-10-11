import math
import random
import time

import numpy as np

import lib

# Bi-Cayley search over groups. Vertices are A_x and B_y for x, y in G, with
# A_x ~ B_{x*s} for s in S (|S| = d). Left multiplication by G is an automorphism,
# so diameter <= D reduces to two BFS runs, from A_e and from B_e.
# Groups: affine F_q x| C_k (k | q-1) and metacyclic Z_m x|_r Z_k.

_FIELDS = {}


def _field(q):
    if q not in _FIELDS:
        _FIELDS[q] = lib.GF(q)
    return _FIELDS[q]


def _specs(G):
    """Descriptions of all groups of order G that this search knows how to build."""
    specs = []
    for q in range(2, G + 1):
        if G % q or not lib.is_prime_power(q):
            continue
        k = G // q
        if (q - 1) % k == 0:
            specs.append(("aff", q, k))
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                specs.append(("sd", m, k, r))
    return specs


def _group_table(spec):
    """Multiplication table (numpy, G x G) with identity at index 0."""
    if spec[0] == "aff":
        _, q, k = spec
        F = _field(q)
        G = q * k
        h = F.pow(F.primitive_element(), (q - 1) // k)
        H = np.array([F.pow(h, i) for i in range(k)], dtype=np.int64)
        hidx = np.full(q, -1, dtype=np.int64)
        hidx[H] = np.arange(k, dtype=np.int64)
        ea = np.repeat(H, q)
        eb = np.tile(np.arange(q, dtype=np.int64), k)
        A1, A2 = ea[:, None], ea[None, :]
        B1, B2 = eb[:, None], eb[None, :]
        na = F.mul_table[A1, A2]
        nb = F.add_table[F.mul_table[A1, B2], B1]
        return hidx[na] * q + nb
    _, m, k, r = spec
    _, mul, _ = lib.semidirect_group(m, k, r)
    G = m * k
    return np.array([[mul(x, y) for y in range(G)] for x in range(G)], dtype=np.int64)


def _inverses(mt):
    G = mt.shape[0]
    inv = np.zeros(G, dtype=np.int64)
    rows, cols = np.nonzero(mt == 0)
    inv[rows] = cols
    return inv.tolist()


def _unreached(src, S, Sinv, mtl, G, D):
    """Number of the 2G vertices at distance > D from src (src is A_e = 0 or B_e = G)."""
    N = 2 * G
    seen = bytearray(N)
    seen[src] = 1
    frontier = [src]
    count = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            if u < G:
                row = mtl[u]
                for s in S:
                    w = G + row[s]
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            else:
                row = mtl[u - G]
                for t in Sinv:
                    w = row[t]
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
        count += len(nxt)
        frontier = nxt
        if not frontier:
            break
    return N - count


def _cost(S, inv, mtl, G, D):
    """Zero exactly when the bi-Cayley graph on S has diameter <= D."""
    Sinv = [inv[s] for s in S]
    return _unreached(0, S, Sinv, mtl, G, D) + _unreached(G, S, Sinv, mtl, G, D)


def _search(d, G, inv, mtl, D, rng, iters, deadline):
    S = rng.sample(range(G), d)
    c = _cost(S, inv, mtl, G, D)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        t = rng.randrange(G)
        if t in S:
            continue
        T = S[:]
        T[i] = t
        ct = _cost(T, inv, mtl, G, D)
        if ct <= c or rng.random() < 0.03:
            S, c = T, ct
    return S if c == 0 else None


def _bicayley_edges(G, mtl, S):
    edges = [(x, G + mtl[x][s]) for x in range(G) for s in S]
    return 2 * G, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is always valid for D >= 2.
    best = list(lib.haar_graph(d, range(d)))
    moore = lib._moore_bound(d, D)

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    if best[0] >= moore:
        return best[0], best[1]

    # D = 3: projective plane incidence graph of the largest prime power q <= d - 1.
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break

    if best[0] >= moore:
        return best[0], best[1]

    # Main search: bi-Cayley graphs over groups of order G (graph has 2G vertices).
    Gmax = min(moore // 2, 400)
    Gmin = max(d, Gmax // 2)
    spec_cache = {}
    while time.monotonic() < deadline:
        lo = max(Gmin, best[0] // 2 + 1)
        if lo > Gmax:
            break
        span = Gmax - lo
        # Bias toward the low end of the band, so improvements ratchet upward.
        G = lo + int(rng.random() ** 2 * (span + 1))
        if G > Gmax:
            G = Gmax
        if G not in spec_cache:
            spec_cache[G] = _specs(G)
        specs = spec_cache[G]
        if not specs:
            continue
        spec = rng.choice(specs)
        mt = _group_table(spec)
        G = mt.shape[0]
        mtl = mt.tolist()
        inv = _inverses(mt)
        S = _search(d, G, inv, mtl, D, rng, 600, deadline)
        if S is not None:
            consider(*_bicayley_edges(G, mtl, S))

    if not lib.is_valid(best[0], best[1], d, D):
        best = list(lib.haar_graph(d, range(d)))
    return best[0], best[1]
