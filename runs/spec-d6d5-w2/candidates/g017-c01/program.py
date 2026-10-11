import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bold change: search bi-Cayley graphs over a broad family of small groups,
# ordered by ascending order so the search aims just above the current record.
# Groups include Heisenberg groups H(p) (nonabelian, order p^3), non-cyclic
# abelian groups Z_a x Z_b, affine groups AGL(1,p), and semidirect products
# Z_m x| Z_k. A bi-Cayley graph on G with connection set S (|S| = d) has
# 2|G| vertices and is bipartite, d-regular, and vertex-transitive on each side,
# so distances from A_1 and B_1 decide the diameter.
#
# Safe fallbacks: K_{d,d} (diameter 2) and PG(2,q) incidence when D = 3.
# Every returned graph is checked with lib.is_valid.
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


def _table(G, mul):
    M = np.empty((G, G), dtype=np.int64)
    for x in range(G):
        for y in range(G):
            M[x, y] = mul(x, y)
    return M


def _heis_mul(p):
    pp = p * p

    def mul(x, y):
        a, r = divmod(x, pp)
        b, c = divmod(r, p)
        a2, r2 = divmod(y, pp)
        b2, c2 = divmod(r2, p)
        return ((a + a2) % p) * pp + ((b + b2) % p) * p + (c + c2 + a * b2) % p
    return mul


def _ab_mul(a, b):
    def mul(x, y):
        i, j = divmod(x, b)
        i2, j2 = divmod(y, b)
        return ((i + i2) % a) * b + (j + j2) % b
    return mul


def _aff_mul(p):
    def mul(x, y):
        u, b = divmod(x, p)
        u += 1
        v, c = divmod(y, p)
        v += 1
        return (((u * v) % p) - 1) * p + (u * c + b) % p
    return mul


def _specs(g_lo, g_hi, per_order_cap=4):
    """Group specs for orders in [g_lo, g_hi], ascending in order."""
    out = []
    for G in range(max(g_lo, 3), g_hi + 1):
        specs = [("cyc", G)]
        a = 2
        while a * a <= G:
            if G % a == 0 and (G // a) % a == 0:
                specs.append(("ab", a, G // a))
            a += 1
        p = round(G ** (1.0 / 3.0))
        if p >= 3 and p ** 3 == G and _is_prime(p):
            specs.append(("heis", p))
        for p in range(3, int(G ** 0.5) + 3):
            if p * (p - 1) == G and _is_prime(p):
                specs.append(("aff", p))
        cnt = 0
        for k in range(2, G // 2 + 1):
            if G % k:
                continue
            m = G // k
            if m < 3:
                continue
            rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
            if rs:
                specs.append(("sd", m, k, rs[0]))
                cnt += 1
            if cnt >= 3:
                break
        out.append((G, specs[:per_order_cap + 2]))
    return out


def _make_table(spec):
    kind = spec[0]
    if kind == "cyc":
        G = spec[1]
        return _table(G, lambda x, y: (x + y) % G)
    if kind == "ab":
        a, b = spec[1], spec[2]
        return _table(a * b, _ab_mul(a, b))
    if kind == "heis":
        p = spec[1]
        return _table(p ** 3, _heis_mul(p))
    if kind == "aff":
        p = spec[1]
        return _table(p * (p - 1), _aff_mul(p))
    _, m, k, r = spec
    order, mul, _ = lib.semidirect_group(m, k, r)
    return _table(order, mul)


def _identity_ok(M):
    G = M.shape[0]
    ar = np.arange(G)
    return bool(np.array_equal(M[0], ar) and np.array_equal(M[:, 0], ar))


def _bc_cost(M, inv, S, G, D):
    """Unreached count from A_1 (node 0) and B_1 (node G) within D steps; 0 means valid."""
    Sa = np.asarray(S, dtype=np.int64)
    iS = inv[Sa]
    adj = np.vstack([G + M[:, Sa], M[:, iS]])
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


def _search_group(M, G, d, D, deadline, rng, iters=2500):
    """Annealed search over connection sets S of size d until cost 0 or deadline."""
    inv = np.argmax(M == 0, axis=1)
    while time.monotonic() < deadline:
        S = rng.sample(range(G), d)
        c = _bc_cost(M, inv, S, G, D)
        T = 2.0
        for _ in range(iters):
            if c == 0 or time.monotonic() >= deadline:
                break
            T = max(0.05, T * 0.998)
            i = rng.randrange(d)
            x = rng.randrange(G)
            if x in S:
                continue
            S2 = list(S)
            S2[i] = x
            c2 = _bc_cost(M, inv, S2, G, D)
            if c2 <= c or rng.random() < math.exp((c - c2) / T):
                S, c = S2, c2
        if c == 0:
            return S
    return None


def _bc_edges(M, S, G):
    E = []
    for x in range(G):
        for s in S:
            E.append((x, G + int(M[x, s])))
    return 2 * G, E


def _bicayley_search(d, D, g_start, deadline, rng, moore_half, consider, get_best_n):
    """Walk groups of ascending order from g_start; wrap around if the window passes the Moore range."""
    base = g_start
    g0 = g_start
    while time.monotonic() < deadline:
        for G, specs in _specs(g0, g0 + 7):
            if time.monotonic() >= deadline:
                return
            if G * 2 <= get_best_n():
                continue
            for spec in specs:
                if time.monotonic() >= deadline:
                    return
                try:
                    M = _make_table(spec)
                except Exception:
                    continue
                if M.shape[0] != G or not _identity_ok(M):
                    continue
                sub = min(deadline, time.monotonic() + 1.2)
                S = _search_group(M, G, d, D, sub, rng)
                if S is not None:
                    n, e = _bc_edges(M, S, G)
                    consider(n, e)
                    break
        g0 = max(g0 + 8, get_best_n() // 2 + 1)
        if g0 > moore_half:
            g0 = base


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
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
            return True
        return False

    # D = 3: incidence graph of PG(2, d-1) when d-1 is a prime power (Heawood for d = 3).
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        try:
            n3, e3 = lib.projective_plane_incidence(d - 1)
            consider(n3, e3)
        except Exception:
            pass

    # D >= 4: bi-Cayley graphs over a broad family of groups.
    if D >= 4 and d >= 3:
        moore_half = lib.moore_bound(d, D) // 2
        g_start = max(2 * d, best_n // 2 + 1, int(0.4 * moore_half))
        fam_rng = random.Random(seed * 1000003 + d * 131 + D)
        _bicayley_search(d, D, g_start, deadline, fam_rng, moore_half,
                         consider, lambda: best_n)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
