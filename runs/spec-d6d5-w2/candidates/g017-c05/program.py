import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baselines: K_{d,d} fallback and the projective-plane incidence graph.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New family for the high-D targets: bi-Cayley graphs over a wider set of
# groups, including Heisenberg groups of order p^3 (non-abelian, not a
# semidirect product of cyclic groups), so that orders just above the
# current record (343 = 7^3 for d=6, D=5) become reachable.
#
# Vertices A_x = x and B_w = G + w. Connection set S (|S| = d, distinct).
# Edge A_x ~ B_{x*s} for x in G, s in S. Left multiplication is an
# automorphism, so the graph has diameter <= D iff BFS from A_1 and from B_1
# reaches all 2|G| vertices within D steps. Cost = unreached count; 0 = valid.
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


def _divisors(n):
    return [k for k in range(1, n + 1) if n % k == 0]


def _specs_for_order(G, rng, cap=8):
    """Group specs of order G: Heisenberg (if G = p^3) and semidirect Z_m x| Z_k."""
    out = []
    p = round(G ** (1.0 / 3.0))
    for q in (p - 1, p, p + 1):
        if q >= 3 and q ** 3 == G and _is_prime(q):
            out.append(("heis", q))
    for k in _divisors(G):
        m = G // k
        if m < 2:
            continue
        if k == 1:
            out.append(("sd", m, 1, 1))
            continue
        rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        picks = rng.sample(rs, min(len(rs), 2)) + [1]  # r = 1 gives Z_m x Z_k
        for r in picks:
            out.append(("sd", m, k, r))
    rng.shuffle(out)
    return out[:cap]


_CACHE = {}


def _get_group(spec):
    """Return (G, M, inv) with M the multiplication table, or None if spec is not a group."""
    if spec in _CACHE:
        return _CACHE[spec]
    if len(_CACHE) > 30:
        _CACHE.clear()
    if spec[0] == "heis":
        p = spec[1]
        G = p ** 3
        idx = np.arange(G, dtype=np.int64)
        a = idx // (p * p)
        b = (idx // p) % p
        c = idx % p
        A, B, C = a[:, None], b[:, None], c[:, None]
        A2, B2, C2 = a[None, :], b[None, :], c[None, :]
        M = ((A + A2) % p) * p * p + ((B + B2) % p) * p + (C + C2 + A * B2) % p
    else:
        _, m, k, r = spec
        G, mul, _ = lib.semidirect_group(m, k, r)
        M = np.empty((G, G), dtype=np.int64)
        for x in range(G):
            M[x, :] = [mul(x, y) for y in range(G)]
    M = M.astype(np.int64)
    ar = np.arange(G)
    if not (np.array_equal(M[0], ar) and np.array_equal(M[:, 0], ar)):
        res = None
    else:
        inv = np.argmax(M == 0, axis=1)
        res = (G, M, inv)
    _CACHE[spec] = res
    return res


def _bc_adj(M, inv, S, G):
    """Adjacency (2G, d): row x < G lists B-nodes G + M[x,s]; row G+w lists A-nodes M[w, s^-1]."""
    Sa = np.asarray(S, dtype=np.int64)
    return np.vstack([G + M[:, Sa], M[:, inv[Sa]]])


def _bc_cost(adj, G, D):
    """Unreached vertices from A_1 (node 0) and B_1 (node G) within D steps. Zero means valid."""
    N = adj.shape[0]
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


def _anneal_group(M, inv, G, d, D, deadline, rng, iters):
    """Annealed search over S (|S| = d) until cost 0, iteration cap, or deadline."""
    S = rng.sample(range(G), d)
    c = _bc_cost(_bc_adj(M, inv, S, G), G, D)
    T = 1.5
    for _ in range(iters):
        if c == 0 or time.monotonic() >= deadline:
            break
        T = max(0.05, T * 0.997)
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        T2 = list(S)
        T2[i] = x
        c2 = _bc_cost(_bc_adj(M, inv, T2, G), G, D)
        if c2 <= c or rng.random() < math.exp((c - c2) / T):
            S, c = T2, c2
    return S if c == 0 else None


def _bc_edges(M, S, G):
    E = []
    for x in range(G):
        for s in S:
            E.append((x, G + int(M[x, s])))
    return 2 * G, E


def _group_phase(d, D, lo, deadline, rng, consider):
    """Round-robin over group orders starting at lo, with growing per-group budgets."""
    budget = 0.4
    found_top = lo - 1
    while time.monotonic() < deadline:
        start_g = max(lo, found_top + 1)
        for G in range(start_g, start_g + 60):
            if time.monotonic() >= deadline:
                return
            for spec in _specs_for_order(G, rng):
                if time.monotonic() >= deadline:
                    return
                try:
                    grp = _get_group(spec)
                except Exception:
                    grp = None
                if grp is None or grp[0] != G:
                    continue
                _, M, inv = grp
                sub = min(deadline, time.monotonic() + budget)
                S = _anneal_group(M, inv, G, d, D, sub, rng, 3000)
                if S is not None:
                    n, e = _bc_edges(M, S, G)
                    consider(n, e)
                    found_top = max(found_top, G)
                    break
        budget = min(budget * 2.0, 6.0)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    moore = lib.moore_bound(d, D)
    if best_n >= moore:
        return best

    if D >= 3 and d >= 3:
        moore_half = moore // 2
        lo = max(2 * d, int(0.44 * moore_half), best_n // 2 + 1)
        _group_phase(d, D, lo, deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
