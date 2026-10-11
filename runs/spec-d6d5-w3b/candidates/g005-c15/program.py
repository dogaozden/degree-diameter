import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over a single finite group G of order N.
#
# Vertices are (0, g) and (1, g) for g in G, index g and N + g. The connection
# set S (d distinct elements) gives edges (0, g) -- (1, g*s) for s in S.
# Left multiplication by G is an automorphism, so the diameter is determined
# by BFS from the two identity vertices (0, e) and (1, e) alone.
# Cost = number of vertices unreached within D summed over those two sources.
# Cost 0 means diameter <= D. Groups are semidirect products Z_m x| Z_k
# (non-abelian when r != 1), or cyclic.
# ----------------------------------------------------------------------------

def _make_group(N, rng):
    """Return (order, mul, inv) for a random group of order N, identity coded as 0."""
    nontriv = [k for k in range(2, N + 1) if N % k == 0 and N // k >= 2]
    if nontriv and rng.random() < 0.85:
        k = rng.choice(nontriv)
        m = N // k
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if rs:
            r = rng.choice(rs)
            order, mul, inv = lib.semidirect_group(m, k, r)
            return order, mul, inv
    return N, (lambda x, y: (x + y) % N), (lambda x: (-x) % N)


def _tables(N, mul, inv, cache, s):
    """(fwd, bwd) for generator s: fwd[g] = g*s, bwd[h] = h*s^{-1}."""
    t = cache.get(s)
    if t is None:
        si = inv(s)
        fwd = [mul(g, s) for g in range(N)]
        bwd = [mul(h, si) for h in range(N)]
        t = (fwd, bwd)
        cache[s] = t
    return t


def _bad(N, D, tabs):
    """Number of vertices not within distance D of (0,e) or of (1,e), summed."""
    total = 0
    for side in (0, 1):
        src = side * N  # identity has index 0 in each side
        seen = bytearray(2 * N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    for fwd, _b in tabs:
                        v = N + fwd[u]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    h = u - N
                    for _f, bwd in tabs:
                        v = bwd[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += 2 * N - count
    return total


def _edges_from(N, tabs):
    E = []
    for g in range(N):
        for fwd, _b in tabs:
            E.append((g, N + fwd[g]))
    return E


def _search_N(N, D, d, rng, att_deadline, iters):
    """Try to find a valid bi-Cayley graph on 2N vertices before att_deadline. Returns (n, edges) or None."""
    if N < d:
        return None
    while time.monotonic() < att_deadline:
        order, mul, inv = _make_group(N, rng)
        cache = {}
        S = rng.sample(range(N), d)
        tabs = [_tables(N, mul, inv, cache, s) for s in S]
        cost = _bad(N, D, tabs)
        T = 1.5
        for it in range(iters):
            if cost == 0:
                break
            if (it & 15) == 0 and time.monotonic() >= att_deadline:
                break
            T = max(0.05, T * 0.997)
            i = rng.randrange(d)
            s_new = rng.randrange(N)
            if s_new in S:
                continue
            old = S[i]
            S[i] = s_new
            tabs_new = tabs[:]
            tabs_new[i] = _tables(N, mul, inv, cache, s_new)
            c2 = _bad(N, D, tabs_new)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
                tabs = tabs_new
            else:
                S[i] = old
        if cost == 0:
            return 2 * N, _edges_from(N, tabs)
    return None


# ----------------------------------------------------------------------------
# Small baseline families (kept as safe candidates).
# ----------------------------------------------------------------------------

def _pg_candidate(d):
    """Incidence graph of PG(2, q), q the largest prime power with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo_candidate(d):
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + total
    rng = random.Random(seed * 1000003 + d * 97 + D)

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 (valid for D >= 2).
    best_n = 2 * d
    best_e = [(i, d + j) for i in range(d) for j in range(d)]

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    if D >= 3 and d >= 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo_candidate(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Bi-Cayley search: bisect on the group order N (graph has 2N vertices).
    lo = 0          # largest N with a verified valid graph
    hi = None       # smallest N where the search failed
    N_try = max(d, 4)
    while time.monotonic() < deadline - 0.5:
        remaining = deadline - time.monotonic()
        att = min(remaining, max(2.0, 0.12 * total))
        att_deadline = time.monotonic() + att
        res = _search_N(N_try, D, d, rng, att_deadline, 1200)
        if res is not None:
            n2, e2 = res
            consider(n2, e2)
            if lib.is_valid(n2, e2, d, D):
                lo = max(lo, N_try)
        else:
            hi = N_try if hi is None else min(hi, N_try)

        if hi is None:
            N_next = lo + max(1, lo // 15)
        elif hi - lo > 1:
            N_next = (lo + hi) // 2
        else:
            N_next = lo + 1
        N_try = max(d, N_next)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n = 2 * d
        best_e = [(i, d + j) for i in range(d) for j in range(d)]
    return best_n, best_e
