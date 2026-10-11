import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline constructions (safe, always valid for D >= 3).
# ----------------------------------------------------------------------------

def _araujo(d):
    """Araujo-Pardo & Lopez record graph (degree d) when q = d-2 is a prime power >= 3."""
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except (ValueError, AssertionError):
        return None


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New family: group Haar graphs (bi-Cayley over non-abelian groups).
#
# Take a finite group G of order N and a set S of d elements containing the
# identity. Vertices a_g and b_g (g in G); edges a_g -- b_{g s} for s in S.
# This is d-regular and bipartite with 2N vertices. Left multiplication by G
# is transitive on each side, so diameter <= 3 reduces to two conditions:
#     S S^{-1} = G   (A-side pairs within distance 2)
#     S^{-1} S = G   (B-side pairs within distance 2)
# (A-B pairs are then within distance 3 automatically.)
# So we search for S with both product sets covering G, maximizing N.
# Groups are semidirect products Z_m x| Z_k (r^k = 1 mod m), which includes
# cyclic and direct-product groups. The identity can be assumed in S.
# ----------------------------------------------------------------------------

def _semidirect_candidates(N):
    """All (m, k, r) with m*k = N giving a valid semidirect product Z_m x| Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        if k == 1:
            out.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(m, k, r):
    """Multiplication and inverse tables of the group Z_m x| Z_k."""
    order, mul, inv = lib.semidirect_group(m, k, r)
    mt = [[mul(x, y) for y in range(order)] for x in range(order)]
    il = [inv(x) for x in range(order)]
    return order, mt, il


def _cost(S, mt, il):
    """Number of uncovered elements of S S^{-1} plus those of S^{-1} S. Zero means valid."""
    N = len(mt)
    A = {mt[s][il[t]] for s in S for t in S}
    B = {mt[il[t]][s] for s in S for t in S}
    return 2 * N - len(A) - len(B)


def _sa(d, mt, il, rng, deadline, iters):
    """Simulated annealing over S (|S| = d, identity fixed in S) minimizing the coverage cost."""
    N = len(mt)
    if d > N or d < 2:
        return None
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _cost(S, mt, il)
    T0, T_end = 1.5, 0.1
    for it in range(iters):
        if cur == 0:
            break
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        x = rng.randrange(1, N)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        c2 = _cost(S, mt, il)
        delta = c2 - cur
        T = T0 * (T_end / T0) ** (it / max(1, iters))
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c2
        else:
            S[i] = old
    return S if cur == 0 else None


def _try_order(N, d, rng, deadline):
    """Try to find a valid S for groups of order N. Returns (n, edges) or None."""
    cands = _semidirect_candidates(N)
    if not cands:
        return None
    rng.shuffle(cands)
    for (m, k, r) in cands[:6]:
        if time.monotonic() > deadline:
            break
        order, mt, il = _tables(m, k, r)
        S = _sa(d, mt, il, rng, deadline, 3000)
        if S is not None:
            edges = [(g, order + mt[g][s]) for g in range(order) for s in S]
            return 2 * order, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    if D >= 3:
        rec = _araujo(d)
        if rec is not None:
            consider(rec[0], rec[1])

        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search (D >= 3): group Haar graphs with diameter <= 3, which are
    # valid for any D >= 3. Sweep orders downward from the covering bound;
    # each success raises the bar for later orders.
    if D >= 3 and d >= 2:
        hi = d * (d - 1) + 1
        slice_len = max(0.5, 0.01 * time_limit)
        while time.monotonic() < deadline:
            if best_n // 2 + 1 > hi:
                break
            for N in range(hi, max(2, best_n // 2 + 1) - 1, -1):
                if time.monotonic() >= deadline:
                    break
                if N <= best_n // 2:
                    break
                slice_end = min(deadline, time.monotonic() + slice_len)
                res = _try_order(N, d, rng, slice_end)
                if res is not None:
                    consider(res[0], res[1])
                    break  # restart the sweep with the new, higher bar

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
