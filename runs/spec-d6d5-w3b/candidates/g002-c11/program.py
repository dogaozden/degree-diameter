import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Known algebraic families, used for small D (D >= 3 only, all have diameter 3).
# ----------------------------------------------------------------------------

def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo_candidate(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# NEW MAIN FAMILY: bi-Cayley graphs over small non-abelian groups.
#
# Group G (order m), connection set S of d distinct elements.
# Vertices A_g = g and B_h = m + h. Edge A_g -- B_{g s} for each s in S.
# Left multiplication by any group element is an automorphism that acts
# transitively on the A side and on the B side. So the diameter is at most D
# iff BFS from A_1 and from B_1 both reach everything within D steps.
# The search is a hill-climb over S, scored by the number of unreached vertices.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k of order G, returned as (order, mul, inv)."""
    for _ in range(60):
        k = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        if k == 1:
            r = 1
            try:
                order, mul, inv = lib.semidirect_group(m, 1, r)
            except ValueError:
                continue
            return order, mul, inv
        for _ in range(200):
            r = rng.randrange(1, m)
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                try:
                    order, mul, inv = lib.semidirect_group(m, k, r)
                except ValueError:
                    break
                return order, mul, inv
    return None


def _attempt(G, mul, inv, d, D, rng, deadline, iters):
    """Hill-climb a d-element connection set S in the group. Returns (n, edges) if valid, else None."""
    if G < d:
        return None
    cache = {}

    def perm(s):
        p = cache.get(s)
        if p is None:
            p = [mul(x, s) for x in range(G)]
            cache[s] = p
        return p

    def cost_of(S):
        P = [perm(s) for s in S]
        Q = [perm(inv(s)) for s in S]
        N = 2 * G
        nbr = [None] * N
        for g in range(G):
            nbr[g] = [G + p[g] for p in P]
        for h in range(G):
            nbr[G + h] = [q[h] for q in Q]
        total = 0
        for src in (0, G):
            seen = bytearray(N)
            seen[src] = 1
            frontier = [src]
            cnt = 1
            for _ in range(D):
                nxt = []
                for u in frontier:
                    for v in nbr[u]:
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                if not nxt:
                    break
                cnt += len(nxt)
                frontier = nxt
            total += N - cnt
        return total, P

    S = rng.sample(range(G), d)
    c, P = cost_of(S)
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        T = S[:]
        T[i] = x
        ct, PT = cost_of(T)
        if ct <= c or rng.random() < 0.03:
            S, c, P = T, ct, PT
    if c != 0:
        return None
    edges = [(g, G + p[g]) for p in P for g in range(G)]
    return 2 * G, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo_candidate(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Main search: bi-Cayley graphs over small semidirect products.
    # Target a group order G so that 2G beats the current best.
    while time.monotonic() < deadline:
        lo = max(best_n // 2 + 1, d)
        span = max(2, lo // 30)
        G = rng.randint(lo, lo + span)
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul, inv = g
        res = _attempt(order, mul, inv, d, D, rng, deadline, 400)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
