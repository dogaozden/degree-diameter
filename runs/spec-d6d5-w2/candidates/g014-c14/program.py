import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Family 1: projective plane incidence graph (diameter 3, valid for any D >= 3).
# ----------------------------------------------------------------------------

def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Family 2: bi-Cayley graphs over finite groups (new search strategy).
#
# Vertices A_x = x and B_y = N + y, with x, y in the group G of order N.
# Edge A_x ~ B_{x*s} for s in S, |S| = d.
#
# Left multiplication by g is an automorphism (A_x -> A_{gx}, B_y -> B_{gy}),
# so the diameter equals max(ecc(A_0), ecc(B_0)). Right translation S -> S*g
# gives an isomorphic graph, so we may assume the identity lies in S.
#
# Search: randomized greedy construction of S (cost is monotone in S, so each
# step adds the element that most reduces unreached pairs), followed by a
# plateau-walk local search that swaps one non-identity element at a time.
# ----------------------------------------------------------------------------

def _semidirect_table(m, k, r):
    """Multiplication table of Z_m x| Z_k with (a,b)*(c,e) = (a + r^b c, b + e), coded a*k+b."""
    N = m * k
    x = np.arange(N, dtype=np.int64)
    a = x // k
    b = x % k
    powr = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    A = a[:, None]
    B = b[:, None]
    C = a[None, :]
    E = b[None, :]
    return ((A + powr[B] * C) % m) * k + (B + E) % k


def _mult_order(r, m):
    t, x = 1, r % m
    while x != 1:
        x = (x * r) % m
        t += 1
    return t


def _group_specs(lo, hi, per_order=3):
    """Semidirect product specs (N, m, k, r) for orders N in [lo, hi].

    Faithful actions (order of r equals k) are preferred; at most one spec per (m, k)
    and at most per_order specs per order.
    """
    specs = []
    for N in range(max(lo, 4), hi + 1):
        cands = []
        for m in range(3, N):
            if N % m:
                continue
            k = N // m
            if k < 2:
                continue
            for r in range(2, m):
                if math.gcd(r, m) != 1 or pow(r, k, m) != 1:
                    continue
                faithful = _mult_order(r, m) == k
                cands.append((0 if faithful else 1, m, k, r))
        cands.sort()
        seen = set()
        chosen = 0
        for _, m, k, r in cands:
            if (m, k) in seen:
                continue
            seen.add((m, k))
            specs.append((N, m, k, r))
            chosen += 1
            if chosen >= per_order:
                break
    return specs


def _make_group(spec):
    N, m, k, r = spec
    M = _semidirect_table(m, k, r)
    inv = np.argmax(M == 0, axis=1)
    return N, M, inv


def _cost(M, inv, N, S, D):
    """Unreached (vertex, source) pairs from A_0 and B_0 within D steps. Zero means valid."""
    Sa = np.asarray(S, dtype=np.int64)
    adj = np.vstack([M[:, Sa] + N, M[:, inv[Sa]]])
    total = 0
    for src in (0, N):
        seen = np.zeros(2 * N, dtype=bool)
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
        total += 2 * N - int(np.count_nonzero(seen))
    return total


def _search(M, inv, N, d, D, deadline, rng):
    """Greedy construction plus plateau-walk local search. Returns S (|S| = d) with cost 0, or None."""
    if N <= d:
        return None
    while time.monotonic() < deadline:
        S = [0]
        while len(S) < d:
            if time.monotonic() >= deadline:
                return None
            pool = [x for x in range(1, N) if x not in S]
            if len(pool) > 80:
                pool = rng.sample(pool, 80)
            costs = [_cost(M, inv, N, S + [x], D) for x in pool]
            mn = min(costs)
            ties = [x for x, c in zip(pool, costs) if c == mn]
            S.append(rng.choice(ties))
        c = _cost(M, inv, N, S, D)
        cb, stall = c, 0
        while c > 0 and stall < 1500 and time.monotonic() < deadline:
            i = rng.randrange(1, d)
            x = rng.randrange(1, N)
            if x in S:
                stall += 1
                continue
            S2 = list(S)
            S2[i] = x
            c2 = _cost(M, inv, N, S2, D)
            if c2 <= c or rng.random() < 0.02:
                S, c = S2, c2
            if c < cb:
                cb, stall = c, 0
            else:
                stall += 1
        if c == 0:
            return S
    return None


def _bicayley_phase(d, D, lo, hi, deadline, rng, consider, best):
    """Sweep candidate groups in ascending order with doubling budgets per pass."""
    specs = _group_specs(lo, hi)
    budget = 0.6
    while time.monotonic() < deadline and any(2 * s[0] > best[0] for s in specs):
        for spec in specs:
            now = time.monotonic()
            if now >= deadline:
                return
            if 2 * spec[0] <= best[0]:
                continue
            N, M, inv = _make_group(spec)
            S = _search(M, inv, N, d, D, min(deadline, now + budget), rng)
            if S is not None:
                edges = [(x, N + int(M[x, s])) for x in range(N) for s in S]
                consider(2 * N, edges)
        budget *= 2


# ----------------------------------------------------------------------------
# Main build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.85 * time_limit, time_limit - 4.0)
    deadline = start + max(0.5, budget)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = list(lib.haar_graph(d, range(d)))

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e
            return True
        return False

    if D >= 3:
        try:
            pg = _pg_candidate(d)
            if pg is not None:
                consider(pg[0], pg[1])
        except Exception:
            pass

    if D >= 3 and d >= 3:
        try:
            rng = random.Random(seed * 1000003 + d * 131 + D)
            mh = max(1, lib.moore_bound(d, D) // 2)
            lo = max(d, int(0.4 * mh))
            hi = max(lo, int(0.6 * mh))
            _bicayley_phase(d, D, lo, hi, deadline, rng, consider, best)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = list(lib.haar_graph(d, range(d)))
    return best[0], best[1]
