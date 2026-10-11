import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baselines: projective-plane incidence graph (Moore graph when d-1 is a
# prime power), the Araujo-Pardo/Lopez record family for d = q+2, and K_{d,d}.
# ----------------------------------------------------------------------------

def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _baseline(d, D):
    """Best known safe construction: K_{d,d}, upgraded by the record families when they apply."""
    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    if D < 3:
        return best
    try:
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            n_a, e_a = lib.araujo_lopez_graph(d - 2)
            if n_a > best[0] and lib.is_valid(n_a, e_a, d, D):
                best = (n_a, e_a)
    except Exception:
        pass
    try:
        pg = _pg_best(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg
    except Exception:
        pass
    return best


# ----------------------------------------------------------------------------
# New construction: multi-orbit voltage lifts over small non-abelian groups.
#
# Base graph: k vertices A_0..A_{k-1} and k vertices B_0..B_{k-1}, d "darts"
# t = 0..d-1. Dart t joins A_i to B_{sig[t][i]} with voltage volt[t][i] in G,
# where each sig[t] is a permutation (so every base vertex has exactly d darts).
# Lift: vertex (side, x) for x in G; A_i at x joins B_j at x * g.
# Every lifted vertex has degree <= d, the lift is bipartite, and left
# multiplication by G is an automorphism, so distances only need to be checked
# from one source per side (the identity fibre element).
#
# Search: simulated annealing over (sig, volt) minimising the number of
# (source, vertex) pairs at distance > D. Groups: cyclic Z_N and semidirect
# products Z_a x| Z_k, with N = (n / 2k) chosen just above the current best.
# ----------------------------------------------------------------------------

def _spec_list(N, rng):
    """Cyclic group first, then the semidirect products Z_a x| Z_k of order N (shuffled)."""
    rest = []
    for kk in range(2, N + 1):
        if N % kk:
            continue
        a = N // kk
        if a == 1:
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, kk, a) == 1 % a:
                rest.append(("sd", a, kk, r))
    rng.shuffle(rest)
    return [("cyc", N)] + rest[:40]


def _mul_table(spec, N):
    """Multiplication table M[x][y] = x*y for the group named by spec (identity is 0)."""
    if spec[0] == "cyc":
        _, mul, _ = lib.cyclic_group(N)
    else:
        _, a, kk, r = spec
        _, mul, _ = lib.semidirect_group(a, kk, r)
    return [[mul(x, y) for y in range(N)] for x in range(N)]


def _lift_edges(N, k, d, sig, volt, M):
    """Edge set of the lift; A_i at x -> id i*N+x, B_j at y -> id (k+j)*N+y. All edges have A-id < B-id."""
    edges = set()
    for t in range(d):
        st = sig[t]
        vt = volt[t]
        for i in range(k):
            j = k + st[i]
            g = vt[i]
            for x in range(N):
                edges.add((i * N + x, j * N + M[x][g]))
    return edges


def _bad_count(n, N, k, d, sig, volt, M, D):
    """Number of (source, vertex) pairs at distance > D, over one source per side (identity fibre)."""
    edges = _lift_edges(N, k, d, sig, volt, M)
    adj = [[] for _ in range(n)]
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    total = 0
    for s in range(2 * k):
        src = s * N
        seen = {src}
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if v not in seen:
                        seen.add(v)
                        nxt.append(v)
            if not nxt:
                break
            frontier = nxt
        total += n - len(seen)
    return total


def _anneal(N, k, d, M, D, rng, deadline, steps):
    """Anneal (sig, volt) to zero bad pairs. Returns (sig, volt) or None."""
    n = 2 * k * N
    sig = [rng.sample(range(k), k) for _ in range(d)]
    volt = [[rng.randrange(N) for _ in range(k)] for _ in range(d)]
    cur = _bad_count(n, N, k, d, sig, volt, M, D)
    for it in range(steps):
        if cur == 0:
            return sig, volt
        if (it & 31) == 0 and time.monotonic() >= deadline:
            return None
        T = max(0.1, 2.0 * (0.05 ** (it / steps)))
        t = rng.randrange(d)
        if k >= 2 and rng.random() < 0.3:
            a, b = rng.sample(range(k), 2)
            st = sig[t]
            st[a], st[b] = st[b], st[a]
            new = _bad_count(n, N, k, d, sig, volt, M, D)
            delta = new - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = new
            else:
                st[a], st[b] = st[b], st[a]
        else:
            i = rng.randrange(k)
            old = volt[t][i]
            volt[t][i] = rng.randrange(N)
            new = _bad_count(n, N, k, d, sig, volt, M, D)
            delta = new - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = new
            else:
                volt[t][i] = old
    if cur == 0:
        return sig, volt
    return None


def _try_N(N, k, d, D, rng, deadline):
    """Try several groups of order N with annealing until the deadline. Returns (n, edges) or None."""
    specs = _spec_list(N, rng)
    cache = {}
    tries = 0
    while time.monotonic() < deadline:
        spec = specs[tries % len(specs)]
        tries += 1
        if spec not in cache:
            try:
                cache[spec] = _mul_table(spec, N)
            except Exception:
                cache[spec] = None
        M = cache[spec]
        if M is None:
            continue
        res = _anneal(N, k, d, M, D, rng, deadline, 2500)
        if res is not None:
            sig, volt = res
            n = 2 * k * N
            edges = list(_lift_edges(N, k, d, sig, volt, M))
            return n, edges
    return None


def _search(d, D, best, rng, deadline):
    """Repeatedly try to beat the current best with lifts over k = 3, 2, 4 base vertices per side."""
    moore = lib.moore_bound(d, D)
    for k in (3, 2, 4):
        while True:
            now = time.monotonic()
            if now >= deadline:
                return best
            N = best[0] // (2 * k) + 1
            if 2 * k * N > moore:
                break
            att_deadline = now + 0.5 * (deadline - now)
            res = _try_N(N, k, d, D, rng, att_deadline)
            if res is None:
                break
            n, e = res
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
            else:
                break
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(time_limit, 60.0) * 0.85 - 1.0)
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = _baseline(d, D)
    if D < 3 or d < 2:
        return best
    if best[0] >= lib.moore_bound(d, D):
        return best

    rng = random.Random(seed)
    try:
        cand = _search(d, D, best, rng, deadline)
        if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
