import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (always valid, used as fallbacks).
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


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite (d, D) graph."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


# ----------------------------------------------------------------------------
# New construction: Haar graphs over groups (bipartite Cayley graphs).
#
# Vertices a_g and b_g for g in a group G of order N. Connection set S of size d
# gives edges a_g -- b_{g s} for s in S. Left multiplication is an automorphism
# acting transitively on each side, so the diameter is <= D iff a BFS of depth D
# from a_e and from b_e reaches every vertex. The search is simulated annealing
# over the connection set S, with a time-based temperature.
# Groups are semidirect products Z_m x| Z_k (direct products when r = 1).
# ----------------------------------------------------------------------------

def _random_group(N, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k of order N, or None."""
    divs = [k for k in range(1, N + 1) if N % k == 0]
    rng.shuffle(divs)
    for k2 in divs[:12]:
        m = N // k2
        if m == 1:
            cands = [0]
        else:
            cands = [1]
            if k2 > 1:
                cands += [r for r in range(2, m)
                          if math.gcd(r, m) == 1 and pow(r, k2, m) == 1]
        r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        if order == N:
            return order, mul
    return None


def _unreached(N, S, get, D):
    """Number of (representative, vertex) pairs at distance > D; zero means diameter <= D."""
    perms = [get(s)[0] for s in S]
    invs = [get(s)[1] for s in S]
    total = 0
    for src in (0, N):  # a_e and b_e
        seen = bytearray(2 * N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    for p in perms:
                        v = N + p[u]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    x = u - N
                    for q in invs:
                        v = q[x]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _haar_search(d, D, N, rng, deadline):
    """Anneal a connection set of size d in a random group of order N. Return (S, get, N) or None."""
    got = _random_group(N, rng)
    if got is None:
        return None
    _, mul = got
    cache = {}

    def get(s):
        if s not in cache:
            if len(cache) > 6000:
                cache.clear()
            perm = [mul(g, s) for g in range(N)]
            inv = [0] * N
            for g, x in enumerate(perm):
                inv[x] = g
            cache[s] = (perm, inv)
        return cache[s]

    S = rng.sample(range(N), d)
    cost = _unreached(N, S, get, D)
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    T0 = 1.5
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - start) / span
        T = T0 * (1.0 - frac) + 0.05
        i = rng.randrange(d)
        new = rng.randrange(N)
        if new in S:
            continue
        S2 = S[:]
        S2[i] = new
        c2 = _unreached(N, S2, get, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            S, cost = S2, c2
    if cost == 0:
        return S, get, N
    return None


def _haar_edges(S, get, N):
    E = []
    for s in S:
        perm = get(s)[0]
        for g in range(N):
            E.append((g, N + perm[g]))
    return 2 * N, E


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    bound = _moore(d, D)
    if best_n >= bound:
        return best

    try:
        chunk_len = max(1.0, budget / 12.0)
        while time.monotonic() < deadline:
            # Target half-orders just above the current best (Haar graph has 2N vertices).
            N = best_n // 2 + 1 + rng.randrange(0, 12)
            N = max(N, d)
            now = time.monotonic()
            attempt_deadline = min(deadline, now + chunk_len)
            res = _haar_search(d, D, N, rng, attempt_deadline)
            if res is not None:
                S, get, NN = res
                n, E = _haar_edges(S, get, NN)
                if n > best_n and lib.is_valid(n, E, d, D):
                    best = (n, E)
                    best_n = n
                    if best_n >= bound:
                        break
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
