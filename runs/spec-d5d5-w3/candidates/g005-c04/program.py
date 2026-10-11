import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: bi-Cayley lifts over a MIXED pool of groups.
#
# A bi-Cayley graph over a group G with connection set S (|S| = d, identity
# in S WLOG) has parts A_x and B_x for x in G, with A_x adjacent to B_{x s}
# for s in S. Left translation is an automorphism, so the diameter is at most
# D iff every vertex lies within D of A_0 and of B_0.
#
# Previous versions used only semidirect products Z_m x| Z_k. Here we also
# sample 2-generated permutation groups (random subgroups of S_7, S_8, S_9)
# whose orders fall in the target band. Those are non-metacyclic groups such
# as PSL(2,7) or PGL(2,7), which the semidirect family cannot reach.
#
# Search: simulated annealing over S with cost = number of (source, vertex)
# pairs beyond distance D. Every produced graph is checked by lib.is_valid
# before it is accepted, and K_{d,d} is kept as the fallback.
# ----------------------------------------------------------------------------

_SA_ITERS = 500
_GROUPS_PER_ORDER = 3
_POOL_PER_ORDER = 2


# ---------------------------------------------------------------- groups

def _semidirect_params(N):
    """All (m, k, r) with m*k = N giving valid semidirect products Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _semidirect_tuple(m, k, r):
    """Group as (order, mul, invs) from a semidirect parameter triple."""
    order, mul, inv = lib.semidirect_group(m, k, r)
    invs = [inv(g) for g in range(order)]
    return order, mul, invs


def _perm_closure(gens, n, hi):
    """Closure of permutation generators, aborted (None) if the group exceeds hi elements."""
    ident = tuple(range(n))
    elems = [ident]
    idx = {ident: 0}
    i = 0
    while i < len(elems):
        x = elems[i]
        i += 1
        for g in gens:
            y = tuple(x[t] for t in g)  # x composed with g
            if y not in idx:
                if len(elems) >= hi:
                    return None
                idx[y] = len(elems)
                elems.append(y)
    return elems, idx


def _perm_group_tuple(elems, idx):
    """Group as (order, mul, invs) from a closed permutation group."""
    N = len(elems)
    n = len(elems[0])

    def mul(i, j):
        a = elems[i]
        b = elems[j]
        return idx[tuple(a[t] for t in b)]

    invs = []
    for a in elems:
        r = [0] * n
        for t, at in enumerate(a):
            r[at] = t
        invs.append(idx[tuple(r)])
    return N, mul, invs


def _rand_perm(n, rng):
    """Random permutation, or with some probability a random involution."""
    if rng.random() < 0.3:
        p = list(range(n))
        rng.shuffle(p)
        out = list(range(n))
        for j in range(0, n - 1, 2):
            if rng.random() < 0.7:
                a, b = p[j], p[j + 1]
                out[a], out[b] = b, a
        return tuple(out)
    p = list(range(n))
    rng.shuffle(p)
    return tuple(p)


def _gather_perm_groups(lo, hi, deadline, rng):
    """Sample 2-generated permutation groups with order in [lo, hi]; keep a few per order."""
    pool = {}
    while time.monotonic() < deadline:
        n = rng.choice((7, 8, 9))
        k = rng.choice((2, 2, 3))
        gens = [_rand_perm(n, rng) for _ in range(k)]
        r = _perm_closure(gens, n, hi)
        if r is None:
            continue
        N = len(r[0])
        if N < lo or len(pool.get(N, [])) >= _POOL_PER_ORDER:
            continue
        pool.setdefault(N, []).append(_perm_group_tuple(r[0], r[1]))
    return pool


def _candidates(N, pool, rng):
    """Permutation groups of order N first, then a few semidirect products."""
    out = list(pool.get(N, []))
    params = _semidirect_params(N)
    rng.shuffle(params)
    for m, k, r in params[:_GROUPS_PER_ORDER]:
        out.append(_semidirect_tuple(m, k, r))
    return out[:_GROUPS_PER_ORDER]


# ---------------------------------------------------------------- bi-Cayley search

def _rperm(mul, N, s, cache):
    """Cached permutation g -> g*s of the group."""
    r = cache.get(s)
    if r is None:
        r = [mul(g, s) for g in range(N)]
        cache[s] = r
    return r


def _unreached(N, invs, S, D, cache, mul):
    """Number of (source, vertex) pairs not within distance D, sources A_0 and B_0."""
    fw = [_rperm(mul, N, s, cache) for s in S]
    bw = [_rperm(mul, N, invs[s], cache) for s in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    for r in fw:
                        v = N + r[u]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    for r in bw:
                        v = r[u - N]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _search_group(N, G, d, D, rng, iters, deadline):
    """Anneal a connection set S of size d (identity fixed) to zero unreached pairs."""
    if N < d:
        return None
    mul, invs, _ = G[1], G[2], G[0]
    cache = {}
    S = [0] + rng.sample(range(1, N), d - 1)
    inS = set(S)
    cur = _unreached(N, invs, S, D, cache, mul)
    it = 0
    while cur > 0 and it < iters and time.monotonic() < deadline:
        it += 1
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in inS:
            continue
        S2 = S[:]
        old = S2[i]
        S2[i] = c
        v = _unreached(N, invs, S2, D, cache, mul)
        T = 2.0 * (1.0 - it / iters) + 0.1
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            inS.discard(old)
            inS.add(c)
            S, cur = S2, v
    return S if cur == 0 else None


def _edges_of(N, G, S):
    """Edges of the bi-Cayley graph: A_x (vertex x) ~ B_{x s} (vertex N + x s)."""
    mul = G[1]
    E = []
    for x in range(N):
        for s in S:
            E.append((x, N + mul(x, s)))
    return 2 * N, E


# ---------------------------------------------------------------- main

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 4.0))
    deadline = t0 + budget

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and order 2d.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    rng = random.Random(seed * 1000003 + d * 97 + D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    half = moore // 2

    # Permutation-group pool for the band of interesting orders.
    pool = {}
    if moore > 60:
        lo = max(d, moore // 4 - 40)
        hi = min(half, 400)
        if hi >= lo:
            gather_deadline = t0 + min(0.15 * budget, 8.0)
            pool = _gather_perm_groups(lo, hi, gather_deadline, rng)

    # Sweep upward from the band where a record-beating order would lie.
    p = max(best[0] // 2 + 1, moore // 4)
    while best[0] < moore and time.monotonic() < deadline:
        if p > half:
            p = best[0] // 2 + 1
            if p > half:
                break
        N = p
        p += 1
        if N < d:
            continue
        for G in _candidates(N, pool, rng):
            if time.monotonic() >= deadline:
                break
            S = _search_group(N, G, d, D, rng, _SA_ITERS, deadline)
            if S is not None:
                n2, e2 = _edges_of(N, G, S)
                consider(n2, e2)
                break
        p = max(p, best[0] // 2 + 1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
