import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New routine 1: bitmask bad-pair counter on an arbitrary graph given as
# neighbour lists over global vertex ids 0..N-1.
# ----------------------------------------------------------------------------

def _bad_pairs(N, nb, D):
    """Number of unordered pairs at distance > D (unreachable pairs included)."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            x = reach[v]
            for u in nb[v]:
                x |= reach[u]
            new.append(x)
        if new == reach:
            break
        reach = new
    return sum(N - r.bit_count() for r in reach) // 2


# ----------------------------------------------------------------------------
# New routine 2: switch annealing on d-regular bipartite graphs with equal
# sides. A switch replaces edges (a,b),(c,e) by (a,e),(c,b), which keeps every
# degree and the bipartition. The cost is the number of bad pairs, and we
# anneal toward cost 0 under a time-scaled geometric temperature schedule.
# ----------------------------------------------------------------------------

def _rep(lst, old, new):
    lst[lst.index(old)] = new


def _anneal(m, d, D, E0, rng, deadline, T0=2.0, T1=0.15):
    """E0: local edges (l, r) with l, r in 0..m-1, d-regular. Returns local edges or None."""
    N = 2 * m
    nb = [[] for _ in range(N)]
    S = set()
    W = []
    for l, r in E0:
        R = m + r
        nb[l].append(R)
        nb[R].append(l)
        S.add(l * N + R)
        W.append([l, R])
    cost = _bad_pairs(N, nb, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    M = len(W)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        i = rng.randrange(M)
        j = rng.randrange(M)
        a, b = W[i]
        c, e = W[j]
        if a == c or b == e:
            continue
        k1 = a * N + e
        k2 = c * N + b
        if k1 in S or k2 in S:
            continue
        _rep(nb[a], b, e)
        _rep(nb[c], e, b)
        _rep(nb[b], a, c)
        _rep(nb[e], c, a)
        new = _bad_pairs(N, nb, D)
        dl = new - cost
        if dl <= 0 or rng.random() < math.exp(-dl / T):
            cost = new
            S.discard(a * N + b)
            S.discard(c * N + e)
            S.add(k1)
            S.add(k2)
            W[i] = [a, e]
            W[j] = [c, b]
        else:
            _rep(nb[a], e, b)
            _rep(nb[c], b, e)
            _rep(nb[b], c, a)
            _rep(nb[e], a, c)
    return [(a, R - m) for a, R in W]


# ----------------------------------------------------------------------------
# New routine 3: matching-split pair insertion. From a d-regular bipartite
# graph on m+m vertices, pick a matching of d edges (l_k, r_k). Remove them,
# add a new left vertex joined to all r_k and a new right vertex joined to all
# l_k. The result is d-regular on (m+1)+(m+1) vertices, so the anneal can warm
# start from a valid graph one size up.
# ----------------------------------------------------------------------------

def _insert_pair(m, E, d, rng):
    idx = list(range(len(E)))
    rng.shuffle(idx)
    chosen = []
    usedL, usedR = set(), set()
    for t in idx:
        l, r = E[t]
        if l in usedL or r in usedR:
            continue
        chosen.append(t)
        usedL.add(l)
        usedR.add(r)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    ch = set(chosen)
    newE = [E[t] for t in range(len(E)) if t not in ch]
    for t in chosen:
        l, r = E[t]
        newE.append((m, r))
        newE.append((l, m))
    return m + 1, newE


def _haar_start(m, d, rng):
    """Random Haar-type d-regular bipartite start (requires m >= d)."""
    shifts = rng.sample(range(m), d)
    return [(i, (i + s) % m) for i in range(m) for s in shifts]


def _pg_local(q):
    """PG(2,q) incidence as a local (m, E) pair."""
    n, e = lib.projective_plane_incidence(q)
    m = n // 2
    return m, [(u, v - m) for u, v in e]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and is optimal for D = 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, best_e

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    # Warm-start chain state: (m, local regular edges) of the last success.
    cur = None
    if D >= 3:
        q = d - 1
        if q >= 2 and lib.is_prime_power(q):
            pg_m, pg_E = _pg_local(q)
            consider(2 * pg_m, [(l, pg_m + r) for l, r in pg_E])
            cur = (pg_m, pg_E)

    fails = 0
    while time.monotonic() < deadline and fails < 6:
        remaining = deadline - time.monotonic()
        if cur is None:
            m_t = d + 1
            E0 = _haar_start(m_t, d, rng)
        else:
            pm, pE = cur
            res = _insert_pair(pm, pE, d, rng) if fails < 2 else None
            if res is None:
                m_t = pm + 1
                E0 = _haar_start(m_t, d, rng)
            else:
                m_t, E0 = res

        budget = min(remaining, max(4.0, remaining / 3.0))
        sub_deadline = min(deadline, time.monotonic() + budget)
        res = _anneal(m_t, d, D, E0, rng, sub_deadline)
        if res is None:
            fails += 1
            continue
        fails = 0
        cur = (m_t, res)
        consider(2 * m_t, [(l, m_t + r) for l, r in res])

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
