import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Direct search over unions of d permutations (d-regular bipartite multigraphs).
#
# Side A = {0..k-1}, side B = {k..2k-1}. Permutation t gives edges (i, k + p_t[i]).
# Each vertex gets degree d, minus any duplicate edges, so degree <= d always.
# Cost = (ordered pairs at distance > D) + 4 * (duplicate edges).
# Moves swap two images inside one permutation, which keeps it a permutation.
# Growth: when a size k succeeds, extend every permutation by one new A/B pair
# and anneal again from that warm start.
# ----------------------------------------------------------------------------

def _pair_cost(k, D, perms):
    """Return (bad ordered pairs beyond distance D, duplicate edge count)."""
    n = 2 * k
    adj = [[] for _ in range(n)]
    seen = set()
    dups = 0
    for p in perms:
        for i in range(k):
            j = p[i]
            key = i * k + j
            if key in seen:
                dups += 1
            else:
                seen.add(key)
            adj[i].append(k + j)
            adj[k + j].append(i)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        reach = new
    bad = n * n - sum(r.bit_count() for r in reach)
    return bad, dups


def _edges(k, perms):
    E = set()
    for p in perms:
        for i in range(k):
            E.add((i, k + p[i]))
    return 2 * k, sorted(E)


def _extend(p, old_k, rng):
    """Extend a permutation of range(old_k) to range(old_k + 1) by inserting the new pair."""
    i = rng.randrange(old_k)
    q = p[:] + [0]
    q[i] = old_k
    q[old_k] = p[i]
    return q


def _anneal(k, D, base, rng, t_end):
    """Simulated annealing on the permutations, starting from copies of base.

    Returns a list of permutations with zero bad pairs, or None at t_end.
    """
    perms = [p[:] for p in base]
    d = len(perms)
    bad, dups = _pair_cost(k, D, perms)
    if bad == 0:
        return perms
    cost = bad + 4 * dups
    t_start = time.monotonic()
    span = max(1e-6, t_end - t_start)
    T0, T1 = 3.0, 0.15
    T = T0
    it = 0
    while True:
        if (it & 7) == 0:
            now = time.monotonic()
            if now >= t_end:
                return None
            frac = (now - t_start) / span
            T = T0 * (T1 / T0) ** frac
        it += 1
        t = rng.randrange(d)
        i, j = rng.sample(range(k), 2)
        p = perms[t]
        p[i], p[j] = p[j], p[i]
        b2, d2 = _pair_cost(k, D, perms)
        c2 = b2 + 4 * d2
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            if b2 == 0:
                return perms
        else:
            p[i], p[j] = p[j], p[i]


def _search(d, D, deadline, rng, consider):
    """Grow k from d while annealing succeeds; retry from the last success on failure."""
    k = d
    base = [rng.sample(range(k), k) for _ in range(d)]
    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0.05:
            break
        length = min(remaining, max(2.0, 0.3 * remaining))
        res = _anneal(k, D, base, rng, now + length)
        if res is not None:
            n, e = _edges(k, res)
            consider(n, e)
            k += 1
            base = [_extend(p, k - 1, rng) for p in res]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.3, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact projective-plane construction for D = 3 (optimal when d-1 is a prime power).
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n, e = lib.projective_plane_incidence(q)
                consider(n, e)
                break

    # Stop early if the Moore bound is already reached.
    if best[0] >= lib._moore_bound(d, D):
        return best

    if time.monotonic() < deadline:
        _search(d, D, deadline, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
