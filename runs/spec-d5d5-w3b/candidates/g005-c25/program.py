import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Different construction from the parent: unstructured random d-regular
# bipartite graphs, repaired by simulated annealing over double edge switches.
# The cost is the number of ordered vertex pairs at distance > D (zero means valid).
# Bisection on the side size N finds the largest N this search can reach.
# ----------------------------------------------------------------------------

def _bad_pairs_ordered(n, adj, D):
    """Ordered pairs (v, w) with dist(v, w) > D, counted via bitmask balls. Zero iff diameter <= D."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return sum(n - b.bit_count() for b in ball)


def _random_regular_bip(N, d, rng, tries=20000):
    """Random simple d-regular bipartite graph with sides 0..N-1 (A) and 0..N-1 (B) by pairing."""
    base = [a for a in range(N) for _ in range(d)]
    for _ in range(tries):
        B = base[:]
        rng.shuffle(B)
        pairs = set(zip(base, B))
        if len(pairs) == len(base):
            return list(pairs)
    return None


def _anneal(N, d, D, rng, deadline, E0):
    """Edge-switch annealing. Each move swaps (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), keeping degrees."""
    E = list(E0)
    S = set(E)
    n = 2 * N
    m = len(E)

    def adjacency():
        adj = [[] for _ in range(n)]
        for a, b in E:
            adj[a].append(N + b)
            adj[N + b].append(a)
        return adj

    cur = _bad_pairs_ordered(n, adjacency(), D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T_hot, T_cold = 3.0, 0.3

    while cur > 0 and time.monotonic() < deadline:
        frac = min(1.0, (time.monotonic() - t0) / span)
        T = T_hot * (T_cold / T_hot) ** frac
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        e1 = (a1, b2)
        e2 = (a2, b1)
        if e1 in S or e2 in S:
            continue
        E[i] = e1
        E[j] = e2
        S.discard((a1, b1))
        S.discard((a2, b2))
        S.add(e1)
        S.add(e2)
        new = _bad_pairs_ordered(n, adjacency(), D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            S.discard(e1)
            S.discard(e2)
            S.add((a1, b1))
            S.add((a2, b2))

    return E if cur == 0 else None


def _attempt(N, d, D, rng, deadline):
    E0 = _random_regular_bip(N, d, rng)
    if E0 is None:
        return None
    return _anneal(N, d, D, rng, deadline, E0)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Safe fallback: K_{d,d}, diameter 2.
    consider(*lib.haar_graph(d, range(d)))
    if D == 2:
        return best

    if D == 3:
        if d >= 3 and lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
            return best
        # Largest prime power q with q + 1 <= d - 1: incidence graph of PG(2, q).
        for q in range(d - 2, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break

    moore = lib.moore_bound(d, D)
    Nmax = moore // 2
    if Nmax <= d:
        return best

    rng = random.Random(seed * 1000003 + d * 101 + D)

    try:
        lo = d          # largest N known to succeed (K_{d,d})
        fail_hi = None  # smallest N known to fail
        slice_len = max(1.0, 0.3 * budget)
        while time.monotonic() < deadline - 0.2:
            if fail_hi is None:
                if lo >= Nmax:
                    break
                N = min(Nmax, max(lo + 1, 2 * lo))
            else:
                N = (lo + fail_hi) // 2
                if N <= lo:
                    break
            now = time.monotonic()
            slice_end = now + min(deadline - now, slice_len)
            try:
                E = _attempt(N, d, D, rng, slice_end)
            except Exception:
                E = None
            if E is not None:
                lo = N
                consider(2 * N, [(a, N + b) for a, b in E])
            else:
                fail_hi = N
    except Exception:
        pass  # keep the best valid graph found so far

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
