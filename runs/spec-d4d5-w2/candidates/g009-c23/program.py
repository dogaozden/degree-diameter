import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: no algebra. Search directly over bipartite d-regular graphs with
# N vertices per side, using degree-preserving double edge switches and simulated
# annealing on the number of vertex pairs at distance > D. The cost is computed
# with bitset ball expansion, so every step is an exact check.
#
# Safe fallbacks: K_{d,d} (always valid for D >= 2) and PG(2, d-1) incidence
# when d-1 is a prime power (diameter 3). Every returned graph passes lib.is_valid.
# ----------------------------------------------------------------------------


def _rep(lst, old, new):
    """Replace one occurrence of old by new in lst."""
    lst[lst.index(old)] = new


def _sw(adj, S, a1, c1, a2, c2):
    """Double edge switch: (a1,c1),(a2,c2) -> (a1,c2),(a2,c1). Self-inverse with args (a1,c2,a2,c1)."""
    _rep(adj[a1], c1, c2)
    _rep(adj[a2], c2, c1)
    _rep(adj[c1], a1, a2)
    _rep(adj[c2], a2, a1)
    S.discard((a1, c1))
    S.discard((a2, c2))
    S.add((a1, c2))
    S.add((a2, c1))


def _ball_cost(adj, V, D):
    """Number of ordered vertex pairs at distance > D. Zero means diameter <= D (and connected)."""
    reach = [1 << v for v in range(V)]
    for _ in range(D):
        new = []
        for v in range(V):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(V - r.bit_count() for r in reach)


def _random_regular_bip(N, d, rng):
    """Random simple d-regular bipartite graph on sides 0..N-1 and N..2N-1, as a set of (a, N+b)."""
    for _ in range(300):
        S = set()
        ok = True
        for _r in range(d):
            done = False
            for _t in range(500):
                p = list(range(N))
                rng.shuffle(p)
                if all((i, N + p[i]) not in S for i in range(N)):
                    for i in range(N):
                        S.add((i, N + p[i]))
                    done = True
                    break
            if not done:
                ok = False
                break
        if ok:
            return S
    return None


def _anneal(N, d, D, rng, t_end):
    """Anneal a d-regular bipartite graph on 2N vertices toward diameter <= D; return edges or None."""
    S = _random_regular_bip(N, d, rng)
    if S is None:
        return None
    V = 2 * N
    adj = [[] for _ in range(V)]
    for a, c in S:
        adj[a].append(c)
        adj[c].append(a)

    cost = _ball_cost(adj, V, D)
    t0 = time.monotonic()
    span = max(1e-6, t_end - t0)
    T0, T1 = 2.0, 0.2
    T = T0
    it = 0
    while cost > 0:
        now = time.monotonic()
        if now >= t_end:
            break
        if it % 8 == 0:
            frac = (now - t0) / span
            T = T0 * (T1 / T0) ** frac
        it += 1

        a1 = rng.randrange(N)
        c1 = adj[a1][rng.randrange(d)]
        a2 = rng.randrange(N)
        c2 = adj[a2][rng.randrange(d)]
        if a1 == a2 or c1 == c2:
            continue
        if (a1, c2) in S or (a2, c1) in S:
            continue

        _sw(adj, S, a1, c1, a2, c2)
        c_new = _ball_cost(adj, V, D)
        delta = c_new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c_new
        else:
            _sw(adj, S, a1, c2, a2, c1)  # undo

    if cost != 0:
        return None
    return [(a, c) for a in range(N) for c in adj[a]]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    best = (best_n, best_e)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Projective plane incidence: diameter 3, degree d when d-1 is a prime power.
    if D >= 3 and d >= 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)

    if D == 3:
        return best

    # Main search: annealed d-regular bipartite graphs, growing the side size N.
    rng = random.Random(seed * 1000003 + d * 131 + D)
    N = max(d, best_n // 2 + 1)
    slice_len = max(8.0, 0.25 * time_limit)
    while True:
        now = time.monotonic()
        rem = deadline - now
        if rem < 0.5:
            break
        t_end = now + min(rem, slice_len)
        edges = _anneal(N, d, D, rng, t_end)
        if edges is not None:
            consider(2 * N, edges)
            N = max(N + 1, best_n // 2 + 1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
