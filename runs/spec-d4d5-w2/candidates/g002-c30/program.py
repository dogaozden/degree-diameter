import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bipartite regular graphs found by edge-switch annealing.
#
# Every vertex has degree exactly d. The side A is vertices 0..N-1 and the side B
# is the rest. Double edge switches keep the graph bipartite and regular.
# The cost is the number of ordered vertex pairs at distance > D, measured with
# big-integer reachability bitmasks. The graph grows one A/B vertex pair at a time,
# keeping regularity, and each growth step is followed by annealing.
# ----------------------------------------------------------------------------


def _bad(n, adj, D):
    """Number of ordered vertex pairs not within distance D. Zero means diameter <= D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _adj_from(n, E):
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    return adj


def _apply(adj, a, b, c, e):
    """Replace edges (a,b),(c,e) by (a,e),(c,b) in the adjacency lists."""
    adj[a][adj[a].index(b)] = e
    adj[e][adj[e].index(c)] = a
    adj[c][adj[c].index(e)] = b
    adj[b][adj[b].index(a)] = c


def _circulant(N, d):
    """Bipartite circulant d-regular start on 2N vertices: A_i ~ B_{i+s}, s in 0..d-1."""
    E = []
    for i in range(N):
        for s in range(d):
            E.append((i, N + (i + s) % N))
    return 2 * N, E


def _anneal(n, E, adj, D, deadline, rng):
    """Anneal double edge switches until diameter <= D or the deadline. E and adj are updated in place."""
    eset = set(E)
    cur = _bad(n, adj, D)
    if cur == 0:
        return True
    T0, T1 = 3.0, 0.3
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T = T0
    it = 0
    m = len(E)
    while cur > 0:
        if (it & 7) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        it += 1
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if (a, e) in eset or (c, b) in eset:
            continue
        _apply(adj, a, b, c, e)
        new = _bad(n, adj, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            E[i] = (a, e)
            E[j] = (c, b)
            eset.discard((a, b))
            eset.discard((c, e))
            eset.add((a, e))
            eset.add((c, b))
            cur = new
        else:
            _apply(adj, a, e, c, b)
    return cur == 0


def _insert(n, E, d, rng):
    """Add one A vertex (id n) and one B vertex (id n+1), keeping regularity.

    Remove d edges (a_k, b_k) with distinct a_k and distinct b_k, then add
    (a_k, B) and (A, b_k). Returns (n+2, new edge list) or None.
    """
    m = len(E)
    if m < d:
        return None
    idx = None
    for _ in range(300):
        cand = rng.sample(range(m), d)
        As = [E[k][0] for k in cand]
        Bs = [E[k][1] for k in cand]
        if len(set(As)) == d and len(set(Bs)) == d:
            idx = cand
            As_, Bs_ = As, Bs
            break
    if idx is None:
        return None
    A, B = n, n + 1
    drop = set(idx)
    E2 = [e for k, e in enumerate(E) if k not in drop]
    for a, b in zip(As_, Bs_):
        E2.append((a, B))
        E2.append((A, b))
    return n + 2, E2


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        # Even cycle of length 2D: bipartite, degree 2, diameter D.
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # Safe fallback: K_{d,d} has diameter 2.
    fallback = lib.haar_graph(d, range(d))

    # Fast path: projective plane meets the Moore bound when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    budget = 0.8 * time_limit
    budget_end = start + budget
    moore = lib.moore_bound(d, D)

    # Phase 1: find a valid starting circulant-based graph, shrinking N on failure.
    N = max(d, min(200, moore // 4))
    cur = None
    while time.monotonic() < budget_end and N >= d:
        n, E = _circulant(N, d)
        adj = _adj_from(n, E)
        slice_end = min(budget_end, time.monotonic() + 0.15 * budget)
        if _anneal(n, E, adj, D, slice_end, rng):
            cur = (n, E)
            break
        N2 = int(N * 0.92)
        N = N2 if N2 < N else N - 1

    if cur is None:
        return fallback

    # Phase 2: grow by one A/B pair at a time, re-annealing after each insertion.
    n, E = cur
    step_slice = max(1.0, 0.06 * budget)
    fails = 0
    while time.monotonic() < budget_end and fails < 6:
        res = _insert(n, E, d, rng)
        if res is None:
            break
        n2, E2 = res
        adj2 = _adj_from(n2, E2)
        slice_end = min(budget_end, time.monotonic() + step_slice)
        if _anneal(n2, E2, adj2, D, slice_end, rng):
            n, E = n2, E2
            fails = 0
        else:
            fails += 1

    edges = [(int(a), int(b)) for a, b in E]
    if n > fallback[0] and lib.is_valid(n, edges, d, D):
        return n, edges
    return fallback
