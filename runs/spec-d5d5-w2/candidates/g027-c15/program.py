import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Helpers.
# ----------------------------------------------------------------------------

def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance more than D (bitmask BFS)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _swap(adj, ES, N, rem, add):
    """Remove edges `rem` and add edges `add` (pairs (a, b), a in A, b in B local index)."""
    for a, b in rem:
        adj[a].remove(N + b)
        adj[N + b].remove(a)
        ES.discard(a * N + b)
    for a, b in add:
        adj[a].append(N + b)
        adj[N + b].append(a)
        ES.add(a * N + b)


def _start(N, d, rng):
    """Random bipartite graph on N+N vertices with degrees <= d (greedy, roughly regular)."""
    adj = [[] for _ in range(2 * N)]
    ES = set()
    EL = []
    for _ in range(d):
        perm = list(range(N))
        rng.shuffle(perm)
        for a in range(N):
            b = perm[a]
            if a * N + b not in ES and len(adj[a]) < d and len(adj[N + b]) < d:
                ES.add(a * N + b)
                EL.append([a, b])
                adj[a].append(N + b)
                adj[N + b].append(a)
    defA = [a for a in range(N) if len(adj[a]) < d]
    defB = [b for b in range(N) if len(adj[N + b]) < d]
    pairs = [(a, b) for a in defA for b in defB if a * N + b not in ES]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[N + b]) < d and a * N + b not in ES:
            ES.add(a * N + b)
            EL.append([a, b])
            adj[a].append(N + b)
            adj[N + b].append(a)
    return adj, ES, EL


def _anneal(N, d, D, rng, deadline):
    """Anneal degree-preserving 2-switches until the bipartite graph has diameter <= D.

    Returns the edge list (pairs of local indices) on success, None on timeout.
    """
    adj, ES, EL = _start(N, d, rng)
    cost = _bad(2 * N, adj, D)
    m = len(EL)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline or m < 2:
            return None
        frac = (now - t0) / span
        T = 2.0 * (1.0 - frac) + 0.05
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = EL[i]
        a2, b2 = EL[j]
        if a1 == a2 or b1 == b2:
            continue
        if a1 * N + b2 in ES or a2 * N + b1 in ES:
            continue
        old = [(a1, b1), (a2, b2)]
        new = [(a1, b2), (a2, b1)]
        _swap(adj, ES, N, old, new)
        c2 = _bad(2 * N, adj, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            EL[i] = [a1, b2]
            EL[j] = [a2, b1]
        else:
            _swap(adj, ES, N, new, old)
    return EL


def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Main entry point.
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

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite with max degree d.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Structured baselines (each validated before use).
    try:
        pg = _pg_best(d)
        if pg is not None:
            consider(pg[0], pg[1])
    except Exception:
        pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            n_a, e_a = lib.araujo_lopez_graph(d - 2)
            consider(n_a, e_a)
        except Exception:
            pass

    # New search family for D >= 4: annealed bipartite graphs with
    # degree-preserving 2-switches, scored by exact unreached-pair counts.
    if D >= 4 and d >= 3:
        try:
            good = max(d, best[0] // 2)
            step = max(1, good // 20)
            while time.monotonic() < deadline:
                cand = good + step
                if 2 * cand > moore:
                    step = max(1, step // 2)
                    if 2 * (good + step) > moore:
                        break
                    continue
                remaining = deadline - time.monotonic()
                slice_end = min(deadline, time.monotonic() + max(2.0, remaining / 3.0))
                EL = _anneal(cand, d, D, rng, slice_end)
                if EL is not None:
                    edges = [(a, cand + b) for a, b in EL]
                    before = best[0]
                    consider(2 * cand, edges)
                    if best[0] > before or True:
                        good = cand
                    step = step * 2
                else:
                    step = max(1, step // 2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
