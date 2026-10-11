import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Search for d-regular bipartite graphs of diameter <= D by annealing.
#
# State: N left vertices 0..N-1, N right vertices 0..N-1, and a list E of
# N*d edges (a, b). Moves are double-edge swaps, which keep the graph simple
# and d-regular and bipartite. Cost = number of unordered vertex pairs at
# distance > D. Growth adds one left and one right vertex by splitting a
# matching of size d, which keeps degrees exact.
# ----------------------------------------------------------------------------

def _adj(N, E):
    """Adjacency lists on global ids: left a -> a, right b -> N + b."""
    adj = [[] for _ in range(2 * N)]
    for a, b in E:
        adj[a].append(N + b)
        adj[N + b].append(a)
    return adj


def _bad(n, adj, D):
    """Number of unordered pairs at distance > D (unreachable pairs count)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    total = 0
    for r in reach:
        total += n - r.bit_count()
    return total // 2


def _anneal(N, E, D, deadline, rng, stall_limit):
    """Anneal double-edge swaps until cost 0. Returns the edge list, or None."""
    E = list(E)
    S = set(E)
    adj = _adj(N, E)
    cost = _bad(2 * N, adj, D)
    m = len(E)
    stall = 0
    T = 0.5
    while cost > 0 and stall < stall_limit and time.monotonic() < deadline:
        i = rng.randrange(m)
        j = rng.randrange(m)
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        n1 = (a1, b2)
        n2 = (a2, b1)
        if n1 in S or n2 in S:
            continue
        E[i] = n1
        E[j] = n2
        S.discard((a1, b1))
        S.discard((a2, b2))
        S.add(n1)
        S.add(n2)
        adj2 = _adj(N, E)
        c2 = _bad(2 * N, adj2, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            stall = 0 if delta < 0 else stall + 1
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            S.discard(n1)
            S.discard(n2)
            S.add((a1, b1))
            S.add((a2, b2))
            stall += 1
        T = max(0.05, T * 0.998)
    if cost == 0:
        return E
    return None


def _extend(N, E, d, rng):
    """Add one left and one right vertex by splitting a matching of size d. None on failure."""
    pick = None
    for _ in range(30):
        order = list(range(len(E)))
        rng.shuffle(order)
        used_a = set()
        used_b = set()
        chosen = []
        for idx in order:
            a, b = E[idx]
            if a in used_a or b in used_b:
                continue
            used_a.add(a)
            used_b.add(b)
            chosen.append(idx)
            if len(chosen) == d:
                break
        if len(chosen) == d:
            pick = chosen
            break
    if pick is None:
        return None
    pickset = set(pick)
    A = [E[k][0] for k in pick]
    B = [E[k][1] for k in pick]
    newE = [e for k, e in enumerate(E) if k not in pickset]
    # New right vertex N adjacent to the old left ends A; new left vertex N adjacent to old right ends B.
    for a in A:
        newE.append((a, N))
    for b in B:
        newE.append((N, b))
    return N + 1, newE


def _search(d, D, deadline, rng):
    """Grow a valid d-regular bipartite graph of diameter <= D. Returns (N, E) or None."""
    N = 2 * d
    shifts = rng.sample(range(N), d)
    E = [(i, (i + s) % N) for i in range(N) for s in shifts]
    E = _anneal(N, E, D, deadline, rng, 3000)
    if E is None:
        return None
    best_n, best_e = N, E
    step = 1
    stall = 800
    while time.monotonic() < deadline:
        n2, e2 = best_n, list(best_e)
        ok = True
        for _ in range(step):
            r = _extend(n2, e2, d, rng)
            if r is None:
                ok = False
                break
            n2, e2 = r
        if ok:
            res = _anneal(n2, e2, D, deadline, rng, stall)
            if res is not None:
                best_n, best_e = n2, res
                step *= 2
                continue
        if step > 1:
            step //= 2
        else:
            if not ok:
                break
            stall = min(stall * 2, 200000)
    return best_n, best_e


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for any D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d == 2:
        # Cycle C_{2D} has diameter D.
        consider(*lib.haar_graph(D, [0, 1]))
        return best

    if D >= 3:
        # Projective plane incidence when d - 1 is a prime power.
        if lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))

    if d >= 3 and D >= 3:
        res = _search(d, D, deadline, rng)
        if res is not None:
            N, E = res
            edges = [(a, N + b) for a, b in E]
            consider(2 * N, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
