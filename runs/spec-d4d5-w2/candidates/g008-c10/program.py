import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold experiment: grow a bipartite graph one vertex-pair at a time, keeping
# max degree <= d, and repair diameter violations with simulated annealing
# over degree-preserving 2-switches. Start from K_{d,d}, which is valid for
# any D >= 2. Safe fallbacks: K_{d,d} and PG(2,q) incidence (for D >= 3).
# ----------------------------------------------------------------------------


def _k_dd(d):
    return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]


def _pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _bad_pairs(N, E, D):
    """Ordered pairs of vertices at distance > D (unreachable counts as bad)."""
    n = 2 * N
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(N + b)
        adj[N + b].append(a)
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


def _grow(N, E, d, rng):
    """Add vertex pair (newA, newB). Pick up to d edges (x, y) with distinct x and
    distinct y, replace each by (newA, y) and (x, newB). Degrees of x, y unchanged."""
    newA, newB = N, N
    order = list(range(len(E)))
    rng.shuffle(order)
    picks = []
    usedX, usedY = set(), set()
    for idx in order:
        if len(picks) >= d:
            break
        x, y = E[idx]
        if x in usedX or y in usedY:
            continue
        picks.append(idx)
        usedX.add(x)
        usedY.add(y)
    removed = set(picks)
    E2 = [e for i, e in enumerate(E) if i not in removed]
    for idx in picks:
        x, y = E[idx]
        E2.append((newA, y))
        E2.append((x, newB))
    return N + 1, E2


def _saturate(N, E, d, rng):
    """Add edges between deficient opposite-side vertices. Never increases distances."""
    E = list(E)
    Eset = set(E)
    degA = [0] * N
    degB = [0] * N
    for a, b in E:
        degA[a] += 1
        degB[b] += 1
    La = [a for a in range(N) if degA[a] < d]
    Lb = [b for b in range(N) if degB[b] < d]
    pairs = [(a, b) for a in La for b in Lb if (a, b) not in Eset]
    rng.shuffle(pairs)
    for a, b in pairs:
        if degA[a] < d and degB[b] < d:
            E.append((a, b))
            degA[a] += 1
            degB[b] += 1
    return E


def _anneal(N, E, D, rng, deadline, cap):
    """Degree-preserving 2-switch annealing on E (mutated in place). Returns (E, cost)."""
    Eset = set(E)
    cur = _bad_pairs(N, E, D)
    if cur == 0 or len(E) < 2:
        return E, cur
    T0, T1 = 2.0, 0.15
    decay = (T1 / T0) ** (1.0 / cap)
    T = T0
    for it in range(cap):
        if cur == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        T *= decay
        m = len(E)
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
        if e1 in Eset or e2 in Eset:
            continue
        E[i] = e1
        E[j] = e2
        Eset.discard((a1, b1))
        Eset.discard((a2, b2))
        Eset.add(e1)
        Eset.add(e2)
        new = _bad_pairs(N, E, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            Eset.discard(e1)
            Eset.discard(e2)
            Eset.add((a1, b1))
            Eset.add((a2, b2))
    return E, cur


def _search(d, D, rng, deadline, consider):
    """Grow from K_{d,d}; each growth step must be repaired to diameter <= D."""
    N = d
    E = [(a, b) for a in range(d) for b in range(d)]
    cap = 400
    while time.monotonic() < deadline:
        N2, E2 = _grow(N, E, d, rng)
        E2 = _saturate(N2, E2, d, rng)
        E2, cur = _anneal(N2, E2, D, rng, deadline, cap)
        if cur == 0:
            N, E = N2, E2
            consider(2 * N, [(a, N + b) for a, b in E])
            cap = 400
        else:
            # Keep the valid state N, E and retry with a fresh random growth and more effort.
            cap = int(cap * 1.3) + 1


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.2, min(0.8 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = _k_dd(d)
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if best_n >= lib.moore_bound(d, D):
        return best

    if D >= 3:
        pg = _pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if best_n < lib.moore_bound(d, D) and time.monotonic() < deadline:
        try:
            _search(d, D, rng, deadline, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = _k_dd(d)
    return best
