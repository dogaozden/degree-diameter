import math
import random
import time

import lib


def _fallback(d, D):
    """Safe baseline: K_{d,d} (optimal for D = 2), a projective-plane incidence graph when D >= 3, or a cycle for d = 2."""
    if d <= 0:
        return 1, []
    if D <= 1:
        return 2, [(0, 1)]
    if d == 2 and D >= 3:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    best = lib.haar_graph(d, range(d))
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n, e = lib.projective_plane_incidence(q)  # degree q + 1 <= d
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
                break
    return best


def _bad(N, E, D):
    """Number of unordered vertex pairs at distance > D in the bipartite graph with sides of size N.

    A-vertex a is index a; B-vertex b is index N + b. Pairs in different components count as bad.
    """
    n = 2 * N
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(N + b)
        adj[N + b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _grow(N, E, d, k, rng):
    """Add k new vertex pairs by degree-preserving splicing of old edges.

    For a new pair (x, y): repeatedly take an old edge (a, b), remove it, and add (a, y) and (x, b).
    Every old vertex keeps its degree, and the new vertices reach degree d. Returns (N+k, E) or None.
    """
    E = list(E)
    new = []
    for t in range(k):
        x = N + t
        y = N + t
        nx = set()  # B-indices joined to x
        ny = set()  # A-indices joined to y
        tries = 0
        while len(nx) < d:
            tries += 1
            if tries > 20000 or not E:
                return None
            i = rng.randrange(len(E))
            a, b = E[i]
            if a in ny or b in nx:
                continue
            E[i] = E[-1]
            E.pop()
            new.append((a, y))
            new.append((x, b))
            ny.add(a)
            nx.add(b)
    return N + k, E + new


def _repair(N, E, D, end, rng, max_evals=4000):
    """Simulated annealing over degree-preserving 2-switches, minimising bad pairs. Returns E or None."""
    E = list(E)
    m = len(E)
    eset = set(E)
    cost = _bad(N, E, D)
    t0 = time.monotonic()
    span = max(1.0, end - t0)
    for _ in range(max_evals):
        if cost == 0:
            break
        now = time.monotonic()
        if now > end:
            break
        frac = (now - t0) / span
        T = 0.6 * (1.0 - frac) + 0.05
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e:
            continue
        if (a, e) in eset or (c, b) in eset:
            continue
        E[i] = (a, e)
        E[j] = (c, b)
        nc = _bad(N, E, D)
        delta = nc - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            eset.discard((a, b))
            eset.discard((c, e))
            eset.add((a, e))
            eset.add((c, b))
            cost = nc
        else:
            E[i] = (a, b)
            E[j] = (c, e)
    return E if cost == 0 else None


def _search(d, D, seed, deadline):
    """Grow a d-regular bipartite graph one chunk at a time, repairing diameter after each growth step.

    Returns (N, E) for the last fully repaired graph (sides of size N), which always has diameter <= D.
    """
    rng = random.Random(seed * 7919 + d * 131 + D)
    N = d
    E = [(a, b) for a in range(d) for b in range(d)]
    chunk = max(1, N // 16)
    misses = 0
    while time.monotonic() < deadline and misses < 3:
        grown = _grow(N, E, d, chunk, rng)
        if grown is None:
            misses += 1
            chunk = max(1, chunk // 2)
            continue
        N2, E2 = grown
        now = time.monotonic()
        step_end = min(deadline, now + max(2.0, (deadline - now) * 0.2))
        res = _repair(N2, E2, D, step_end, rng)
        if res is not None:
            N, E = N2, res
            misses = 0
            chunk = max(1, min(max(1, N // 16), chunk * 2))
        else:
            misses += 1
            chunk = max(1, chunk // 2)
    return N, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    best = _fallback(d, D)
    if d < 3 or D < 3:
        return best
    try:
        N, E = _search(d, D, seed, deadline)
        n = 2 * N
        edges = [(a, N + b) for a, b in E]
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except Exception:
        pass
    if not lib.is_valid(best[0], best[1], d, D):
        best = _fallback(d, D)
    return best
