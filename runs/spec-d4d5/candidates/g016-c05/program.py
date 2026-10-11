import math
import random
import time

import lib


def _popcount(x):
    return bin(x).count("1")


def _moore_bound(d, D):
    """Bipartite Moore bound 2 * sum_{i<D} (d-1)^i, used to skip impossible orders."""
    return 2 * sum((d - 1) ** i for i in range(D))


def _missing_pairs(n, E, D):
    """Ordered vertex pairs not joined by a path of length <= D (0 means diameter <= D)."""
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - _popcount(r) for r in reach)


def _anneal_regular(s, d, D, rng, deadline):
    """Edge-switch annealing over d-regular bipartite graphs with s vertices per side.

    Starts from a circulant d-regular bipartite graph and performs degree-preserving
    switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), accepting by Metropolis on the number
    of missing pairs. Returns the edge list (A global ids 0..s-1, B global ids s..2s-1)
    when diameter <= D is reached, else None.
    """
    n = 2 * s
    E = []
    S = set()
    for i in range(s):
        for t in range(d):
            e = (i, s + (i + t) % s)
            E.append(e)
            S.add(e)
    cur = _missing_pairs(n, E, D)
    if cur == 0:
        return E
    L = len(E)
    t0 = time.monotonic()
    total = max(1e-6, deadline - t0)
    T0, T1 = 4.0, 0.3
    while True:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t0) / total
        T = T0 * ((T1 / T0) ** frac)
        i = rng.randrange(L)
        j = rng.randrange(L)
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        n1, n2 = (a1, b2), (a2, b1)
        if n1 in S or n2 in S:
            continue
        E[i] = n1
        E[j] = n2
        S.discard((a1, b1))
        S.discard((a2, b2))
        S.add(n1)
        S.add(n2)
        c = _missing_pairs(n, E, D)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c
            if cur == 0:
                return E
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            S.discard(n1)
            S.discard(n2)
            S.add((a1, b1))
            S.add((a2, b2))
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (diameter 2), valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    try:
        # Projective plane incidence when d-1 is a prime power (diameter 3).
        if D >= 3 and d >= 2 and lib.is_prime_power(d - 1):
            n0, e0 = lib.projective_plane_incidence(d - 1)
            consider(n0, e0)
    except Exception:
        pass

    try:
        if d >= 3 and D >= 3:
            bound = _moore_bound(d, D)
            s = best_n // 2 + 1
            while time.monotonic() < deadline and 2 * s <= bound:
                E = _anneal_regular(s, d, D, rng, deadline)
                if E is None:
                    break
                edges = [(a, b) for a, b in E]
                if not consider(2 * s, edges):
                    break
                s += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
