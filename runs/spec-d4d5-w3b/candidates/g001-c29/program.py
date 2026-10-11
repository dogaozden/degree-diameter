import math
import random
import time

import lib


def _cost(N, E, D):
    """Sum over vertices of the number of vertices at distance > D (zero iff diameter <= D)."""
    n = 2 * N
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(N + b)
        adj[N + b].append(a)
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        if new == ball:
            break
        ball = new
    return sum(n - x.bit_count() for x in ball)


def _scramble(E, rng, steps):
    """Randomize a bipartite simple edge list by degree-preserving 2-switches (no cost evaluation)."""
    E = list(E)
    S = set(E)
    m = len(E)
    for _ in range(steps):
        i, j = rng.randrange(m), rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e:
            continue
        f1, f2 = (a, e), (c, b)
        if f1 in S or f2 in S:
            continue
        S.discard((a, b))
        S.discard((c, e))
        S.add(f1)
        S.add(f2)
        E[i], E[j] = f1, f2
    return E


def _anneal(N, E, D, rng, deadline, iters):
    """Simulated annealing over degree-preserving 2-switches minimizing the distance-violation cost."""
    E = list(E)
    S = set(E)
    m = len(E)
    cost = _cost(N, E, D)
    T0, T1 = 3.0, 0.2
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / max(1, iters))
        i, j = rng.randrange(m), rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e:
            continue
        f1, f2 = (a, e), (c, b)
        if f1 in S or f2 in S:
            continue
        E[i], E[j] = f1, f2
        S.discard((a, b))
        S.discard((c, e))
        S.add(f1)
        S.add(f2)
        c2 = _cost(N, E, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            E[i], E[j] = (a, b), (c, e)
            S.discard(f1)
            S.discard(f2)
            S.add((a, b))
            S.add((c, e))
    return cost == 0, E, cost


def _split(N, E, d, rng):
    """Insert one A-vertex and one B-vertex by splitting d matching edges; degrees of old vertices are kept."""
    m = len(E)
    if m < d:
        return None
    idx = None
    for _ in range(200):
        cand = rng.sample(range(m), d)
        if len({E[i][0] for i in cand}) == d and len({E[i][1] for i in cand}) == d:
            idx = cand
            break
    if idx is None:
        return None
    chosen = set(idx)
    removed = [E[i] for i in idx]
    NE = [e for i, e in enumerate(E) if i not in chosen]
    v = N  # new A-side index
    w = N  # new B-side index
    for a, b in removed:
        NE.append((v, b))
        NE.append((a, w))
    return N + 1, NE


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: a single edge is valid for any d >= 1, D >= 1.
    best = (2, [(0, 1)])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d >= 2 and D >= 2:
        consider(*lib.haar_graph(d, range(d)))  # K_{d,d}, diameter 2
    if d >= 2 and D >= 3:
        q = d - 1
        while q >= 2 and not lib.is_prime_power(q):
            q -= 1
        if q >= 2:
            consider(*lib.projective_plane_incidence(q))

    # Direct search: anneal bipartite d-regular graphs on a fixed side size N with
    # 2-switches, then grow the side size by one via edge splitting after each success.
    if d >= 2 and D >= 3:
        rng = random.Random(seed * 1000003 + d * 101 + D)
        N = max(d, best[0] // 2)
        E = None
        fails = 0
        iters = 6000
        while time.monotonic() < deadline:
            if E is None:
                E = _scramble([(a, (a + s) % N) for a in range(N) for s in range(d)],
                              rng, 4 * N * d)
            ok, E2, _ = _anneal(N, E, D, rng, deadline, iters)
            if ok:
                consider(2 * N, [(a, N + b) for a, b in E2])
                g = _split(N, E2, d, rng)
                if g is None:
                    break
                N, E = g
                fails = 0
            else:
                fails += 1
                E = E2 if fails % 4 else None

    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])
    return best
