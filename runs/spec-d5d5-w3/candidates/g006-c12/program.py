import math
import random
import time

import lib

STEPS = 2000  # annealing steps per growth attempt


def _kdd(d):
    """K_{d,d}: valid for every D >= 2 (diameter 2)."""
    n = 2 * d
    edges = [(i, d + j) for i in range(d) for j in range(d)]
    return n, edges


def _bad(adj, n, D):
    """Number of unordered vertex pairs at distance > D (bitset ball computation)."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        nb = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nb[v] = x
        ball = nb
    return sum(n - r.bit_count() for r in ball) // 2


def _swap(adj, a1, b1, a2, b2):
    """Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1). Degrees are preserved."""
    adj[a1][adj[a1].index(b1)] = b2
    adj[b1][adj[b1].index(a1)] = a2
    adj[a2][adj[a2].index(b2)] = b1
    adj[b2][adj[b2].index(a2)] = a1


def _anneal(adj, N, D, d, rng, deadline, steps):
    """Edge-swap simulated annealing on a d-regular bipartite graph with parts of size N.

    A-side ids are 0..N-1, B-side ids are N..2N-1. Modifies adj in place.
    Returns True when the diameter is at most D (cost zero).
    """
    n = 2 * N
    cost = _bad(adj, n, D)
    if cost == 0:
        return True
    E = set()
    for a in range(N):
        for x in adj[a]:
            E.add(a * n + x)
    T0, T1 = 1.0, 0.05
    for it in range(steps):
        if time.monotonic() > deadline:
            return False
        T = T0 * (T1 / T0) ** (it / steps)
        a1 = rng.randrange(N)
        b1 = adj[a1][rng.randrange(d)]
        a2 = rng.randrange(N)
        b2 = adj[a2][rng.randrange(d)]
        if a1 == a2 or b1 == b2:
            continue
        if a1 * n + b2 in E or a2 * n + b1 in E:
            continue
        _swap(adj, a1, b1, a2, b2)
        c2 = _bad(adj, n, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
            E.discard(a1 * n + b1)
            E.discard(a2 * n + b2)
            E.add(a1 * n + b2)
            E.add(a2 * n + b1)
            if cost == 0:
                return True
        else:
            _swap(adj, a1, b2, a2, b1)
    return False


def _extend(adj, N, d, rng):
    """Add one A-vertex and one B-vertex, keeping d-regularity.

    Removes a matching of d edges (a_i, b_i), then joins the new A-vertex to every b_i
    and the new B-vertex to every a_i. Returns the new adjacency (parts of size N+1) or None.
    """
    chosen = None
    for _ in range(30):
        order = list(range(N))
        rng.shuffle(order)
        pick = []
        used = set()
        for a in order:
            opts = [b for b in adj[a] if b not in used]
            if opts:
                b = rng.choice(opts)
                pick.append((a, b))
                used.add(b)
                if len(pick) == d:
                    break
        if len(pick) == d:
            chosen = pick
            break
    if chosen is None:
        return None
    new = [None] * (2 * N + 2)
    for a in range(N):
        new[a] = [x if x < N else x + 1 for x in adj[a]]
    for x in range(N, 2 * N):
        new[x + 1] = list(adj[x])
    A2, B2 = N, 2 * N + 1
    new[A2] = []
    new[B2] = []
    for a, b in chosen:
        bb = b + 1
        new[a][new[a].index(bb)] = B2
        new[bb][new[bb].index(a)] = A2
        new[A2].append(bb)
        new[B2].append(a)
    return new


def _edges_of(adj, N):
    return [(a, x) for a in range(N) for x in adj[a]]


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 5.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    best_n, best_e = _kdd(d)
    if D == 2:
        return best_n, best_e

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best_n, best_e

    moore = lib.moore_bound(d, D)
    Nmax = moore // 2

    # Start from K_{d,d} as a d-regular bipartite graph with parts of size d.
    cur = [None] * (2 * d)
    for a in range(d):
        cur[a] = [d + j for j in range(d)]
    for j in range(d):
        cur[d + j] = list(range(d))
    N = d
    step = max(1, N // 20)

    while time.monotonic() < deadline and N < Nmax:
        cand, Nc = cur, N
        tgt = min(Nmax, N + step)
        ok = True
        while Nc < tgt:
            nxt = _extend(cand, Nc, d, rng)
            if nxt is None:
                ok = False
                break
            cand, Nc = nxt, Nc + 1
        if ok and _anneal(cand, Nc, D, d, rng, deadline, STEPS):
            cur, N = cand, Nc
            consider(2 * N, _edges_of(cur, N))
        else:
            if step == 1:
                break
            step = max(1, step // 2)

    return best_n, best_e
