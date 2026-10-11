import math
import random
import time

import lib


def _group(ma, mb):
    """Abelian group Z_ma x Z_mb with element a*mb+b. Returns (order, add, sub) tables."""
    m = ma * mb
    add = [[0] * m for _ in range(m)]
    sub = [[0] * m for _ in range(m)]
    for x in range(m):
        a1, b1 = divmod(x, mb)
        for y in range(m):
            a2, b2 = divmod(y, mb)
            add[x][y] = ((a1 + a2) % ma) * mb + (b1 + b2) % mb
            sub[x][y] = ((a1 - a2) % ma) * mb + (b1 - b2) % mb
    return m, add, sub


def _cover_search(m, sub, d, rng, deadline):
    """Find S in a group of order m, |S| = d, 0 in S, with S - S = whole group.

    Such S gives the Haar-type bipartite graph a_x ~ b_{x+s} (2m vertices, degree d),
    which has diameter <= 3 (vertex-transitive, eccentricity of a_0 is <= 3).
    Simulated annealing minimises the number of group elements not covered by S - S.
    Returns S, or None if the deadline passes first.
    """
    S = [0] + rng.sample(range(1, m), d - 1)
    cnt = [0] * m
    unc = [m - 1]  # nonzero group elements not yet covered by differences

    def bump(g, delta):
        old = cnt[g]
        new = old + delta
        cnt[g] = new
        if old == 0 and new > 0:
            unc[0] -= 1
        elif old > 0 and new == 0:
            unc[0] += 1

    def remove(i):
        s = S[i]
        for j in range(d):
            if j != i:
                t = S[j]
                bump(sub[s][t], -1)
                bump(sub[t][s], -1)

    def insert(i, x):
        S[i] = x
        for j in range(d):
            if j != i:
                t = S[j]
                bump(sub[x][t], 1)
                bump(sub[t][x], 1)

    for i in range(d):
        for j in range(d):
            if i != j:
                bump(sub[S[i]][S[j]], 1)

    cur = unc[0]
    it = 0
    cycle = 20000
    T0, T1 = 1.5, 0.05
    while True:
        if unc[0] == 0:
            return S
        it += 1
        if (it & 255) == 0 and time.monotonic() >= deadline:
            return None
        phase = (it % cycle) / cycle
        T = T0 * (T1 / T0) ** phase
        idx = rng.randrange(1, d)
        x = rng.randrange(1, m)
        if x in S:
            continue
        old = S[idx]
        remove(idx)
        insert(idx, x)
        new = unc[0]
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
        else:
            remove(idx)
            insert(idx, old)


def _haar_from(m, add, S):
    """Haar graph of an abelian group: a_x ~ b_{x+s} for s in S. Vertices a_x = x, b_y = m + y."""
    edges = []
    for x in range(m):
        for s in S:
            edges.append((x, m + add[x][s]))
    return 2 * m, edges


def _moore(d, D):
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    # Safe structured fallback for D = 3.
    best = None
    q = d - 1
    cand = None
    if D == 3 and q >= 2 and lib.is_prime_power(q):
        cand = lib.projective_plane_incidence(q)
    elif D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        cand = lib.araujo_lopez_graph(d - 2)
    if cand is not None and lib.is_valid(cand[0], cand[1], d, D):
        best = cand

    # Bold alternative for D = 3: abelian Haar graphs from difference covers.
    # Any group of order m with S - S = G (|S| = d) yields a valid bipartite graph
    # on 2m vertices. This does not need the projective-plane structure.
    if D == 3 and d >= 3:
        ub = d * d - d + 1  # a difference cover of size d has at most d^2-d+1 elements
        m = (best[0] // 2 + 1) if best is not None else d + 1
        m = max(m, d + 1)
        while m <= ub and time.monotonic() < deadline:
            now = time.monotonic()
            slice_total = max(0.5, 0.4 * (deadline - now))
            groups = [(m, 1)]
            if m % 2 == 0 and m // 2 >= 2:
                groups.append((2, m // 2))
            per_group = slice_total / len(groups)
            for ma, mb in groups:
                if time.monotonic() >= deadline:
                    break
                order, add, sub = _group(ma, mb)
                g_deadline = min(deadline, time.monotonic() + per_group)
                S = _cover_search(order, sub, d, rng, g_deadline)
                if S is None:
                    continue
                n, edges = _haar_from(order, add, S)
                if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                    best = (n, edges)
                    break
            m += 1

    if best is not None:
        return best[0], list(best[1])

    # Generic fallback: random Haar graphs checked by diameter (any D).
    best_h = lib.haar_graph(d, range(d))  # K_{d,d}
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best_h, misses = found, 0
        else:
            misses += 1
        m += 1
    return best_h
