import math
import random
import time

import lib


def _pg_fallback(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _group(a, b):
    """Abelian group Z_a x Z_b with element x = i*b + j. Returns (add, sub) tables."""
    m = a * b
    add = [[0] * m for _ in range(m)]
    neg = [0] * m
    for x in range(m):
        xi, xj = divmod(x, b)
        neg[x] = ((-xi) % a) * b + (-xj) % b
        row = add[x]
        for y in range(m):
            yi, yj = divmod(y, b)
            row[y] = ((xi + yi) % a) * b + (xj + yj) % b
    sub = [[add[x][neg[y]] for y in range(m)] for x in range(m)]
    return add, sub


def _search_set(m, sub, d, rng, budget):
    """Anneal a d-subset S of the group (0 in S) so that S - S covers every nonzero element.

    For a Haar-type bipartite graph on two copies of G with a_x ~ b_{x+s}, s in S,
    S - S = G gives diameter 3, since S - S + S = G + S = G then holds automatically.
    Returns S, or None if the budget runs out.
    """
    t_start = time.monotonic()
    t_end = t_start + budget
    S = [0] + rng.sample(range(1, m), d - 1)
    inS = [False] * m
    for x in S:
        inS[x] = True
    cnt = [0] * m
    for i in range(d):
        for j in range(d):
            if i != j:
                cnt[sub[S[i]][S[j]]] += 1
    st = [sum(1 for g in range(1, m) if cnt[g] == 0)]  # number of uncovered nonzero elements

    def apply(g, delta):
        c0 = cnt[g]
        c1 = c0 + delta
        cnt[g] = c1
        if c0 == 0:
            st[0] -= 1
        elif c1 == 0:
            st[0] += 1

    def bump(i, delta):
        x = S[i]
        for j in range(d):
            if j != i:
                y = S[j]
                apply(sub[x][y], delta)
                apply(sub[y][x], delta)

    T0 = 0.6
    T = T0
    it = 0
    while st[0] > 0:
        it += 1
        if (it & 127) == 0:
            now = time.monotonic()
            if now >= t_end:
                return None
            T = T0 * (0.02 ** ((now - t_start) / budget))
        i = rng.randrange(1, d)
        y = rng.randrange(1, m)
        if inS[y]:
            continue
        x = S[i]
        old = st[0]
        bump(i, -1)
        S[i] = y
        bump(i, +1)
        delta = st[0] - old
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            inS[x] = False
            inS[y] = True
        else:
            bump(i, -1)
            S[i] = x
            bump(i, +1)
    return S


def _haar_from_group(m, add, S):
    """Bipartite graph with parts a_x, b_x (x in G) and edges a_x ~ b_{x+s} for s in S."""
    E = []
    for x in range(m):
        row = add[x]
        for s in S:
            E.append((x, m + row[s]))
    return 2 * m, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 2.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])

    if D >= 3:
        pg = _pg_fallback(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg

    # Main family for D >= 3: Haar graphs over abelian groups Z_a x Z_b, found by
    # difference-cover search. The Moore-type limit for D = 3 is m <= d^2 - d + 1.
    if D >= 3 and d >= 2:
        M = d * d - d + 1
        m = max(d, best[0] // 2)
        while m <= M and time.monotonic() < deadline:
            remaining = deadline - time.monotonic()
            budget = min(10.0, max(0.5, 0.15 * remaining))
            a = rng.choice([x for x in range(1, m + 1) if m % x == 0])
            add, sub = _group(a, m // a)
            S = _search_set(m, sub, d, rng, budget)
            if S is not None:
                n, E = _haar_from_group(m, add, S)
                if n > best[0] and lib.is_valid(n, E, d, D):
                    best = (n, E)
            m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
