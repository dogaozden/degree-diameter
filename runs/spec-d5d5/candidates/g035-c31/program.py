import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over a wide family of finite groups (cyclic, abelian
# products, dihedral, and semidirect products Z_m x| Z_k), annealed over the
# connection set S. A bi-Cayley graph on 2G vertices with A_x ~ B_{x g}
# (g in S) is bipartite and d-regular. Left translation is an automorphism,
# so checking eccentricities from A_0 and B_0 covers the whole graph.
# ----------------------------------------------------------------------------

MAX_GROUPS = 8        # groups tried per order N before choosing another N
ANNEAL_ITERS = 1500   # annealing steps per group


def _cyc(G):
    return lambda x, y: (x + y) % G


def _prod(a, b):
    """Z_a x Z_b, element x = x1*b + x2."""
    def mul(x, y):
        x1, x2 = divmod(x, b)
        y1, y2 = divmod(y, b)
        return ((x1 + y1) % a) * b + (x2 + y2) % b
    return mul


def _dih(m):
    """Dihedral group of order 2m; element s*m + t stands for r^t f^s."""
    def mul(x, y):
        s1, t1 = divmod(x, m)
        s2, t2 = divmod(y, m)
        t = (t1 + (t2 if s1 == 0 else -t2)) % m
        return ((s1 + s2) % 2) * m + t
    return mul


def _group_muls(G, rng):
    """Shuffled list of (name, multiplication function) for groups of order G."""
    out = [("Z", _cyc(G))]
    for a in range(2, G):
        if G % a:
            continue
        b = G // a
        if a > b:
            break
        if math.gcd(a, b) > 1:
            out.append(("ZxZ", _prod(a, b)))
    if G % 2 == 0 and G // 2 >= 3:
        out.append(("D", _dih(G // 2)))
    for k in range(2, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            break
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append(("SD", lib.semidirect_group(m, k, r)[1]))
    rng.shuffle(out)
    return out


def _table(G, mul):
    """Multiplication table T[x][y] = x*y and inverse list for a group of order G."""
    T = [[mul(x, y) for y in range(G)] for x in range(G)]
    e = next(x for x in range(G) if T[x][x] == x)
    invs = [T[x].index(e) for x in range(G)]
    return T, invs


def _cost(G, T, invs, S, D):
    """Number of (source, vertex) pairs not within distance D, sources A_0 and B_0."""
    Sinv = [invs[g] for g in S]
    N2 = 2 * G
    total = 0
    for src in (0, G):
        seen = bytearray(N2)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    row = T[u]
                    for g in S:
                        v = G + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - G]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N2 - count
    return total


def _anneal(G, T, invs, d, D, rng, deadline, iters):
    """Simulated annealing over S (identity fixed in S, WLOG). Returns S with zero cost or None."""
    if G < d + 1:
        return None
    e = next(x for x in range(G) if T[x][x] == x)
    S = [e]
    while len(S) < d:
        c = rng.randrange(G)
        if c not in S:
            S.append(c)
    cur = _cost(G, T, invs, S, D)
    T0 = 3.0
    for step in range(iters):
        if cur == 0:
            break
        if (step & 31) == 0 and time.monotonic() > deadline:
            break
        temp = T0 * (1.0 - step / iters) + 0.05
        i = rng.randrange(1, d)
        c = rng.randrange(G)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _cost(G, T, invs, S2, D)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _fallback(d, D):
    """K_{d,d}: diameter 2, valid for every D >= 2."""
    return lib.haar_graph(d, range(d))


def _build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = _fallback(d, D)
    if D == 2 or d < 2:
        return best

    moore = lib._moore_bound(d, D)
    best_n = best[0]

    while time.monotonic() < deadline and best_n < moore:
        lo = best_n // 2 + 1
        if lo > moore // 2:
            break
        N = lo + rng.randrange(max(1, lo // 20))
        cands = _group_muls(N, rng)
        for _name, mul in cands[:MAX_GROUPS]:
            if time.monotonic() > deadline:
                break
            T, invs = _table(N, mul)
            S = _anneal(N, T, invs, d, D, rng, deadline, ANNEAL_ITERS)
            if S is not None:
                edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                n2 = 2 * N
                if n2 > best_n and lib.is_valid(n2, edges, d, D):
                    best = (n2, edges)
                    best_n = n2
                break
    return best


def build(d, D, seed, time_limit):
    try:
        n, edges = _build(d, D, seed, time_limit)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if D >= 2 and d >= 1:
        return _fallback(d, D)
    return 1, []
