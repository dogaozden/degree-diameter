import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez record graph (degree q+2) when q = d-2 is a prime power >= 3."""
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except (ValueError, AssertionError):
        return None


# ----------------------------------------------------------------------------
# Graph utilities.
# ----------------------------------------------------------------------------

def _adj(n, edges):
    adj = [[] for _ in range(n)]
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    return adj


def _bipartition(n, edges):
    """Two-colouring of the graph (colour 0 = left side)."""
    adj = _adj(n, edges)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _is_regular(n, edges, d):
    deg = [0] * n
    for a, b in edges:
        deg[a] += 1
        deg[b] += 1
    return all(x == d for x in deg)


def _bad(N, adj, D):
    """Number of unordered vertex pairs at distance > D (bitmask balls, closed-neighbourhood steps)."""
    ball = [0] * N
    for v in range(N):
        m = 1 << v
        for u in adj[v]:
            m |= 1 << u
        ball[v] = m
    for _ in range(D - 1):
        new = [0] * N
        for v in range(N):
            m = ball[v]
            for u in adj[v]:
                m |= ball[u]
            new[v] = m
        ball = new
    return sum(N - ball[v].bit_count() for v in range(N)) // 2


# ----------------------------------------------------------------------------
# New idea: "stolen-matching growth with 2-switch annealing".
#
# Given a d-regular bipartite graph (L, R) of diameter <= D, grow it by two
# vertices a* (in L) and b* (in R), keeping it d-regular:
#   1. Pick a random matching M of size d in the graph.
#   2. Delete M; join a* to the right ends of M and b* to the left ends of M.
#      Every degree is restored to d, and the order increases by 2.
#   3. The result may have diameter > D. Repair it by degree-preserving
#      2-switches (a1-b1, a2-b2  ->  a1-b2, a2-b1), annealing the number of
#      vertex pairs at distance > D toward zero.
# Degree and bipartiteness are preserved by every move, so only diameter needs repair.
# ----------------------------------------------------------------------------

def _try_grow(n, E, d, D, deadline, rng, iters):
    N = n + 2
    a_new, b_new = n, n + 1

    M = None
    for _ in range(30):
        order = E[:]
        rng.shuffle(order)
        ua, ub, cand = set(), set(), []
        for a, b in order:
            if a not in ua and b not in ub:
                ua.add(a)
                ub.add(b)
                cand.append((a, b))
                if len(cand) == d:
                    break
        if len(cand) == d:
            M = cand
            break
    if M is None:
        return None

    Mset = set(M)
    E2 = [e for e in E if e not in Mset]
    E2 += [(a_new, b) for a, b in M]
    E2 += [(a, b_new) for a, b in M]

    S = {a * N + b for a, b in E2}
    cost = _bad(N, _adj(N, E2), D)
    T0, T1 = 1.0, 0.1
    L = len(E2)

    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            return None
        T = T0 * (T1 / T0) ** (it / iters)
        i, j = rng.randrange(L), rng.randrange(L)
        if i == j:
            continue
        a1, b1 = E2[i]
        a2, b2 = E2[j]
        if a1 == a2 or b1 == b2:
            continue
        k1 = a1 * N + b2
        k2 = a2 * N + b1
        if k1 in S or k2 in S:
            continue
        old1 = a1 * N + b1
        old2 = a2 * N + b2
        E2[i] = (a1, b2)
        E2[j] = (a2, b1)
        S.discard(old1)
        S.discard(old2)
        S.add(k1)
        S.add(k2)
        c2 = _bad(N, _adj(N, E2), D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            E2[i] = (a1, b1)
            E2[j] = (a2, b2)
            S.discard(k1)
            S.discard(k2)
            S.add(old1)
            S.add(old2)

    if cost != 0:
        return None
    if not lib.is_valid(N, E2, d, D):
        return None
    return N, E2


def _sa_grow(n, edges, d, D, deadline, rng, iters):
    """Repeatedly grow a d-regular base by two vertices while the annealer succeeds."""
    color = _bipartition(n, edges)
    cur_n = n
    cur_E = [(u, v) if color[u] == 0 else (v, u) for u, v in edges]
    while time.monotonic() < deadline:
        cand = _try_grow(cur_n, cur_E, d, D, deadline, rng, iters)
        if cand is None:
            continue
        cur_n, cur_E = cand
    return cur_n, cur_E


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Fallback: K_{d,d} has diameter 2 and is d-regular.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    bases = [best]
    if D >= 3:
        rec = _araujo(d)
        if rec is not None:
            consider(rec[0], rec[1])
            bases.append(rec)
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            bases.append(pg)

    # Growth via stolen-matching + 2-switch annealing (skipped for tiny d,
    # where the small known graphs are already optimal).
    if d >= 5:
        regular = [b for b in bases if _is_regular(b[0], b[1], d)]
        base = max(regular, key=lambda x: x[0])
        n2, e2 = _sa_grow(base[0], base[1], d, D, deadline, rng, iters=2500)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
