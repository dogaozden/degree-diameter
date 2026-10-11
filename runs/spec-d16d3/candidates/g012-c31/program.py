"""Twin-doubled projective planes with searched arcs (diameter-3 family).

Idea: take PG(2,q) incidence (degree q+1) with spare capacity s = d - q - 1 per vertex.
Add an A-twin of each point v in a set S (adjacent to the q+1 lines through v) and a
B-twin of each line v in a set U (adjacent to the q+1 points on v). Twins only add load
to the vertices they touch, so S and U are independently required to satisfy
|N(w) ∩ S| <= s for every vertex w, where N(w) = {v : dot(v, w) = 0}. The order is
2(q^2+q+1) + |S| + |U|, and diameter 3 holds for any such S and U.

New in this version:
  * _max_arc: iterated local search for the largest such set, seeded by a conic
    (hyperoval for even q), with known arc bounds used as early exits.
  * per-q potential pruning and time shares proportional to potential.
Fallbacks: K_{d,d} (diameter 2), cycle C_{2D} for d = 2, K_2 for D = 1.
"""
import random
import time

import lib


def _pg(q):
    """Incidence of PG(2,q) as symmetric orthogonality adjacency on vector indices 0..m-1."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    nbr = [[] for _ in range(m)]
    for u, v in edges:
        nbr[u].append(v - m)
        nbr[v - m].append(u)
    return m, nbr, edges


def _conic_seed(q):
    """Conic (plus nucleus for even q): an arc with at most 2 points on every line."""
    F = lib.GF(q)
    idx = {p: i for i, p in enumerate(lib.projective_points(q))}
    S = [idx[(1, t, F.mul(t, t))] for t in range(q)] + [idx[(0, 0, 1)]]
    if q % 2 == 0:
        S.append(idx[(0, 1, 0)])
    return S


def _max_arc(m, s, nbr, seed_set, ub, deadline, rng):
    """Iterated local search for a large S with |nbr[w] ∩ S| <= s for every w.

    Moves: remove 1-3 random members, then greedily refill in random order.
    The walk restarts from the best set when it drifts too far below it.
    """
    cl = [0] * m
    in_s = [False] * m
    cur = []

    def add(v):
        in_s[v] = True
        cur.append(v)
        for w in nbr[v]:
            cl[w] += 1

    def remove(v):
        in_s[v] = False
        cur.remove(v)
        for w in nbr[v]:
            cl[w] -= 1

    def feasible(v):
        return (not in_s[v]) and all(cl[w] < s for w in nbr[v])

    def fill(order):
        for v in order:
            if feasible(v):
                add(v)

    fill(seed_set)
    fill(rng.sample(range(m), m))
    best = cur[:]
    while len(best) < ub and time.monotonic() < deadline:
        k = rng.randint(1, 3)
        for v in rng.sample(cur, min(k, len(cur))):
            remove(v)
        order = list(range(m))
        rng.shuffle(order)
        fill(order)
        if len(cur) > len(best):
            best = cur[:]
        elif len(cur) < len(best) - 2:
            for v in cur[:]:
                remove(v)
            fill(best)
    return best


def _twin_graph(m, nbr, edges, S):
    """PG incidence plus an A-twin per v in S (to lines through v) and a B-twin per v in S (to points on v)."""
    K = len(S)
    E = list(edges)
    for t, v in enumerate(S):
        a = 2 * m + t
        b = 2 * m + K + t
        for w in nbr[v]:
            E.append((a, m + w))
            E.append((w, b))
    return 2 * m + 2 * K, E


def _arc_bound(q, s, m):
    """Known upper bound on an arc-like set S with at most s points on every line."""
    if s <= 0:
        return 0
    if s >= q + 1:
        return m
    if s == 2:
        return q + 2 if q % 2 == 0 else q + 1
    return min(m, (s - 1) * q + s)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    search_end = t0 + 0.55 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    fallback = lib.haar_graph(d, range(d))   # K_{d,d}, diameter 2
    if D == 2:
        return fallback

    best_n, best_e = fallback
    qs = [q for q in range(2, min(d - 1, 31) + 1) if lib.is_prime_power(q)]
    plan = []
    for q in qs:
        m = q * q + q + 1
        s = d - q - 1
        plan.append((2 * (m + _arc_bound(q, s, m)), q, s))
    plan.sort(reverse=True)

    try:
        for pos, (pot, q, s) in enumerate(plan):
            if pot <= best_n:
                continue
            now = time.monotonic()
            total_rem = sum(p[0] for p in plan[pos:] if p[0] > best_n)
            share = pot / total_rem if total_rem else 0.0
            deadline = now + max(0.0, search_end - now) * share

            m, nbr, edges = _pg(q)
            S = []
            if s >= 1:
                seeds = _conic_seed(q) if s >= 2 else []
                ub = _arc_bound(q, s, m)
                S = _max_arc(m, s, nbr, seeds, ub, deadline, rng)
            n, e = _twin_graph(m, nbr, edges, S)
            if n > best_n and lib.is_valid(n, e, d, D):
                best_n, best_e = n, e
    except Exception:
        pass

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, best_e
