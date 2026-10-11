import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline families: projective plane incidence, Araujo-Pardo-Lopez (D = 3),
# and K_{d,d} as the universal fallback (valid for every D >= 2).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# NEW construction for D >= 4: cyclic voltage lifts of the PG(2, d-1) incidence
# graph (a bipartite base with B = 2(q^2+q+1) vertices and degree q+1 = d).
#
# A dart (u, v, a) joins u*m+g to v*m+(g+a)%m for all g in Z_m. Lifts are
# bipartite (every base edge joins a point to a line) and simple, and each
# vertex keeps degree d. The lift has B*m vertices, so m is searched directly
# for orders beyond the record, with simulated annealing on the voltages.
# ----------------------------------------------------------------------------

def _build_adj(B, darts, volt, m):
    """Adjacency lists of the Z_m lift of the base graph with the given voltages."""
    N = B * m
    adj = [[] for _ in range(N)]
    for (u, v), a in zip(darts, volt):
        ub = u * m
        vb = v * m
        for g in range(m):
            x = ub + g
            y = vb + (g + a) % m
            adj[x].append(y)
            adj[y].append(x)
    return N, adj


def _lift_cost(N, adj, D):
    """Number of ordered (vertex, vertex) pairs at distance > D. Zero iff diameter <= D."""
    reach = [1 << x for x in range(N)]
    for _ in range(D):
        new = []
        for x in range(N):
            r = reach[x]
            for y in adj[x]:
                r |= reach[y]
            new.append(r)
        reach = new
    return sum(N - r.bit_count() for r in reach)


def _anneal_lift(B, darts, m, D, deadline, rng):
    """Anneal voltages in Z_m so the lift has diameter <= D. Returns (voltages or None, cost)."""
    E = len(darts)
    volt = [rng.randrange(m) for _ in range(E)]
    N, adj = _build_adj(B, darts, volt, m)
    cost = _lift_cost(N, adj, D)
    T = 3.0
    while cost > 0 and time.monotonic() < deadline:
        i = rng.randrange(E)
        old = volt[i]
        new = rng.randrange(m)
        if new == old:
            continue
        volt[i] = new
        N, adj = _build_adj(B, darts, volt, m)
        c2 = _lift_cost(N, adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            volt[i] = old
        T = max(0.3, T * 0.998)
    return (volt if cost == 0 else None), cost


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if D == 3:
            ar = _araujo(d)
            if ar is not None:
                consider(ar[0], ar[1])

    # Voltage-lift search over Z_m for the PG(2, d-1) base (needs d-1 a prime power).
    q = d - 1
    if D >= 4 and q >= 2 and lib.is_prime_power(q):
        B, base_edges = lib.projective_plane_incidence(q)
        darts = [(int(u), int(v)) for u, v in base_edges]
        m_cur = 12
        while m_cur >= 2 and time.monotonic() < deadline - 1.0:
            if B * m_cur <= best_n:
                m_cur -= 1
                continue
            now = time.monotonic()
            sub_deadline = now + 0.55 * (deadline - now)
            volt, _ = _anneal_lift(B, darts, m_cur, D, sub_deadline, rng)
            if volt is not None:
                triples = [(u, v, a) for (u, v), a in zip(darts, volt)]
                n, e = lib.voltage_lift(B, triples, m_cur)
                if consider(n, e):
                    m_cur += 1  # success: try a larger lift next
                    continue
            m_cur -= 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
