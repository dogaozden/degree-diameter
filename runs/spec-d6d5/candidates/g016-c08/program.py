import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Voltage lifts of the projective-plane incidence graph over cyclic groups Z_m.
#
# The base graph is PG(2, q) incidence, q = d - 1, which is d-regular bipartite
# with diameter 3. Each base edge (u, v) gets a voltage a in Z_m, so the lift
# joins u*m+g to v*m+(g+a) mod m. The lift stays simple, bipartite and d-regular.
# The voltages are annealed so that the lift has diameter <= D.
# ----------------------------------------------------------------------------

def _adj_from_darts(bn, darts, volt, m):
    adj = [[] for _ in range(bn * m)]
    for (u, v), a in zip(darts, volt):
        um, vm = u * m, v * m
        for g in range(m):
            x = um + g
            y = vm + (g + a) % m
            adj[x].append(y)
            adj[y].append(x)
    return adj


def _set_volt(adj, u, v, a_old, a_new, m):
    """Move every lifted copy of base edge (u, v) from voltage a_old to a_new."""
    um, vm = u * m, v * m
    for g in range(m):
        x = um + g
        yo = vm + (g + a_old) % m
        yn = vm + (g + a_new) % m
        adj[x].remove(yo)
        adj[yo].remove(x)
        adj[x].append(yn)
        adj[yn].append(x)


def _bad_pairs_adj(n, adj, D):
    """Ordered pairs at distance > D. Zero iff the graph has diameter <= D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _anneal_lift(bn, darts, m, D, rng, deadline):
    """Anneal voltages for the Z_m lift until diameter <= D. Returns (volt or None, cost)."""
    E = len(darts)
    n = bn * m
    volt = [rng.randrange(m) for _ in range(E)]
    adj = _adj_from_darts(bn, darts, volt, m)
    cur = _bad_pairs_adj(n, adj, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = max(0.15, 2.5 * (1.0 - (now - t0) / span))
        e = rng.randrange(E)
        u, v = darts[e]
        old = volt[e]
        new = rng.randrange(m - 1)
        if new >= old:
            new += 1
        _set_volt(adj, u, v, old, new, m)
        c2 = _bad_pairs_adj(n, adj, D)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c2
            volt[e] = new
        else:
            _set_volt(adj, u, v, new, old, m)
    return (volt if cur == 0 else None), cur


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.75 * time_limit)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        q = d - 1
        if q >= 2 and lib.is_prime_power(q):
            bn, b_edges = lib.projective_plane_incidence(q)
            consider(bn, b_edges)

            # Cyclic voltage lifts of the base incidence graph, m = 2, 3, ...
            moore = lib._moore_bound(d, D)
            m = 2
            while bn * m <= moore and time.monotonic() < deadline:
                volt = None
                while volt is None and time.monotonic() < deadline:
                    rem = deadline - time.monotonic()
                    budget_end = time.monotonic() + max(1.0, 0.5 * rem)
                    volt, _ = _anneal_lift(bn, b_edges, m, D, rng, budget_end)
                if volt is None:
                    break
                n_l, e_l = lib.voltage_lift(
                    bn, [(u, v, a) for (u, v), a in zip(b_edges, volt)], m)
                consider(n_l, e_l)
                m += 1

        # Araujo-Pardo and Lopez record family for d = q + 2 (diameter 3).
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n_a, e_a = lib.araujo_lopez_graph(d - 2)
                consider(n_a, e_a)
            except Exception:
                pass

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
