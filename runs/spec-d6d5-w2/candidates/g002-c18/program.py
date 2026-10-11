import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base family: projective plane incidence graphs (diameter 3, degree q+1).
# New construction for D >= 4: bi-regular voltage lifts of PG(2, q) over
# groups of order G (cyclic and small semidirect products), with simulated
# annealing on the voltages. The lift has nb * G vertices, where nb = 2(q^2+q+1).
# Left multiplication (u, x) -> (u, c x) is an automorphism, so the diameter
# is certified by checking only the fibre representatives (u, identity).
# ----------------------------------------------------------------------------

def _pg_base(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            n, edges = lib.projective_plane_incidence(q)
            return q, n, edges
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 (used only for D = 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _groups(G):
    """Groups of order G as (order, mul): cyclic plus semidirect Z_m x| Z_k."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if k == 1:
            order, mul, _ = lib.cyclic_group(G)
            out.append((order, mul))
            continue
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                try:
                    order, mul, _ = lib.semidirect_group(m, k, r)
                except ValueError:
                    continue
                if order == G:
                    out.append((order, mul))
    return out


def _mul_table(G, mul):
    """tab[g][x] = x * g in the group (identity is element 0)."""
    return [[mul(x, g) for x in range(G)] for g in range(G)]


def _adj(nb, G, darts, gs, tab):
    """Adjacency lists of the lift for the current voltages."""
    N = nb * G
    adj = [[] for _ in range(N)]
    for (u, v), g in zip(darts, gs):
        row = tab[g]
        ub, vb = u * G, v * G
        for x in range(G):
            a = ub + x
            b = vb + row[x]
            adj[a].append(b)
            adj[b].append(a)
    return adj


def _cost(N, adj, D, reps):
    """Number of (representative, vertex) pairs at distance > D. Zero means diameter <= D."""
    ball = [1 << v for v in range(N)]
    for _ in range(D):
        nxt = []
        for v in range(N):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nxt.append(x)
        ball = nxt
    return sum(N - ball[r].bit_count() for r in reps)


def _anneal(nb, G, darts, tab, D, rng, deadline):
    """Simulated annealing over one voltage per base edge. Returns (best_cost, best_voltages)."""
    N = nb * G
    reps = [u * G for u in range(nb)]
    gs = [rng.randrange(G) for _ in darts]
    cost = _cost(N, _adj(nb, G, darts, gs, tab), D, reps)
    best_c, best_g = cost, gs[:]
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while best_c > 0 and time.monotonic() < deadline:
        frac = min(1.0, (time.monotonic() - t0) / span)
        T = 1.5 * (1.0 - frac) + 0.15
        i = rng.randrange(len(darts))
        old = gs[i]
        new = rng.randrange(G)
        if new == old:
            continue
        gs[i] = new
        c2 = _cost(N, _adj(nb, G, darts, gs, tab), D, reps)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            if cost < best_c:
                best_c, best_g = cost, gs[:]
        else:
            gs[i] = old
    return best_c, best_g


def _lift_edges(nb, G, darts, gs, tab):
    """Edge list of the voltage lift (vertex u*G + x)."""
    edges = []
    for (u, v), g in zip(darts, gs):
        row = tab[g]
        ub, vb = u * G, v * G
        for x in range(G):
            edges.append((ub + x, vb + row[x]))
    return nb * G, edges


def _lift_search(nb, base_edges, d, D, g_start, deadline, rng, consider, best):
    """Search voltage lifts of order G, moving G up on success and down on failure."""
    darts = [(u, v) for u, v in base_edges]
    G = max(2, g_start)
    done = set()
    while G >= 2 and G not in done and time.monotonic() < deadline - 1.0:
        done.add(G)
        now = time.monotonic()
        sub = now + max(2.0, 0.5 * (deadline - now))
        groups = _groups(G)
        if not groups:
            G -= 1
            continue
        ok = False
        while time.monotonic() < sub - 0.5 and not ok:
            now = time.monotonic()
            order, mul = rng.choice(groups)
            tab = _mul_table(order, mul)
            dl = min(sub, now + max(3.0, 0.5 * (sub - now)))
            c, gs = _anneal(nb, order, darts, tab, D, rng, dl)
            if c == 0:
                n_, e_ = _lift_edges(nb, order, darts, gs, tab)
                if lib.is_valid(n_, e_, d, D):
                    consider(n_, e_)
                    ok = True
        if ok:
            G += 1
        else:
            G -= 1


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n = 2 * d
    best_e = [(i, d + j) for i in range(d) for j in range(d)]
    if not lib.is_valid(best_n, best_e, d, D):
        return 1, []
    best = [best_n, best_e]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    if D >= 3:
        try:
            pg = _pg_base(d)
        except Exception:
            pg = None
        if pg is not None:
            q, nb, be = pg
            consider(nb, be)
            if D == 3:
                ar = _araujo(d)
                if ar is not None:
                    consider(ar[0], ar[1])
            else:
                g_start = max(2, int(0.5 * lib.moore_bound(d, D)) // nb)
                try:
                    _lift_search(nb, be, d, D, g_start, deadline, rng, consider, best)
                except Exception:
                    pass

    n_out, e_out = best[0], best[1]
    if not lib.is_valid(n_out, e_out, d, D):
        n_out = 2 * d
        e_out = [(i, d + j) for i in range(d) for j in range(d)]
        if not lib.is_valid(n_out, e_out, d, D):
            return 1, []
    return n_out, e_out
