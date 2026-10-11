import random
import time

import lib


# ----------------------------------------------------------------------------
# Twin blow-up with integer multiplicities (new in this version).
#
# If x is a vertex of a valid bipartite graph G with diameter <= 3 (D >= 3),
# then adding a twin x' with N(x') = N(x) keeps G valid:
#   - x' and x are at distance 2, and x' and any other vertex w are at the
#     same distance as x and w (or at distance 2 from a twin, which is fine).
#   - Twins of different vertices at distance k stay at distance <= max(k, 3).
#   - x' is on x's side, so the graph stays bipartite.
# The only limit is degree: every neighbour y of x needs spare degree.
# Twins may repeat (several twins of the same x), and twins may themselves be
# cloned later, because a twin is just another vertex with a neighbourhood.
# The parent allowed each point or line at most one new partner. Here the
# same spare slot pool is filled greedily with any number of twins, and the
# randomized greedy is restarted with different tie-breaking noise.
# ----------------------------------------------------------------------------


def _clone_run(adj0, d, rng, noise):
    """Greedy twin blow-up of the adjacency-list graph adj0 under max degree d.

    Each step picks a vertex x whose neighbours all have degree < d, preferring
    small degree (a twin of a degree-k vertex uses k slots and adds one vertex).
    Ties and near-ties are broken by random noise. Returns the new adjacency lists.
    """
    adj = [list(a) for a in adj0]
    deg = [len(a) for a in adj]
    while True:
        best, bestkey = -1, None
        for x, ax in enumerate(adj):
            if not ax or any(deg[y] >= d for y in ax):
                continue
            key = len(ax) + noise * rng.random()
            if bestkey is None or key < bestkey:
                best, bestkey = x, key
        if best < 0:
            break
        nb = list(adj[best])
        new = len(adj)
        adj.append(nb)
        deg.append(len(nb))
        for y in nb:
            adj[y].append(new)
            deg[y] += 1
    return adj


def _to_edges(adj):
    """Edge list (u, v) with u < v from adjacency lists."""
    return [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]


def _bases(d):
    """Valid diameter-3 bases: PG(2, q) incidence graphs with q + 1 <= d, plus Araujo-Lopez if d - 2 is a prime power."""
    out = []
    for q in range(2, d):
        if lib.is_prime_power(q):
            out.append(lib.projective_plane_incidence(q))
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        out.append(lib.araujo_lopez_graph(q))
    return out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D < 3:
        return best

    rng = random.Random(seed)
    bases = []
    for n0, e0 in _bases(d):
        adj0 = [[] for _ in range(n0)]
        for u, v in e0:
            adj0[u].append(v)
            adj0[v].append(u)
        bases.append(adj0)
    if not bases:
        return best

    noises = [0.0, 0.5, 2.0, 20.0]
    it = 0
    while time.monotonic() < deadline:
        adj0 = bases[it % len(bases)]
        noise = noises[(it // len(bases)) % len(noises)]
        it += 1
        adj = _clone_run(adj0, d, rng, noise)
        n = len(adj)
        if n > best_n:
            e = _to_edges(adj)
            if lib.is_valid(n, e, d, D):
                best, best_n = (n, e), n

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
