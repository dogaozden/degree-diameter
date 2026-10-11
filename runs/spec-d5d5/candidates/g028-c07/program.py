import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction families:
#   * D = 3: projective-plane incidence graphs and the Araujo-Pardo-Lopez
#     extension (both via lib), used as baselines.
#   * D >= 3: a growth-and-repair search. Start from K_{d,d}. Each step adds one
#     vertex on each side and rewires d disjoint edges through them, which keeps
#     the graph bipartite and d-regular. Then simulated annealing over 2-switches
#     (degree- and bipartition-preserving) drives the number of vertex pairs at
#     distance > D to zero. The current valid graph is kept as the fallback.
# ----------------------------------------------------------------------------

MAX_TOTAL_N = 1200  # cap on total vertices for the search (keeps each cost evaluation cheap)


def _bad(N, edges, D):
    """Number of unordered vertex pairs at distance > D. A is 0..N-1, B is N..2N-1."""
    n2 = 2 * N
    nbr = [[] for _ in range(n2)]
    for a, b in edges:
        nbr[a].append(N + b)
        nbr[N + b].append(a)
    reach = [1 << v for v in range(n2)]
    for _ in range(D):
        new = []
        for v in range(n2):
            x = reach[v]
            for u in nbr[v]:
                x |= reach[u]
            new.append(x)
        reach = new
    return sum(n2 - r.bit_count() for r in reach) // 2


def _anneal(N, edges, D, rng, deadline, T0=2.0, T1=0.15):
    """Annealed 2-switch repair. Mutates `edges` in place; True iff diameter <= D afterwards."""
    E = len(edges)
    eset = set(edges)
    cost = _bad(N, edges, D)
    start = time.monotonic()
    span = max(1e-6, deadline - start)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - start) / span)
        i = rng.randrange(E)
        j = rng.randrange(E)
        if i == j:
            continue
        a1, b1 = edges[i]
        a2, b2 = edges[j]
        if a1 == a2 or b1 == b2:
            continue
        n1 = (a1, b2)
        n2 = (a2, b1)
        if n1 in eset or n2 in eset:
            continue
        edges[i] = n1
        edges[j] = n2
        eset.discard((a1, b1))
        eset.discard((a2, b2))
        eset.add(n1)
        eset.add(n2)
        c2 = _bad(N, edges, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            edges[i] = (a1, b1)
            edges[j] = (a2, b2)
            eset.discard(n1)
            eset.discard(n2)
            eset.add((a1, b1))
            eset.add((a2, b2))
    return cost == 0


def _grow_one(N, edges, d, rng):
    """Add one vertex per side by rewiring d edges with distinct endpoints through the new pair.

    Returns (N+1, new_edges) or None if no suitable matching was found.
    """
    if len(edges) < d:
        return None
    for _ in range(30):
        idx = list(range(len(edges)))
        rng.shuffle(idx)
        usedA, usedB, chosen = set(), set(), []
        for i in idx:
            a, b = edges[i]
            if a in usedA or b in usedB:
                continue
            chosen.append(i)
            usedA.add(a)
            usedB.add(b)
            if len(chosen) == d:
                break
        if len(chosen) == d:
            chosen_set = set(chosen)
            xs = [edges[i][0] for i in chosen]
            ys = [edges[i][1] for i in chosen]
            new_edges = [e for k, e in enumerate(edges) if k not in chosen_set]
            new_edges += [(N, y) for y in ys]   # new A-vertex N joins the freed B-ends
            new_edges += [(x, N) for x in xs]   # new B-vertex N joins the freed A-ends
            return N + 1, new_edges
    return None


def _search(d, D, rng, deadline):
    """Growth-and-repair search. Returns (N, edges) with edges as (a, b) index pairs, valid."""
    N = d
    edges = [(a, b) for a in range(d) for b in range(d)]  # K_{d,d}: valid for any D >= 2
    best = (N, list(edges))
    moore = lib._moore_bound(d, D)
    while time.monotonic() < deadline:
        if 2 * (N + 1) > moore or 2 * (N + 1) > MAX_TOTAL_N:
            break
        g = _grow_one(N, edges, d, rng)
        if g is None:
            break
        N2, e2 = g
        remaining = deadline - time.monotonic()
        stage_end = time.monotonic() + max(1.0, 0.4 * remaining)
        stage_end = min(stage_end, deadline)
        if _anneal(N2, e2, D, rng, stage_end):
            N, edges = N2, e2
            best = (N, list(edges))
        else:
            break
    return best


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # even cycle C_{2D}: bipartite, diameter D, Moore-optimal for d = 2
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    rng = random.Random(seed)

    # Structured baselines for D = 3.
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n_pg, e_pg = lib.projective_plane_incidence(q)
                consider(n_pg, e_pg)
                break
        q2 = d - 2
        if q2 >= 3 and lib.is_prime_power(q2):
            try:
                n_al, e_al = lib.araujo_lopez_graph(q2)
                consider(n_al, e_al)
            except ValueError:
                pass

    # Main search: growth-and-repair from K_{d,d}, using most of the budget.
    if time.monotonic() < deadline:
        N, idx_edges = _search(d, D, rng, deadline)
        if N > 0:
            e = [(a, N + b) for a, b in idx_edges]
            consider(2 * N, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best

