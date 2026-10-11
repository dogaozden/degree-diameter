import math
import random
import time

import lib


def _cost(h, edges, D):
    """Number of unordered vertex pairs at distance > D.

    Internal labels: A-vertex a is a in [0, h); B-vertex b is h + b in [h, 2h).
    """
    n = 2 * h
    adj = [[] for _ in range(n)]
    for a, b in edges:
        adj[a].append(h + b)
        adj[h + b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _to_pairs(h, edges):
    """Convert internal (a, b) edges to output labels 0..2h-1."""
    return [(a, h + b) for a, b in edges]


def _circulant(h, d):
    """d-regular simple bipartite graph on h + h vertices (requires h >= d)."""
    return [(i, (i + s) % h) for i in range(h) for s in range(d)]


def _pg_start(d):
    """Incidence graph of PG(2, d-1) when d-1 is a prime power (regular, diameter 3)."""
    q = d - 1
    if q < 2 or not lib.is_prime_power(q):
        return None
    n2, E = lib.projective_plane_incidence(q)
    m = n2 // 2
    return m, [(u, v - m) for u, v in E]


def _insert(h, edges, d, rng):
    """Add one new A vertex and one new B vertex, keeping every degree equal to d.

    Pick d edges (a_i, b_i) forming a matching. Remove them. Add (a_i, H) and
    (H, b_i), where H = h is the new index on both sides. Old degrees are unchanged
    and the two new vertices get degree d.
    Returns (h + 1, new_edges), or None if no matching of size d was found.
    """
    idx = list(range(len(edges)))
    rng.shuffle(idx)
    used_a, used_b = set(), set()
    chosen = []
    for i in idx:
        a, b = edges[i]
        if a in used_a or b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        chosen.append(i)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return None
    cs = set(chosen)
    new_edges = [e for i, e in enumerate(edges) if i not in cs]
    H = h
    for i in chosen:
        a, b = edges[i]
        new_edges.append((a, H))
        new_edges.append((H, b))
    return h + 1, new_edges


def _anneal(h, edges, D, rng, deadline, T0, T1):
    """Simulated annealing over double edge switches (a1,b1),(a2,b2) -> (a1,b2),(a2,b1).

    Switches keep the graph bipartite and d-regular. Mutates `edges` in place.
    Returns the final cost (0 means diameter <= D).
    """
    eset = set(edges)
    cost = _cost(h, edges, D)
    if cost == 0:
        return 0
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    m = len(edges)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** ((now - t0) / span)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = edges[i]
        a2, b2 = edges[j]
        if a1 == a2 or b1 == b2:
            continue
        e1 = (a1, b2)
        e2 = (a2, b1)
        if e1 in eset or e2 in eset:
            continue
        edges[i] = e1
        edges[j] = e2
        eset.discard((a1, b1))
        eset.discard((a2, b2))
        eset.add(e1)
        eset.add(e2)
        c2 = _cost(h, edges, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            edges[i] = (a1, b1)
            edges[j] = (a2, b2)
            eset.discard(e1)
            eset.discard(e2)
            eset.add((a1, b1))
            eset.add((a2, b2))
    return cost


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best_n = 2 * d
    best_edges = [(i, d + j) for i in range(d) for j in range(d)]

    def consider(n, e):
        nonlocal best_n, best_edges
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_edges = n, e

    # Projective-plane incidence graph with q = largest prime power <= d-1 (diameter 3).
    if D >= 3 and d >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break

    # Starting regular state: PG(2, d-1) if it is d-regular, otherwise a circulant.
    pgs = _pg_start(d) if D >= 3 else None
    if pgs is not None:
        h, edges = pgs
    else:
        h = d
        edges = _circulant(h, d)

    if _cost(h, edges, D) != 0:
        h = d
        edges = _circulant(h, d)
    consider(2 * h, _to_pairs(h, edges))

    # Growth loop: insert a vertex pair, then anneal the switches until the diameter
    # is <= D again. A failed slice keeps the last valid state and retries with a
    # fresh insertion and a longer slice.
    valid_h, valid_edges = h, list(edges)
    fails = 0
    while fails < 12:
        left = deadline - time.monotonic()
        if left <= 0.3:
            break
        cand = _insert(valid_h, valid_edges, d, rng)
        if cand is None:
            fails += 1
            continue
        h2, e2 = cand
        slice_end = time.monotonic() + min(left, 2.0 * (1.5 ** fails))
        c = _anneal(h2, e2, D, rng, slice_end, T0=2.0, T1=0.1)
        if c == 0:
            valid_h, valid_edges = h2, e2
            consider(2 * h2, _to_pairs(h2, e2))
            fails = 0
        else:
            fails += 1

    if not lib.is_valid(best_n, best_edges, d, D):
        best_n = 2 * d
        best_edges = [(i, d + j) for i in range(d) for j in range(d)]
    return best_n, list(best_edges)
