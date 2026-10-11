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


# ----------------------------------------------------------------------------
# Graph utilities on adjacency sets.
# ----------------------------------------------------------------------------

def _colors(n, adj):
    """Two-colouring of a bipartite graph given by adjacency sets."""
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


def _bad_pairs(n, adj, D):
    """Number of unordered vertex pairs at distance more than D (bitmask balls)."""
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


# ----------------------------------------------------------------------------
# New helper 1: edge-splitting vertex insertion.
# A new vertex v of colour c is joined to d opposite-colour vertices. Saturated
# targets give up one edge (w, z); z (colour c) gets a free slot.
# ----------------------------------------------------------------------------

def _insert(n, color, adj, E, d, c, rng):
    v = n
    n += 1
    adj.append(set())
    color.append(c)
    opp = [x for x in range(v) if color[x] == 1 - c]
    deficient = [x for x in opp if len(adj[x]) < d]
    full = [x for x in opp if len(adj[x]) >= d]
    rng.shuffle(deficient)
    rng.shuffle(full)
    chosen = deficient[:d]
    for w in full[:d - len(chosen)]:
        z = rng.choice(tuple(adj[w]))
        adj[w].discard(z)
        adj[z].discard(w)
        key = (w, z) if color[w] == 0 else (z, w)
        i = E.index(key)
        E[i] = E[-1]
        E.pop()
        chosen.append(w)
    for w in chosen:
        adj[v].add(w)
        adj[w].add(v)
        E.append((v, w) if c == 0 else (w, v))
    return n


def _saturate(n, color, adj, E, d, rng):
    """Greedily join deficient opposite-colour vertices in random order."""
    A = [x for x in range(n) if color[x] == 0 and len(adj[x]) < d]
    B = [x for x in range(n) if color[x] == 1 and len(adj[x]) < d]
    pairs = [(a, b) for a in A for b in B if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)
            E.append((a, b))


# ----------------------------------------------------------------------------
# New helper 2: degree-preserving two-switch annealing.
# Moves (a1,b1),(a2,b2) -> (a1,b2),(a2,b1) keep every degree and bipartiteness.
# Cost = pairs at distance > D. Metropolis acceptance, plateau moves allowed.
# ----------------------------------------------------------------------------

def _anneal(n, adj, E, D, deadline, rng):
    """Anneal until cost 0 (return True) or deadline (return False). Edits adj and E in place."""
    cost = _bad_pairs(n, adj, D)
    if cost == 0:
        return True
    m = len(E)
    if m < 2:
        return False
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    T = 1.0
    it = 0
    while cost > 0:
        it += 1
        if (it & 15) == 0:
            now = time.monotonic()
            if now >= deadline:
                return False
            T = 0.15 + 0.85 * (1.0 - (now - t0) / span)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
            continue
        adj[a1].discard(b1)
        adj[b1].discard(a1)
        adj[a2].discard(b2)
        adj[b2].discard(a2)
        adj[a1].add(b2)
        adj[b2].add(a1)
        adj[a2].add(b1)
        adj[b1].add(a2)
        new = _bad_pairs(n, adj, D)
        if new <= cost or rng.random() < math.exp(-(new - cost) / T):
            cost = new
            E[i] = (a1, b2)
            E[j] = (a2, b1)
        else:
            adj[a1].discard(b2)
            adj[b2].discard(a1)
            adj[a2].discard(b1)
            adj[b1].discard(a2)
            adj[a1].add(b1)
            adj[b1].add(a1)
            adj[a2].add(b2)
            adj[b2].add(a2)
    return True


# ----------------------------------------------------------------------------
# Growth loop: insert a vertex pair, saturate, anneal back to diameter D.
# ----------------------------------------------------------------------------

def _grow_from(n, edges, d, D, deadline, rng):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _colors(n, adj)
    E = [(u, v) if color[u] == 0 else (v, u) for u, v in edges]
    while time.monotonic() < deadline:
        cn = n
        cadj = [set(s) for s in adj]
        ccol = list(color)
        cE = list(E)
        cn = _insert(cn, ccol, cadj, cE, d, 0, rng)
        cn = _insert(cn, ccol, cadj, cE, d, 1, rng)
        _saturate(cn, ccol, cadj, cE, d, rng)
        now = time.monotonic()
        slice_end = min(deadline, now + max(2.0, (deadline - now) / 3))
        if _anneal(cn, cadj, cE, D, slice_end, rng):
            n, adj, color, E = cn, cadj, ccol, cE
    return n, list(E)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        # Araujo-Pardo & Lopez record family for d = q + 2.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Grow the best valid graph with the insertion + two-switch annealing search.
    try:
        gn, ge = _grow_from(best_n, best[1], d, D, deadline, rng)
        consider(gn, ge)
    except Exception:
        pass

    n, e = best
    if not lib.is_valid(n, e, d, D):
        return lib.haar_graph(d, range(d))
    return best
