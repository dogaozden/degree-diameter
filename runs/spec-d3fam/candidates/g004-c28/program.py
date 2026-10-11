import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Graph helpers (adjacency-list level).
# ----------------------------------------------------------------------------

def _adjacency(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _bipartition(n, adj):
    """Two-colouring of the (bipartite) graph given by adjacency lists."""
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


def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _remove_vertex(n, edges, x):
    """Delete vertex x and compact labels; returns (n-1, edges)."""
    def f(v):
        return v if v < x else v - 1
    new = [(f(u), f(v)) for u, v in edges if u != x and v != x]
    return n - 1, new


# ----------------------------------------------------------------------------
# Cover-based growth and edge saturation (diameter-preserving).
# A new vertex joined to S keeps diameter <= D iff S's (D-1)-balls cover
# every vertex. Existing distances can only shrink, so growth is monotone.
# ----------------------------------------------------------------------------

def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices; None if it fails."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng, attempts):
    """Greedily add vertices whose neighbourhoods cover everything within D-1."""
    edges = list(edges)
    if D < 2:
        return n, edges
    adj = _adjacency(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(attempts):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Greedily join deficient opposite-colour vertices in random order."""
    edges = list(edges)
    adj = _adjacency(n, edges)
    existing = set()
    for u, v in edges:
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


# ----------------------------------------------------------------------------
# Randomized remove-and-regrow search. Every accepted state is verified with
# lib.is_valid, so the search can never return an invalid graph.
# ----------------------------------------------------------------------------

def _improve(n, edges, d, D, deadline, rng):
    best = (n, edges)
    cur = (n, edges)
    while time.monotonic() < deadline:
        cn, ce = cur
        if rng.random() < 0.6 or cn < 4:
            base_n, base_e = cn, ce
        else:
            x = rng.randrange(cn)
            base_n, base_e = _remove_vertex(cn, ce, x)
        n2, e2 = _extend_cover(base_n, base_e, d, D, deadline, rng, attempts=3)
        e2 = _saturate_edges(n2, e2, d, rng)
        # Plateau moves are allowed; shrinking moves are not.
        if n2 < cn:
            continue
        if not lib.is_valid(n2, e2, d, D):
            continue
        cur = (n2, e2)
        if n2 > best[0]:
            best = cur
    return best


# ----------------------------------------------------------------------------
# Seed constructions.
# ----------------------------------------------------------------------------

def _largest_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d-1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _seed_candidates(d, D):
    """Return candidate (n, edges) seeds; each is validated before use."""
    out = []
    if D == 3:
        # Moore-optimal when d-1 is a prime power.
        if lib.is_prime_power(d - 1):
            out.append(lib.projective_plane_incidence(d - 1))
        # Araujo-Pardo & Lopez record family, order 2(q^2+q+5) for d = q+2.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                out.append(lib.araujo_lopez_graph(d - 2))
            except (ValueError, StopIteration, KeyError):
                pass
        pg = _largest_pg(d)
        if pg is not None:
            out.append(pg)
    elif D >= 4 and d >= 2:
        pg = _largest_pg(d)
        if pg is not None:
            out.append(pg)
    return out


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.8 * time_limit, time_limit - 4.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    for n_c, e_c in _seed_candidates(d, D):
        consider(n_c, e_c)

    # Use the remaining budget on remove-and-regrow search from the best seed.
    if time.monotonic() < deadline:
        n_s, e_s = best
        n_i, e_i = _improve(n_s, list(e_s), d, D, deadline, rng)
        consider(n_i, e_i)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
