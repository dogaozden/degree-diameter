import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions (all diameter 3, validated before use).
# ----------------------------------------------------------------------------

def _pg_base(d):
    """Incidence graph of PG(2, q), q the largest prime power with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _al_base(d):
    """Araujo-Pardo & Lopez graph for the largest prime power q with q + 2 <= d."""
    for q in range(d - 2, 2, -1):
        if lib.is_prime_power(q):
            try:
                return lib.araujo_lopez_graph(q)
            except Exception:
                return None
    return None


# ----------------------------------------------------------------------------
# Bitmask balls, greedy covers, and a plateau search over valid graphs.
#
# Invariant: the working graph is always valid (bipartite, max degree <= d,
# diameter <= D). Growth adds a vertex whose neighbourhood covers every vertex
# within distance D-1 of the existing graph; this keeps diameter <= D. Moves
# are degree-preserving 2-switches accepted only when diameter stays <= D.
# ----------------------------------------------------------------------------

def _balls(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return ball


def _greedy_cover(cands, ball, full, d, rng):
    """Randomized greedy cover of `full` by at most d candidates; None on failure."""
    pool = list(cands)
    rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        best_g, best_i = 0, -1
        for i, t in enumerate(pool):
            g = (ball[t] & ~covered).bit_count()
            if g > best_g or (g == best_g and g > 0 and rng.random() < 0.3):
                best_g, best_i = g, i
        if best_i < 0:
            break
        t = pool.pop(best_i)
        chosen.append(t)
        covered |= ball[t]
    return chosen if covered == full else None


def _two_color(n, adj):
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


def _saturate(n, adj, color, elist, d, rng):
    """Add opposite-side edges between deficient vertices (distances only shrink)."""
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    rng.shuffle(left)
    rng.shuffle(right)
    for a in left:
        for b in right:
            if len(adj[a]) >= d:
                break
            if len(adj[b]) < d and b not in adj[a]:
                adj[a].add(b)
                adj[b].add(a)
                elist.append((a, b))


def _grow_step(n, adj, color, elist, d, D, rng):
    """Try to add one vertex covering all vertices within D-1. Returns new n or None."""
    ball = _balls(n, [list(s) for s in adj], D - 1)
    full = (1 << n) - 1
    sides = [0, 1]
    rng.shuffle(sides)
    for c in sides:
        cands = [t for t in range(n) if color[t] == 1 - c and len(adj[t]) < d]
        if not cands:
            continue
        chosen = None
        for _ in range(4):
            chosen = _greedy_cover(cands, ball, full, d, rng)
            if chosen:
                break
        if chosen:
            v = n
            adj.append(set())
            color.append(c)
            for t in chosen:
                adj[t].add(v)
                adj[v].add(t)
                elist.append((t, v) if c == 1 else (v, t))
            _saturate(n + 1, adj, color, elist, d, rng)
            return n + 1
    return None


def _search(n, edges, d, D, deadline, rng):
    """Plateau search: grow whenever possible, otherwise random valid 2-switches."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _two_color(n, adj)
    elist = [(u, v) if color[u] == 0 else (v, u) for u, v in edges]
    n_cur = n

    while time.monotonic() < deadline:
        # Degree-preserving switches cannot create spare capacity, so stop
        # once every vertex is saturated.
        if not any(len(adj[v]) < d for v in range(n_cur)):
            break

        r = _grow_step(n_cur, adj, color, elist, d, D, rng)
        if r is not None:
            n_cur = r
            continue

        if len(elist) < 2:
            break
        i = rng.randrange(len(elist))
        j = rng.randrange(len(elist))
        if i == j:
            continue
        a1, b1 = elist[i]
        a2, b2 = elist[j]
        if b2 in adj[a1] or b1 in adj[a2]:
            continue

        # Apply 2-switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1).
        adj[a1].discard(b1)
        adj[b1].discard(a1)
        adj[a2].discard(b2)
        adj[b2].discard(a2)
        adj[a1].add(b2)
        adj[b2].add(a1)
        adj[a2].add(b1)
        adj[b1].add(a2)
        elist[i] = (a1, b2)
        elist[j] = (a2, b1)

        if lib.bad_pairs(n_cur, elist, D) != 0:
            # Revert.
            adj[a1].discard(b2)
            adj[b2].discard(a1)
            adj[a2].discard(b1)
            adj[b1].discard(a2)
            adj[a1].add(b1)
            adj[b1].add(a1)
            adj[a2].add(b2)
            adj[b2].add(a2)
            elist[i] = (a1, b1)
            elist[j] = (a2, b2)

    return n_cur, list(elist)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        bases = []
        for b in (_pg_base(d), _al_base(d)):
            if b is not None and lib.is_valid(b[0], b[1], d, D):
                bases.append(b)
                consider(b[0], b[1])

        if bases:
            share = (deadline - time.monotonic()) / len(bases)
            for idx, (n0, e0) in enumerate(bases):
                end = min(deadline, time.monotonic() + share)
                n2, e2 = _search(n0, e0, d, D, end, random.Random(seed * 131 + idx))
                consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
