import random
import time

import lib


# ----------------------------------------------------------------------------
# Graph helpers
# ----------------------------------------------------------------------------

def _adj(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _edges_of(adj):
    return [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]


def _bipartition(n, adj):
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


def _balls(n, adj, r):
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


def _cover(cands, ball, full, d, rng):
    """Randomized greedy cover of `full` by at most d candidates; None if it fails."""
    pool = list(cands)
    rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        mx = max(gains, default=0)
        if mx == 0:
            break
        slack = 1 if rng.random() < 0.3 else 0
        opts = [i for i, g in enumerate(gains) if g > 0 and g >= mx - slack]
        i = rng.choice(opts)
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _try_add(adj, color, d, D, rng):
    """Add one vertex on some side whose neighbourhood keeps every vertex within distance D of it.

    Mutates adj and color in place. Returns True if a vertex was added.
    """
    n = len(adj)
    if D < 2:
        return False
    ball = _balls(n, adj, D - 1)
    full = (1 << n) - 1
    sides = [0, 1]
    rng.shuffle(sides)
    for c in sides:
        cands = [s for s in range(n) if color[s] == c and len(adj[s]) < d]
        if not cands:
            continue
        chosen = _cover(cands, ball, full, d, rng)
        if chosen is None:
            continue
        v = n
        adj.append(list(chosen))
        for s in chosen:
            adj[s].append(v)
        color.append(1 - c)
        return True
    return False


def _saturate(adj, color, d, rng):
    """Join spare-degree opposite-side pairs (only adds edges, so diameter cannot get worse)."""
    n = len(adj)
    existing = set()
    for u in range(n):
        for v in adj[u]:
            if u < v:
                existing.add((u, v))
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d:
            adj[a].append(b)
            adj[b].append(a)


def _grow(n, edges, d, D, deadline, rng):
    """Greedy growth by cover vertices, then saturation."""
    adj = _adj(n, edges)
    color = _bipartition(n, adj)
    steps = 0
    while time.monotonic() < deadline and steps < 2000:
        if not _try_add(adj, color, d, D, rng):
            break
        steps += 1
    _saturate(adj, color, d, rng)
    return len(adj), _edges_of(adj)


# ----------------------------------------------------------------------------
# Large-neighbourhood search: remove a few vertices near a random centre,
# regrow with cover vertices, saturate, keep if valid and not smaller.
# ----------------------------------------------------------------------------

def _lns(n0, e0, d, D, deadline, rng, consider):
    cur_n, cur_e = n0, list(e0)
    while time.monotonic() < deadline:
        if cur_n < 4:
            break
        adj = _adj(cur_n, cur_e)

        # Pick a removal set of 1..3 vertices from a radius-2 neighbourhood.
        c0 = rng.randrange(cur_n)
        pool = [c0]
        seen = {c0}
        frontier = [c0]
        for _ in range(2):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if v not in seen:
                        seen.add(v)
                        nxt.append(v)
            frontier = nxt
            pool.extend(nxt)
        r = rng.randint(1, 3)
        R = set(rng.sample(pool, min(r, len(pool))))

        keep = [v for v in range(cur_n) if v not in R]
        mp = {v: i for i, v in enumerate(keep)}
        n1 = len(keep)
        adj1 = [[] for _ in range(n1)]
        for u in keep:
            for v in adj[u]:
                if v in mp:
                    adj1[mp[u]].append(mp[v])
        color = _bipartition(n1, adj1)

        # Try to regrow up to r+1 vertices; partial regrowth is allowed.
        for _ in range(len(R) + 1):
            if time.monotonic() >= deadline:
                break
            if not _try_add(adj1, color, d, D, rng):
                break
        _saturate(adj1, color, d, rng)

        n2 = len(adj1)
        if n2 < cur_n:
            continue
        e2 = _edges_of(adj1)
        if not lib.is_valid(n2, e2, d, D):
            continue
        cur_n, cur_e = n2, e2
        consider(n2, e2)
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best = (fb_n, fb_e)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        # Moore-optimal: PG(2, d-1) incidence graph.
        if lib.is_prime_power(d - 1):
            try:
                consider(*lib.projective_plane_incidence(d - 1))
            except Exception:
                pass
            return best

        # Araujo-Pardo & Lopez record family for d-2 a prime power.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if D >= 3:
        # Largest projective plane with q+1 <= d, grown by cover vertices.
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                try:
                    n0, e0 = lib.projective_plane_incidence(q)
                    consider(n0, e0)
                    n1, e1 = _grow(n0, e0, d, D, start + 0.25 * time_limit, rng)
                    consider(n1, e1)
                except Exception:
                    pass
                break

    # Bold step: large-neighbourhood search from the best valid graph found so far.
    base_n, base_e = best
    try:
        _lns(base_n, base_e, d, D, deadline, rng, consider)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = (fb_n, fb_e)
    return best
