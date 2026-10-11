import itertools
import math
import random
import time
from collections import deque

import lib


# ----------------------------------------------------------------------------
# Classical bases (kept as a secondary construction family).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared helpers.
# ----------------------------------------------------------------------------

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


def _greedy_cover(cands, ball, full, d, rng, randomize):
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


def _extend_cover(n, edges, d, D, deadline, rng):
    """Add vertices whose neighbourhoods cover all vertices within distance D-1 of the rest."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
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
            for attempt in range(60):
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
    """Greedily join deficient opposite-side vertices. Keeps degrees <= d."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
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


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(6):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _duplicate_twins(n, edges, d, rng):
    """Add non-adjacent twins (same neighbourhood) while neighbours have spare degree."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    changed = True
    while changed:
        changed = False
        order = list(range(len(adj)))
        rng.shuffle(order)
        for v in order:
            nb = adj[v]
            if not nb or len(nb) > d:
                continue
            if any(len(adj[u]) >= d for u in nb):
                continue
            w = len(adj)
            adj.append(set(nb))
            for u in nb:
                adj[u].add(w)
            changed = True
    out = [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]
    return len(adj), out


def _trial(base_n, base_e, d, D, rng, deadline):
    """One pipeline: twin duplication mixed with cover growth and saturation."""
    mode = rng.randrange(2)
    n, e = base_n, list(base_e)
    if mode == 0:
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    else:
        n, e = _grow(n, e, d, D, deadline, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
    return n, e


# ----------------------------------------------------------------------------
# NEW CONSTRUCTION: random voltage lifts over small (possibly non-abelian) groups.
#
# Base graph: s A-vertices and s B-vertices, each of degree d (random darts).
# Group G of order N acts regularly on each fibre, so the lift has 2*s*N vertices.
# Diameter only needs checking by BFS from the identity of each fibre, because G
# acts transitively on every fibre (left multiplication is an automorphism).
# Degree is at most d by construction, and the graph is bipartite (A to B only).
# ----------------------------------------------------------------------------

def _bfs_ok(adj, sources, n, D):
    """True if every BFS from each source reaches all n vertices within distance D."""
    for s in sources:
        dist = [-1] * n
        dist[s] = 0
        dq = deque([s])
        cnt = 1
        while dq:
            u = dq.popleft()
            du = dist[u]
            if du >= D:
                continue
            for v in adj[u]:
                if dist[v] < 0:
                    dist[v] = du + 1
                    cnt += 1
                    dq.append(v)
        if cnt != n:
            return False
    return True


def _random_group(N, rng):
    """Multiplication of a random group of order N: cyclic, or Z_m x|_r Z_k (identity code 0)."""
    divs = [k for k in range(1, N + 1) if N % k == 0]
    k = rng.choice(divs)
    m = N // k
    if k == 1:
        _, mul, _ = lib.cyclic_group(m)
        return mul
    r = 1
    if m > 1:
        for _ in range(60):
            cand = rng.randrange(1, m)
            if math.gcd(cand, m) == 1 and pow(cand, k, m) == 1 % m:
                r = cand
                break
    _, mul, _ = lib.semidirect_group(m, k, r)
    return mul


def _lift_once(s, d, N, mul, rng):
    """Random base with s+s vertices, each degree d; return the group lift (n, edges)."""
    slots = [j for j in range(s) for _ in range(d)]
    rng.shuffle(slots)
    darts = []
    for i in range(s):
        for t in range(d):
            darts.append((i, s + slots[i * d + t], rng.randrange(N)))
    return lib.group_lift(2 * s, darts, N, mul)


def _lift_search(d, D, deadline, rng, state, consider):
    """Random voltage-lift search for valid graphs larger than state['n']."""
    moore = lib.moore_bound(d, D)
    while time.monotonic() < deadline:
        options = []
        for s in (1, 2, 3):
            lo = state["n"] // (2 * s) + 1
            hi = moore // (2 * s)
            if lo <= hi:
                options.append((s, lo, hi))
        if not options:
            break
        s, lo, hi = rng.choice(options)
        N = rng.randint(lo, hi)
        mul = _random_group(N, rng)
        n, edges = _lift_once(s, d, N, mul, rng)
        if n <= state["n"]:
            continue
        adj = [[] for _ in range(n)]
        for u, v in edges:
            adj[u].append(v)
            adj[v].append(u)
        if not _bfs_ok(adj, [u * N for u in range(2 * s)], n, D):
            continue
        if consider(n, edges):
            n2, e2 = _grow(n, edges, d, D, deadline, rng)
            consider(n2, e2)


# ----------------------------------------------------------------------------
# Driver.
#   1. Random voltage lifts over small groups (new construction).
#   2. Grow the best lift with cover vertices.
#   3. Structured base (W(q) or PG(2,q)) grown, with twin trials.
#   4. Another lift search from the best graph.
# Every candidate passes lib.is_valid before it is kept. K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = 0.85 * time_limit

    def at(f):
        return start + f * T

    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    n0, e0 = lib.haar_graph(d, range(d))
    state = {"n": n0, "e": [tuple(x) for x in e0]}

    def consider(n, e):
        if n > state["n"] and lib.is_valid(n, e, d, D):
            state["n"], state["e"] = n, [tuple(x) for x in e]
            return True
        return False

    moore = lib.moore_bound(d, D)

    def done():
        return state["n"] >= moore

    # Phase 1: voltage-lift search over small groups.
    if D >= 2 and not done():
        try:
            _lift_search(d, D, at(0.55), rng, state, consider)
        except Exception:
            pass

    # Phase 2: grow the best lift.
    if D >= 2 and not done() and time.monotonic() < at(0.62):
        try:
            n2, e2 = _grow(state["n"], state["e"], d, D, at(0.62), rng)
            consider(n2, e2)
        except Exception:
            pass

    # Phase 3: structured base, growth, and twin trials.
    if D >= 2 and not done() and time.monotonic() < at(0.9):
        try:
            base = _best_gq(d) if D >= 4 else None
            if base is None:
                base = _best_pg(d)
            if base is not None:
                bn, be = base
                n1, e1 = _grow(bn, be, d, D, at(0.72), rng)
                consider(n1, e1)
                base_n, base_e = n1, e1
            else:
                base_n, base_e = state["n"], state["e"]
            while time.monotonic() < at(0.9) and not done():
                n, e = _trial(base_n, base_e, d, D, rng, at(0.9))
                consider(n, e)
        except Exception:
            pass

    # Phase 4: lift search again (may improve on the structured result).
    if D >= 2 and not done() and time.monotonic() < at(1.0):
        try:
            _lift_search(d, D, at(1.0), rng, state, consider)
        except Exception:
            pass

    if not lib.is_valid(state["n"], state["e"], d, D):
        return lib.haar_graph(d, range(d))
    return state["n"], list(state["e"])
