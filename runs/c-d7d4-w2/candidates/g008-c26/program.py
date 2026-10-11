import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured bases.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
    """
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
    for q in range(d - 1, 1, -1):
        if q <= 8 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Shared helpers on set-adjacency graphs.
# ----------------------------------------------------------------------------

def _balls(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        nb = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nb.append(x)
        ball = nb
    return ball


def _bad_count(n, adj, D):
    """Unordered pairs at distance > D (unreachable pairs included)."""
    ball = _balls(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _colour(n, adj):
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        st = [s]
        while st:
            u = st.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    st.append(v)
    return col


def _cover(cands, ball, full, d, rng):
    """Greedy cover of `full` by at most d candidate balls. Returns list or None."""
    pool = list(cands)
    rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        best = -1
        bg = 0
        for s in pool:
            g = (ball[s] & ~covered).bit_count()
            if g > bg:
                bg = g
                best = s
        if best < 0:
            break
        chosen.append(best)
        pool.remove(best)
        covered |= ball[best]
    return chosen if covered == full else None


def _cover_grow(n, edges, d, D, deadline, rng):
    """Add vertices whose neighbourhoods cover everything within distance D-1.

    A new vertex v adjacent to such a cover is within distance D of every vertex,
    and no other distance gets worse, so validity is kept.
    """
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _colour(n, adj)
    while time.monotonic() < deadline:
        m = len(adj)
        ball = _balls(m, adj, D - 1)
        full = (1 << m) - 1
        sides = [0, 1]
        rng.shuffle(sides)
        added = False
        for c in sides:
            cands = [s for s in range(m) if col[s] == c and len(adj[s]) < d]
            chosen = _cover(cands, ball, full, d, rng)
            if chosen:
                v = m
                adj.append(set())
                col.append(1 - c)
                for s in chosen:
                    adj[s].add(v)
                    adj[v].add(s)
                added = True
                break
        if not added:
            break
    return len(adj), [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]


def _saturate(n, edges, d, rng):
    """Add cross-side edges between deficient vertices. Only shortens distances."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _colour(n, adj)
    left = [v for v in range(n) if col[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if col[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _grow_all(n, edges, d, D, deadline, rng):
    cur_n, cur_e = n, list(edges)
    for _ in range(6):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _cover_grow(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Voltage lifts over small (possibly non-abelian) groups.
#
# Base: s vertices on side A and s on side B, d layers. Layer l is a permutation
# pl of {0..s-1} (A index -> B index) with a group voltage g[l][a]. The lift has
# vertices (a, x) and (s+b, y) for x, y in the group, and joins (a, x) to
# (s+pl[a], x*g). Every vertex then has degree <= d and the graph is bipartite.
# A random start is hill-climbed (voltage changes and permutation swaps) toward
# zero pairs at distance > D. This is a different search space from the
# double-edge-switch annealing of the greedy pipeline.
# ----------------------------------------------------------------------------

_GROUP_CACHE = {}


def _group_candidates(G):
    if G in _GROUP_CACHE:
        return _GROUP_CACHE[G]
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        for r in range(max(1, m)):
            try:
                lib.semidirect_group(m, k, r)
            except ValueError:
                continue
            out.append((m, k, r))
    _GROUP_CACHE[G] = out
    return out


def _mul_table(key):
    m, k, r = key
    order, mul, _ = lib.semidirect_group(m, k, r)
    return [[mul(x, g) for g in range(order)] for x in range(order)]


def _state_adj(s, G, mt, d, perms, volts):
    n = 2 * s * G
    adj = [set() for _ in range(n)]
    for l in range(d):
        pl = perms[l]
        vl = volts[l]
        for a in range(s):
            t = s + pl[a]
            g = vl[a]
            for x in range(G):
                u = a * G + x
                v = t * G + mt[x][g]
                adj[u].add(v)
                adj[v].add(u)
    return n, adj


def _climb(s, G, mt, d, D, rng, iters, until):
    perms = [rng.sample(range(s), s) for _ in range(d)]
    volts = [[rng.randrange(G) for _ in range(s)] for _ in range(d)]
    n, adj = _state_adj(s, G, mt, d, perms, volts)
    cur = _bad_count(n, adj, D)
    for _ in range(iters):
        if cur == 0 or time.monotonic() > until:
            break
        l = rng.randrange(d)
        a = rng.randrange(s)
        if s > 1 and rng.random() < 0.3:
            b = rng.randrange(s)
            if b == a:
                continue
            pl = perms[l]
            pl[a], pl[b] = pl[b], pl[a]
            n, adj = _state_adj(s, G, mt, d, perms, volts)
            new = _bad_count(n, adj, D)
            if new <= cur or (new == cur + 1 and rng.random() < 0.05):
                cur = new
            else:
                pl[a], pl[b] = pl[b], pl[a]
        else:
            old = volts[l][a]
            volts[l][a] = rng.randrange(G)
            n, adj = _state_adj(s, G, mt, d, perms, volts)
            new = _bad_count(n, adj, D)
            if new <= cur or (new == cur + 1 and rng.random() < 0.05):
                cur = new
            else:
                volts[l][a] = old
    return (perms, volts) if cur == 0 else None


def _lift_search(d, D, cap, deadline, rng, get_best, consider):
    tables = {}
    while time.monotonic() < deadline:
        bn = get_best()
        if bn >= cap:
            break
        s = rng.choice((1, 1, 2, 2, 3, 4, 5, 6))
        G = bn // (2 * s) + 1 + rng.randrange(3)  # aim just above the current best
        if 2 * s * G > cap:
            continue
        cands = _group_candidates(G)
        if not cands:
            continue
        key = rng.choice(cands)
        if key not in tables:
            tables[key] = _mul_table(key)
        mt = tables[key]
        until = min(deadline, time.monotonic() + 6.0)
        res = _climb(s, G, mt, d, D, rng, 5000, until)
        if res is not None:
            perms, volts = res
            n, adj = _state_adj(s, G, mt, d, perms, volts)
            e = [(u, v) for u in range(n) for v in adj[u] if u < v]
            consider(n, e)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2 and optimal at D = 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    cap = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    def get_best():
        return best_n

    if best_n < cap and D == 3:
        base = _best_pg(d)
        if base is not None:
            consider(base[0], base[1])
        if d >= 5 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except ValueError:
                pass

    if best_n < cap and D == 4:
        base = _best_gq(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            n1, e1 = _grow_all(n0, e0, d, D, start + 0.2 * time_limit, rng)
            consider(n1, e1)

    # Main improver: voltage-lift hill climbing over small groups.
    if best_n < cap and time.monotonic() < deadline:
        _lift_search(d, D, cap, deadline, rng, get_best, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
