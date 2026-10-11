import itertools
import math
import random
import time

import lib

FRAC = 0.85          # fraction of time_limit used for searching
MARGIN = 2.5         # seconds kept in reserve
PAIR_SLICE = 4.0     # seconds per rewire-growth attempt
VERT_SLICE = 8.0     # seconds per vertex-addition attempt
VERT_ITERS = 1500    # annealing steps per vertex-addition attempt


# ---------------------------------------------------------------- graph helpers

def _adj_lists(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


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
    reach = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        if new == reach:
            break
        reach = new
    return reach


def _bad_pairs(n, adj, D):
    """Number of unordered pairs at distance > D (unreachable pairs count)."""
    return sum(n - x.bit_count() for x in _balls(n, adj, D)) // 2


# ---------------------------------------------------------------- base constructions

def _best_pg(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            try:
                return _gq_w(q)
            except Exception:
                return None
    return None


# ---------------------------------------------------------------- rewire growth
# Remove a matching R of d oriented edges (u on side 0, v on side 1).
# Add x (side 0) joined to all v's and y (side 1) joined to all u's.
# Every degree is preserved and two vertices are added.

def _random_matching(Eo, d, rng):
    pool = list(Eo)
    rng.shuffle(pool)
    used = set()
    R = []
    for u, v in pool:
        if u in used or v in used:
            continue
        R.append((u, v))
        used.add(u)
        used.add(v)
        if len(R) == d:
            return R
    return None


def _rewire_edges(n, Eo, R):
    Rk = {(min(u, v), max(u, v)) for u, v in R}
    out = [e for e in Eo if (min(e[0], e[1]), max(e[0], e[1])) not in Rk]
    x, y = n, n + 1
    for u, v in R:
        out.append((x, v))
        out.append((u, y))
    return n + 2, out


def _rewire_cost(n, Eo, R, D):
    Rk = {(min(u, v), max(u, v)) for u, v in R}
    adj = [[] for _ in range(n + 2)]
    for u, v in Eo:
        if (min(u, v), max(u, v)) in Rk:
            continue
        adj[u].append(v)
        adj[v].append(u)
    x, y = n, n + 1
    for u, v in R:
        adj[x].append(v)
        adj[v].append(x)
        adj[u].append(y)
        adj[y].append(u)
    return _bad_pairs(n + 2, adj, D)


def _pair_search(n, E, d, D, deadline, rng):
    """Anneal a matching so the rewired graph has diameter <= D. Returns (n+2, edges) or None."""
    adj = _adj_lists(n, E)
    col = _bipartition(n, adj)
    Eo = [(u, v) if col[u] == 0 else (v, u) for u, v in E]
    if len(Eo) < d:
        return None
    R = _random_matching(Eo, d, rng)
    if R is None:
        return None
    c = _rewire_cost(n, Eo, R, D)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    while c > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t0) / span
        T = 1.0 * (0.05 ** frac)
        i = rng.randrange(d)
        cand = Eo[rng.randrange(len(Eo))]
        used = set()
        for j, (a, b) in enumerate(R):
            if j != i:
                used.add(a)
                used.add(b)
        if cand[0] in used or cand[1] in used:
            continue
        newR = list(R)
        newR[i] = cand
        c2 = _rewire_cost(n, Eo, newR, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            R, c = newR, c2
    if c == 0:
        return _rewire_edges(n, Eo, R)
    return None


# ---------------------------------------------------------------- vertex addition
# Add one vertex joined to a diameter-covering set of opposite-side vertices,
# then anneal double-edge swaps until the diameter bound holds again.

def _pick_neighbours(n, adj, color, c, d, D, rng):
    other = [v for v in range(n) if color[v] == 1 - c]
    if len(other) < d:
        return None
    balls = _balls(n, adj, D - 1)
    full = (1 << n) - 1
    covered, chosen = 0, []
    cand = other[:]
    rng.shuffle(cand)
    while covered != full and len(chosen) < d and cand:
        best_u, best_g = -1, 0
        for u in cand:
            g = (balls[u] & ~covered).bit_count()
            if g > best_g:
                best_u, best_g = u, g
        if best_u < 0:
            break
        chosen.append(best_u)
        covered |= balls[best_u]
        cand.remove(best_u)
    chosen_set = set(chosen)
    rest = [v for v in other if v not in chosen_set]
    rng.shuffle(rest)
    chosen += rest[: d - len(chosen)]
    return chosen


def _swap(adj, side0, rng):
    a1 = rng.choice(side0)
    if not adj[a1]:
        return None
    b1 = rng.choice(tuple(adj[a1]))
    a2 = rng.choice(side0)
    if a2 == a1 or not adj[a2]:
        return None
    b2 = rng.choice(tuple(adj[a2]))
    if b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
        return None
    adj[a1].remove(b1); adj[b1].remove(a1)
    adj[a2].remove(b2); adj[b2].remove(a2)
    adj[a1].add(b2); adj[b2].add(a1)
    adj[a2].add(b1); adj[b1].add(a2)
    return (a1, b1, a2, b2)


def _unswap(adj, mv):
    a1, b1, a2, b2 = mv
    adj[a1].remove(b2); adj[b2].remove(a1)
    adj[a2].remove(b1); adj[b1].remove(a2)
    adj[a1].add(b1); adj[b1].add(a1)
    adj[a2].add(b2); adj[b2].add(a2)


def _augment(n, adj, color, d, rng):
    """Join deficient opposite-colour vertices. Adding edges never breaks the diameter bound."""
    d0 = [u for u in range(n) if color[u] == 0 and len(adj[u]) < d]
    d1 = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    if not d0 or not d1:
        return
    rng.shuffle(d0)
    for u in d0:
        if len(adj[u]) >= d:
            continue
        for v in d1:
            if len(adj[v]) < d and v not in adj[u]:
                adj[u].add(v)
                adj[v].add(u)
                if len(adj[u]) >= d:
                    break


def _vertex_attempt(n, adj, color, d, D, rng, deadline, iters):
    adj = [set(s) for s in adj]
    color = list(color)
    c = rng.randrange(2)
    nb = _pick_neighbours(n, adj, color, c, d, D, rng)
    if nb is None:
        return None
    for u in nb:
        if len(adj[u]) >= d:
            w = rng.choice(tuple(adj[u]))
            adj[u].discard(w)
            adj[w].discard(u)
    x = n
    adj.append(set())
    color.append(c)
    n += 1
    for u in nb:
        adj[x].add(u)
        adj[u].add(x)

    side0 = [v for v in range(n) if color[v] == 0]
    cost = _bad_pairs(n, adj, D)
    for it in range(iters):
        if cost == 0:
            break
        if time.monotonic() > deadline:
            return None
        mv = _swap(adj, side0, rng)
        if mv is None:
            continue
        new = _bad_pairs(n, adj, D)
        delta = new - cost
        temp = 1.5 * (1.0 - it / iters) + 0.05
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cost = new
        else:
            _unswap(adj, mv)
    if cost != 0:
        return None
    _augment(n, adj, color, d, rng)
    return n, adj, color


# ---------------------------------------------------------------- driver

def _search(n0, e0, d, D, deadline, rng):
    """Alternate rewire growth and vertex addition; restart from the best graph after repeated misses."""
    best = (n0, e0)
    best_n = n0
    cur_n, cur_e = n0, e0
    misses = 0
    while time.monotonic() < deadline:
        ok = False
        if misses % 2 == 0:
            res = _pair_search(cur_n, cur_e, d, D,
                               min(deadline, time.monotonic() + PAIR_SLICE), rng)
            if res is not None:
                cur_n, cur_e = res
                ok = True
        else:
            adj = [set() for _ in range(cur_n)]
            for u, v in cur_e:
                adj[u].add(v)
                adj[v].add(u)
            color = _bipartition(cur_n, [list(s) for s in adj])
            vr = _vertex_attempt(cur_n, adj, color, d, D, rng,
                                 min(deadline, time.monotonic() + VERT_SLICE), VERT_ITERS)
            if vr is not None:
                nn, adj2, _ = vr
                cur_n = nn
                cur_e = [(u, v) for u in range(nn) for v in adj2[u] if u < v]
                ok = True
        if ok:
            misses = 0
            if cur_n > best_n and lib.is_valid(cur_n, cur_e, d, D):
                best = (cur_n, cur_e)
                best_n = cur_n
        else:
            misses += 1
            if misses >= 6:
                cur_n, cur_e = best
                misses = 0
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.3, min(FRAC * time_limit, time_limit - MARGIN))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:                       # cycle of length 2D: bipartite, diameter D
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:                       # K_{d,d} is Moore-extremal for D = 2
        return lib.haar_graph(d, range(d))

    moore = lib.moore_bound(d, D)

    # Moore-extremal projective plane for D = 3.
    if D == 3 and lib.is_prime_power(d - 1):
        pg = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(pg[0], pg[1], d, D):
            return pg

    cands = [lib.haar_graph(d, range(d))]
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            cands.append(lib.araujo_lopez_graph(d - 2))   # record construction, degree q+2 = d
        except Exception:
            pass
    pg = _best_pg(d)
    if pg is not None:
        cands.append(pg)
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            cands.append(gq)

    valid = [c for c in cands if lib.is_valid(c[0], c[1], d, D)]
    base = max(valid, key=lambda c: c[0]) if valid else cands[0]
    if base[0] >= moore:
        return base

    best = _search(base[0], base[1], d, D, deadline, rng)
    if lib.is_valid(best[0], best[1], d, D):
        return best
    return base
