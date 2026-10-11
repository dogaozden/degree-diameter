import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured bases.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and totally isotropic lines of W(q); order 2(q+1)(q^2+1)."""
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _best_gq(d):
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Graph helpers.
# ----------------------------------------------------------------------------

def _balls(n, adj, r):
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


def _colour(n, adj):
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


def _cover(cands, ball, full, d, rng, randomize):
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best = max(gains)
        if best == 0:
            break
        opts = [i for i, g in enumerate(gains) if g == best]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend(n, edges, d, D, deadline, rng):
    """Add vertices whose neighbourhoods cover all vertices within distance D-1 (keeps diameter D)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _colour(n, adj)
    while time.monotonic() < deadline:
        ball = _balls(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(8):
                chosen = _cover(cands, ball, full, d, rng, attempt > 0)
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


def _saturate(n, edges, d, rng):
    """Join deficient opposite-side vertices. Only shortens distances, so validity is kept."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    ex = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        ex.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _colour(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in ex]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# NEW CONSTRUCTION: bi-Cayley graphs over finite groups.
#
# Two base vertices A, B; one dart per connection element g in S (|S| = d):
# (x, A) ~ (x*g, B). Each side is vertex-transitive under left multiplication,
# so the diameter is at most D iff BFS from (A, e) and from (B, e) reach all
# 2N vertices within D steps. Search S by simulated annealing on the number of
# unreached vertices. Groups: cyclic Z_N and semidirect Z_m x| Z_k with mk = N.
# Orders are scanned from the Moore limit downward; the first valid lift wins.
# ----------------------------------------------------------------------------

def _group_options(N, rng):
    opts = [lib.cyclic_group(N)]
    cands = []
    for k in range(2, 9):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                cands.append((m, k, r))
    rng.shuffle(cands)
    for m, k, r in cands[:2]:
        try:
            opts.append(lib.semidirect_group(m, k, r))
        except ValueError:
            pass
    return opts


def _cost(order, mt, ginv, S, D):
    """Number of vertices not reached within D steps from (A, e) and from (B, e)."""
    total = 0
    for root in (0, order):
        seen = {root}
        frontier = [root]
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < order:
                    row = mt[v]
                    for g in S:
                        w = order + row[g]
                        if w not in seen:
                            seen.add(w)
                            nxt.append(w)
                else:
                    row = mt[v - order]
                    for g in S:
                        w = row[ginv[g]]
                        if w not in seen:
                            seen.add(w)
                            nxt.append(w)
            frontier = nxt
        total += 2 * order - len(seen)
    return total


def _anneal_group(order, mt, ginv, d, D, rng, end):
    if d > order:
        return None
    S = rng.sample(range(order), d)
    cur = _cost(order, mt, ginv, S, D)
    T = 2.0
    while cur > 0 and time.monotonic() < end:
        i = rng.randrange(d)
        c = rng.randrange(order)
        if c in S:
            continue
        S2 = list(S)
        S2[i] = c
        c2 = _cost(order, mt, ginv, S2, D)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            S, cur = S2, c2
        T = max(0.1, T * 0.995)
    return S if cur == 0 else None


def _lift_search(d, D, lo_n, deadline, rng, per_option):
    """Return a valid bi-Cayley graph with more than lo_n vertices, or None."""
    hi = lib.moore_bound(d, D) // 2
    for N in range(hi, lo_n // 2, -1):
        if time.monotonic() >= deadline:
            break
        for order, mul, inv in _group_options(N, rng):
            if time.monotonic() >= deadline:
                break
            mt = [[mul(x, y) for y in range(order)] for x in range(order)]
            ginv = [inv(g) for g in range(order)]
            end = min(deadline, time.monotonic() + per_option)
            S = _anneal_group(order, mt, ginv, d, D, rng, end)
            if S is not None:
                n2, e2 = lib.group_lift(2, [(0, 1, g) for g in S], order, mul)
                if lib.is_valid(n2, e2, d, D):
                    return n2, e2
    return None


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.9 * time_limit
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    # Structured base (generalized quadrangle for D >= 4, projective plane for D = 3).
    base = None
    if D >= 4:
        base = _best_gq(d)
    if base is None and D >= 3:
        base = _best_pg(d)
    if base is not None:
        n0, e0 = base
        consider(n0, e0)
        grow_end = start + 0.20 * time_limit
        n1, e1 = _grow(best_n, best_e, d, D, grow_end, rng)
        consider(n1, e1)

    # New construction: bi-Cayley lifts, searched from the Moore limit downward.
    if D >= 2 and time.monotonic() < deadline:
        lift_end = start + 0.80 * time_limit
        res = _lift_search(d, D, best_n, lift_end, rng, per_option=0.15)
        if res is not None:
            consider(*res)

    # Top up any remaining slack with cover growth from the best graph.
    if D >= 2 and time.monotonic() < deadline:
        n3, e3 = _grow(best_n, best_e, d, D, deadline, rng)
        consider(n3, e3)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
