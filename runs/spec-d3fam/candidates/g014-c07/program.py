import itertools
import math
import random
import time

import lib

TIME_FRAC = 0.8       # fraction of time_limit used before returning
MARGIN = 2.0          # seconds kept in reserve
ITER = 1500           # annealing steps per vertex-insertion attempt
MAX_FAILS = 12        # consecutive failed insertion attempts before stopping


# ---------------------------------------------------------------- adjacency helpers

def _to_adj(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _to_edges(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


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
    return sum(n - b.bit_count() for b in _balls(n, adj, D)) // 2


def _greedy(cands, ball, full, d, rng, randomize):
    """Greedy cover of `full` by at most d candidates. Returns (chosen, covered_all)."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        best_g, best_i = 0, -1
        for i, s in enumerate(pool):
            g = (ball[s] & ~covered).bit_count()
            if g > best_g or (randomize and g == best_g and g > 0 and rng.random() < 0.5):
                best_g, best_i = g, i
        if best_i < 0:
            break
        s = pool.pop(best_i)
        chosen.append(s)
        covered |= ball[s]
    return chosen, covered == full


# ---------------------------------------------------------------- base constructions

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
            return _gq_w(q)
    return None


# ---------------------------------------------------------------- growth moves (diameter-safe)

def _saturate(n, adj, color, d, rng):
    """Join deficient opposite-colour non-adjacent vertices. Adding edges never breaks the bound."""
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)


def _grow_once(n, adj, color, d, D, rng):
    """Add one vertex whose neighbourhood covers every vertex within D-1 of the graph.

    The new vertex is at distance <= D from everything, and old distances cannot grow.
    Mutates adj/color in place; returns the new vertex count, or None.
    """
    ball = _balls(n, adj, D - 1)
    full = (1 << n) - 1
    sides = [0, 1]
    rng.shuffle(sides)
    for c in sides:
        cands = [s for s in range(n) if color[s] == c and len(adj[s]) < d]
        if not cands:
            continue
        for t in range(30):
            chosen, ok = _greedy(cands, ball, full, d, rng, t > 0)
            if ok:
                v = n
                adj.append(set())
                color.append(1 - c)
                for s in chosen:
                    adj[s].add(v)
                    adj[v].add(s)
                return n + 1
    return None


def _grow(n, adj, color, d, D, rng, deadline):
    """Alternate cover-vertex additions with edge saturation until neither applies."""
    while time.monotonic() < deadline:
        _saturate(n, adj, color, d, rng)
        m = _grow_once(n, adj, color, d, D, rng)
        if m is None:
            break
        n = m
    _saturate(n, adj, color, d, rng)
    return n


# ---------------------------------------------------------------- annealed insertion

def _pick(n, adj, color, c, d, D, rng):
    """Choose d vertices of colour 1-c, greedily covering the radius-(D-1) balls where possible."""
    other = [v for v in range(n) if color[v] == 1 - c]
    if len(other) < d:
        return None
    ball = _balls(n, adj, D - 1)
    chosen, _ = _greedy(other, ball, (1 << n) - 1, d, rng, True)
    chosen_set = set(chosen)
    rest = [v for v in other if v not in chosen_set]
    rng.shuffle(rest)
    return chosen + rest[:d - len(chosen)]


def _swap(adj, side0, rng):
    """Degree-preserving double-edge swap keeping bipartiteness. Returns undo info or None."""
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


def _insert_anneal(n, adj, color, d, D, rng, deadline):
    """Add one vertex, then anneal swaps until the diameter bound holds again.

    Returns (n, adj, color) on success, else None. Degrees and bipartiteness are preserved.
    """
    adj = [set(s) for s in adj]
    color = list(color)
    c = rng.randrange(2)
    nb = _pick(n, adj, color, c, d, D, rng)
    if not nb:
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
    if not side0:
        return None
    cost = _bad_pairs(n, adj, D)
    for it in range(ITER):
        if cost == 0:
            break
        if time.monotonic() > deadline:
            return None
        mv = _swap(adj, side0, rng)
        if mv is None:
            continue
        new = _bad_pairs(n, adj, D)
        delta = new - cost
        temp = 1.5 * (1.0 - it / ITER) + 0.05
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cost = new
        else:
            _unswap(adj, mv)
    if cost != 0:
        return None
    return n, adj, color


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, TIME_FRAC * time_limit - MARGIN)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:                          # cycle of length 2D: bipartite, diameter D
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    fallback = lib.haar_graph(d, range(d))   # K_{d,d}: diameter 2, valid for D >= 2
    if D == 2:
        return fallback

    best_n, best_e = fallback

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    # Moore-extremal case: nothing can beat it.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    # Structured starting candidates.
    if D == 3:
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))   # 2(q^2+q+5), q = d-2
            except Exception:
                pass
        q = d - 1
        while q >= 2 and not lib.is_prime_power(q):
            q -= 1
        if q >= 2:
            consider(*lib.projective_plane_incidence(q))
    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Working state: best candidate, grown with diameter-safe moves.
    def snapshot():
        adj = _to_adj(best_n, best_e)
        return best_n, adj, _colour(best_n, adj)

    def publish(n, adj):
        nonlocal best_n, best_e
        if n > best_n:
            e = _to_edges(n, adj)
            if lib.is_valid(n, e, d, D):
                best_n, best_e = n, e
                return True
        return False

    cn, cadj, ccol = snapshot()
    cn = _grow(cn, cadj, ccol, d, D, rng, deadline)
    if not publish(cn, cadj):
        cn, cadj, ccol = snapshot()

    # Main search: annealed vertex insertion, each followed by diameter-safe growth.
    fails = 0
    while time.monotonic() < deadline and fails < MAX_FAILS:
        res = _insert_anneal(cn, cadj, ccol, d, D, rng, deadline)
        if res is None:
            fails += 1
            continue
        fails = 0
        n2, a2, c2 = res
        n2 = _grow(n2, a2, c2, d, D, rng, deadline)
        if publish(n2, a2):
            cn, cadj, ccol = n2, a2, c2
        elif n2 > cn:
            cn, cadj, ccol = n2, a2, c2
        else:
            cn, cadj, ccol = snapshot()

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, best_e
