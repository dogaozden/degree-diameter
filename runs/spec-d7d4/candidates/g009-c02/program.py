import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases: generalized quadrangle W(q) for D = 4, projective plane for D = 3.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); points first, then lines."""
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


def _largest_pp_le(x):
    """Largest prime power q with 2 <= q <= x, or None."""
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


# ----------------------------------------------------------------------------
# Cost: number of unordered vertex pairs at distance > D (unreachable counts).
# ----------------------------------------------------------------------------

def _bitballs(n, adj, D):
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _cost(n, adj, D):
    return sum(n - r.bit_count() for r in _bitballs(n, adj, D)) // 2


# ----------------------------------------------------------------------------
# Simulated annealing over bipartite graphs with a fixed vertex count.
# Moves: re-attach one end of an edge (degree-preserving on the kept end),
# then greedily saturate spare degree between opposite sides. Adding edges
# never increases the cost, so saturation is always kept or undone with the move.
# ----------------------------------------------------------------------------

def _anneal(n, color, adj0, d, D, deadline, rng):
    """Return (cost, adj) for the final state; cost 0 means valid."""
    adj = [set(s) for s in adj0]
    log = []

    def add(a, b):
        adj[a].add(b)
        adj[b].add(a)
        log.append((True, a, b))

    def rem(a, b):
        adj[a].discard(b)
        adj[b].discard(a)
        log.append((False, a, b))

    def undo(mark):
        while len(log) > mark:
            is_add, a, b = log.pop()
            if is_add:
                adj[a].discard(b)
                adj[b].discard(a)
            else:
                adj[a].add(b)
                adj[b].add(a)

    def saturate():
        d0 = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
        d1 = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
        if not d0 or not d1:
            return
        rng.shuffle(d0)
        rng.shuffle(d1)
        for x in d0:
            if len(adj[x]) >= d:
                continue
            for y in d1:
                if len(adj[y]) < d and y not in adj[x]:
                    add(x, y)
                    if len(adj[x]) >= d:
                        break

    saturate()
    log.clear()
    cur = _cost(n, adj, D)
    start = time.monotonic()
    span = max(1e-6, deadline - start)
    t0, t1 = 1.0, 0.03

    while cur > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - start) / span
        T = t0 * (t1 / t0) ** frac
        log.clear()
        a = rng.randrange(n)
        if not adj[a]:
            continue
        b = rng.choice(sorted(adj[a]))
        e = rng.randrange(n)
        if color[e] != color[b] or e == b or e in adj[a] or len(adj[e]) >= d:
            continue
        rem(a, b)
        add(a, e)
        saturate()
        new = _cost(n, adj, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            undo(0)
    return cur, adj


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def _fallback(d, D):
    if d < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    return lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2


def _build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.8 * time_limit, time_limit - 6.0)
    deadline = start + max(0.0, budget)
    rng = random.Random(seed)

    best = _fallback(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d < 1 or D < 1 or D == 1:
        return best
    if d < 4:
        # Small cases: the projective-plane / quadrangle bases are already the best we do.
        if D == 3:
            q = _largest_pp_le(d - 1)
            if q:
                consider(*lib.projective_plane_incidence(q))
        elif D == 4:
            q = _largest_pp_le(d - 1)
            if q and q >= 2:
                consider(*_gq_w(q))
        return best

    # Choose base: W(q) for D = 4, PG(2,q) for D = 3, K_{d,d} otherwise.
    base = None
    q = _largest_pp_le(d - 1)
    if D == 3 and q:
        base = lib.projective_plane_incidence(q)
    elif D == 4 and q and q >= 2:
        base = _gq_w(q)
    if base is None:
        base = lib.haar_graph(d, range(d))
    consider(*base)

    # Vertex insertion + annealing: add a point and a line, then repair distances.
    n, edges = base
    half = n // 2
    color = [0] * half + [1] * half
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    cur_n, cur_adj, cur_color = n, adj, color

    while time.monotonic() < deadline:
        trial_n = cur_n + 2
        trial_adj = [set(s) for s in cur_adj] + [set(), set()]
        trial_color = cur_color + [0, 1]
        remaining = deadline - time.monotonic()
        slice_end = time.monotonic() + max(2.0, remaining / 3.0)
        cost, res_adj = _anneal(trial_n, trial_color, trial_adj, d, D,
                                min(slice_end, deadline), rng)
        if cost == 0:
            cur_n, cur_adj, cur_color = trial_n, res_adj, trial_color
            out = [(a, b) for a in range(cur_n) for b in cur_adj[a] if a < b]
            consider(cur_n, out)
        # On failure the same size is retried from the last valid state.

    if not lib.is_valid(best[0], best[1], d, D):
        best = _fallback(d, D)
    return best


def build(d, D, seed, time_limit):
    try:
        n, edges = _build(d, D, seed, time_limit)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return _fallback(d, D)
