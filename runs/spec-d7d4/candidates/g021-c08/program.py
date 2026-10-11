"""Bold variant: diameter-preserving growth from a generalized quadrangle or projective
plane base, then simulated annealing with degree-preserving double-edge swaps to insert
extra vertices. Every returned graph is verified with lib.is_valid, and the best verified
graph is kept, so the output is always valid."""
import itertools
import math
import random
import time

import lib


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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def _baseline(d, D):
    """Starting graph: a projective plane (D = 3), a quadrangle W(q) (D = 4), else K_{d,d}."""
    if D == 3:
        for q in range(min(d - 1, 23), 1, -1):
            if lib.is_prime_power(q):
                return lib.projective_plane_incidence(q)
    if D == 4:
        for q in range(min(d - 1, 9), 1, -1):
            if lib.is_prime_power(q):
                return _gq_w(q)
    return lib.haar_graph(d, range(d))


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


def _balls(N, adj, r):
    """Bitmask of the radius-r ball around every vertex."""
    reach = [1 << v for v in range(N)]
    for _ in range(r):
        new = [0] * N
        for v in range(N):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new[v] = x
        reach = new
    return reach


def _bad(N, adj, D):
    """Number of unordered pairs at distance greater than D (unreachable pairs included)."""
    reach = _balls(N, adj, D)
    return sum(N - r.bit_count() for r in reach) // 2


def _edges(adj, side):
    return [(a, b) for a in range(len(adj)) if side[a] == 0 for b in adj[a]]


def _greedy(cands, ball, full, d, rng, randomize):
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


def _cover_add(adj, side, d, D, rng):
    """Append one vertex whose neighbourhood covers all vertices within D-1 steps.
    This keeps the diameter at most D. Mutates adj and side; returns True on success."""
    N = len(adj)
    ball = _balls(N, adj, D - 1)
    full = (1 << N) - 1
    sides = [0, 1]
    rng.shuffle(sides)
    for s in sides:
        cands = [u for u in range(N) if side[u] != s and len(adj[u]) < d]
        if not cands:
            continue
        for attempt in range(8):
            chosen = _greedy(cands, ball, full, d, rng, attempt > 0)
            if chosen:
                v = N
                adj.append(set(chosen))
                side.append(s)
                for u in chosen:
                    adj[u].add(v)
                return True
    return False


def _saturate(adj, side, d, rng):
    """Add edges between opposite-side vertices with spare degree. Distances never grow."""
    N = len(adj)
    L = [u for u in range(N) if side[u] == 0 and len(adj[u]) < d]
    R = [u for u in range(N) if side[u] == 1 and len(adj[u]) < d]
    pairs = [(a, b) for a in L for b in R if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)


def _add_forced(adj, side, d, rng):
    """Insert a vertex joined to d random opposite vertices, freeing a slot at any
    full neighbour by dropping one of its edges. Degrees stay <= d."""
    N = len(adj)
    s = rng.randrange(2)
    opp = [u for u in range(N) if side[u] != s]
    if not opp:
        return False
    chosen = rng.sample(opp, min(d, len(opp)))
    for u in chosen:
        if len(adj[u]) >= d:
            x = rng.choice(list(adj[u]))
            adj[u].discard(x)
            adj[x].discard(u)
    v = N
    adj.append(set(chosen))
    side.append(s)
    for u in chosen:
        adj[u].add(v)
    return True


def _swap_apply(adj, a, b, c, e):
    """Replace edges (a,b),(c,e) by (a,e),(c,b). Degrees are unchanged."""
    adj[a].discard(b)
    adj[b].discard(a)
    adj[c].discard(e)
    adj[e].discard(c)
    adj[a].add(e)
    adj[e].add(a)
    adj[c].add(b)
    adj[b].add(c)


def _anneal(adj, side, d, D, deadline, rng, T0, T1):
    """Simulated annealing on the bad-pair count with swap and add-edge moves.
    Returns True if the graph reaches diameter <= D before the deadline."""
    N = len(adj)
    cur = _bad(N, adj, D)
    if cur == 0:
        return True
    E = [(a, b) for a in range(N) if side[a] == 0 for b in adj[a]]
    L = [v for v in range(N) if side[v] == 0]
    R = [v for v in range(N) if side[v] == 1]
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T = T0
    it = 0
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        it += 1
        if it % 16 == 0:
            T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        if rng.random() < 0.2 or len(E) < 2:
            a = rng.choice(L)
            b = rng.choice(R)
            if b in adj[a] or len(adj[a]) >= d or len(adj[b]) >= d:
                continue
            adj[a].add(b)
            adj[b].add(a)
            new = _bad(N, adj, D)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
                E.append((a, b))
            else:
                adj[a].discard(b)
                adj[b].discard(a)
        else:
            i = rng.randrange(len(E))
            j = rng.randrange(len(E))
            a, b = E[i]
            c, e = E[j]
            if a == c or b == e or e in adj[a] or b in adj[c]:
                continue
            _swap_apply(adj, a, b, c, e)
            new = _bad(N, adj, D)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
                E[i] = (a, e)
                E[j] = (c, b)
            else:
                _swap_apply(adj, a, e, c, b)
    return cur == 0


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.85 * time_limit - 1.5)
    deadline = start + total
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    rng = random.Random(seed)

    # Safe fallback: K_{d,d}, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

    base = _baseline(d, D)
    consider(base[0], base[1])
    if best[0] >= lib._moore_bound(d, D):
        return best

    try:
        n0, e0 = best
        cur_adj = [set() for _ in range(n0)]
        for u, v in e0:
            cur_adj[u].add(v)
            cur_adj[v].add(u)
        cur_side = _bipartition(n0, cur_adj)
        _saturate(cur_adj, cur_side, d, rng)

        slice_len = max(3.0, total / 6.0)
        while time.monotonic() < deadline:
            trial_adj = [set(s) for s in cur_adj]
            trial_side = list(cur_side)
            if _cover_add(trial_adj, trial_side, d, D, rng):
                _saturate(trial_adj, trial_side, d, rng)
                if not consider(len(trial_adj), _edges(trial_adj, trial_side)):
                    break
                cur_adj, cur_side = trial_adj, trial_side
                continue
            _add_forced(trial_adj, trial_side, d, rng)
            slice_end = min(deadline, time.monotonic() + slice_len)
            if _anneal(trial_adj, trial_side, d, D, slice_end, rng, 2.0, 0.1):
                _saturate(trial_adj, trial_side, d, rng)
                if not consider(len(trial_adj), _edges(trial_adj, trial_side)):
                    break
                cur_adj, cur_side = trial_adj, trial_side
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
