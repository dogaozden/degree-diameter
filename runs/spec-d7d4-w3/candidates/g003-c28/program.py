import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions: projective planes (D = 3) and generalized quadrangles W(q) (D >= 4).
# ----------------------------------------------------------------------------

def _best_pg(d, count=1):
    """Incidence graphs of PG(2, q) for the largest prime powers q with q + 1 <= d."""
    out = []
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            out.append(lib.projective_plane_incidence(q))
            if len(out) == count:
                break
    return out


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


def _gq_bases(d, count):
    out = []
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            out.append(_gq_w(q))
            if len(out) == count:
                break
    return out


# ----------------------------------------------------------------------------
# Graph helpers.
# ----------------------------------------------------------------------------

def _adjacency(n, edges):
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


def _balls_radius(n, adj, r):
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


# ----------------------------------------------------------------------------
# NEW (bold): cyclic Haar graphs H(Z_m, S) with |S| = d.
# Order 2m, d-regular, bipartite. Search for S with diameter <= D by
# hill climbing on the number of vertices unreached from a_0 and b_0
# (the graph is vertex-transitive within each side, so two sources suffice).
# ----------------------------------------------------------------------------

def _haar_nbrs(m, S, u):
    if u < m:
        return [m + (u + s) % m for s in S]
    j = u - m
    return [(j - s) % m for s in S]


def _haar_cost(m, S, D):
    N = 2 * m
    total = 0
    for src in (0, m):
        dist = [-1] * N
        dist[src] = 0
        frontier = [src]
        seen = 1
        for step in range(D):
            nxt = []
            for u in frontier:
                for v in _haar_nbrs(m, S, u):
                    if dist[v] < 0:
                        dist[v] = step + 1
                        nxt.append(v)
            seen += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - seen
    return total


def _haar_search(d, D, lo, hi, deadline, rng, consider, st):
    if lo < d:
        lo = d
    while time.monotonic() < deadline and lo <= hi:
        m = rng.randint(lo, hi)
        S = rng.sample(range(m), d)
        cur = _haar_cost(m, S, D)
        for _ in range(250):
            if cur == 0 or time.monotonic() > deadline:
                break
            idx = rng.randrange(d)
            new = rng.randrange(m)
            if new in S:
                continue
            old = S[idx]
            S[idx] = new
            c = _haar_cost(m, S, D)
            if c <= cur:
                cur = c
            else:
                S[idx] = old
        if cur == 0:
            edges = [(i, m + (i + s) % m) for i in range(m) for s in S]
            consider(2 * m, edges)
            # Push the search range above the current best order.
            lo = max(lo, st["best"][0] // 2 + 1)


# ----------------------------------------------------------------------------
# Diameter-preserving growth: cover-based vertex addition, edge saturation.
# ----------------------------------------------------------------------------

def _greedy_saturate(n, edges, d, D, rng, deadline, samples=300):
    """Add cross-side edges between spare-degree vertices, greedily maximising the
    number of distance-(D-1) ball differences they create. Never breaks diameter."""
    edges = list(edges)
    adj = _adjacency(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
    while time.monotonic() < deadline:
        left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
        right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
        if not left or not right:
            break
        ball = _balls_radius(n, adj, D - 1)
        best, best_s = None, -1.0
        for _ in range(samples):
            a = rng.choice(left)
            b = rng.choice(right)
            if (min(a, b), max(a, b)) in existing:
                continue
            s = ((ball[a] & ~ball[b]).bit_count()
                 + (ball[b] & ~ball[a]).bit_count() + rng.random())
            if s > best_s:
                best, best_s = (a, b), s
        if best is None:
            pairs = [(a, b) for a in left for b in right
                     if (min(a, b), max(a, b)) not in existing]
            if not pairs:
                break
            best = rng.choice(pairs)
        a, b = best
        edges.append((a, b))
        existing.add((min(a, b), max(a, b)))
        adj[a].append(b)
        adj[b].append(a)
        deg[a] += 1
        deg[b] += 1
    return edges


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


def _extend_cover(n, edges, d, D, deadline, rng, always_random=False):
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = _adjacency(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    attempts_max = 600 if D >= 4 else 200

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(attempts_max):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng,
                                       always_random or attempt > 0)
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


def _grow(n, edges, d, D, deadline, rng, always_random=False):
    cur_n, cur_e = n, list(edges)
    for _ in range(12):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, always_random)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _greedy_saturate(cur_n, e2, d, D, rng, deadline)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Twin blow-up with spare-capacity packing (valid for D >= 2).
# ----------------------------------------------------------------------------

def _pack(R, cap, n, rng, deadline, iters):
    k = len(R)
    if k == 0:
        return []
    users = [[] for _ in range(n)]
    for i, r in enumerate(R):
        for u in r:
            users[u].append(i)
    load = [0] * n
    inS = [False] * k
    S = set()

    def add(i):
        inS[i] = True
        S.add(i)
        for u in R[i]:
            load[u] += 1

    def remove(i):
        inS[i] = False
        S.discard(i)
        for u in R[i]:
            load[u] -= 1

    order = list(range(k))
    rng.shuffle(order)
    for i in order:
        if all(load[u] < cap[u] for u in R[i]):
            add(i)
    best = list(S)

    for _ in range(iters):
        if time.monotonic() > deadline:
            break
        i = rng.randrange(k)
        if inS[i]:
            continue
        removed = []
        for u in R[i]:
            while load[u] >= cap[u]:
                opts = [x for x in users[u] if inS[x]]
                if not opts:
                    break
                j = rng.choice(opts)
                remove(j)
                removed.append(j)
        add(i)
        delta = 1 - len(removed)
        if delta < 0 and rng.random() >= 0.03:
            remove(i)
            for j in removed:
                add(j)
        if len(S) > len(best):
            best = list(S)
    return best


def _exact_cover(R, universe, users, deadline, node_cap):
    covered = set()
    chosen = []
    nodes = [0]

    def rec():
        if len(covered) == len(universe):
            return True
        nodes[0] += 1
        if nodes[0] > node_cap or time.monotonic() > deadline:
            return False
        best_opts = None
        for u in universe:
            if u in covered:
                continue
            opts = [i for i in users[u] if all(r not in covered for r in R[i])]
            if not opts:
                return False
            if best_opts is None or len(opts) < len(best_opts):
                best_opts = opts
        for i in best_opts:
            for r in R[i]:
                covered.add(r)
            chosen.append(i)
            if rec():
                return True
            chosen.pop()
            for r in R[i]:
                covered.discard(r)
        return False

    return list(chosen) if rec() else None


def _twin_pass(n, edges, d, side, rng, deadline, iters):
    adj = _adjacency(n, edges)
    color = _bipartition(n, adj)
    deg = [len(a) for a in adj]
    capv = [d - deg[u] for u in range(n)]
    cands = [v for v in range(n)
             if color[v] == side and adj[v] and all(capv[u] >= 1 for u in adj[v])]
    if not cands:
        return n, edges
    R = [adj[v] for v in cands]
    universe = sorted({u for r in R for u in r})

    chosen = None
    if all(capv[u] == 1 for u in universe):
        users = [[] for _ in range(n)]
        for i, r in enumerate(R):
            for u in r:
                users[u].append(i)
        ex = _exact_cover(R, universe, users, deadline, 3000)
        if ex is not None:
            chosen = ex
    pk = _pack(R, capv, n, rng, deadline, iters)
    if chosen is None or len(pk) > len(chosen):
        chosen = pk
    if not chosen:
        return n, edges

    new_edges = list(edges)
    nn = n
    for i in chosen:
        v = cands[i]
        for u in adj[v]:
            new_edges.append((u, nn))
        nn += 1
    return nn, new_edges


def _expand(n, edges, d, D, deadline, rng, rounds=6, always_random=False):
    cur_n, cur_e = n, list(edges)
    for _ in range(rounds):
        if time.monotonic() >= deadline:
            break
        n0 = cur_n
        for side in (0, 1):
            iters = rng.choice([3000, 10000, 30000])
            cur_n, cur_e = _twin_pass(cur_n, cur_e, d, side, rng, deadline, iters)
        cur_n, cur_e = _grow(cur_n, cur_e, d, D, deadline, rng, always_random)
        if cur_n == n0:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Search phases.
# ----------------------------------------------------------------------------

def _expansion_loop(d, D, seed, deadline, bases, consider, st):
    if not bases:
        return
    target = lib._moore_bound(d, D)
    attempt = 0
    rot = 0
    while time.monotonic() < deadline and st["best"][0] < target:
        attempt += 1
        arng = random.Random(seed * 1000003 + attempt)
        if arng.random() < 0.35:
            src = st["best"]
        else:
            src = bases[rot % len(bases)]
            rot += 1
        always_random = arng.random() < 0.3
        n2, e2 = _expand(src[0], src[1], d, D, deadline, arng,
                         always_random=always_random)
        e2 = _greedy_saturate(n2, e2, d, D, arng, deadline)
        consider(n2, e2)


def _run(d, D, seed, start, total, deadline, rng, consider, st):
    if D == 2:
        return  # K_{d,d} already has the Moore order 2d for D = 2

    if d == 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])  # even cycle C_{2D}
        return

    moore = lib._moore_bound(d, D)

    if D == 3:
        pg = _best_pg(d, 2)
        if not pg:
            return
        for b in pg:
            consider(b[0], b[1])
        if st["best"][0] >= moore:
            return
        _haar_search(d, D, st["best"][0] // 2 + 1, moore // 2,
                     start + 0.5 * total, rng, consider, st)
        _expansion_loop(d, D, seed, deadline, list(pg), consider, st)
        return

    if D >= 4:
        raw = _gq_bases(d, 2)
        for b in raw:
            consider(b[0], b[1])
        if st["best"][0] >= moore:
            return
        # NEW (bold): cyclic Haar graph search with degree d, diameter D.
        _haar_search(d, D, st["best"][0] // 2 + 1, moore // 2,
                     start + 0.6 * total, rng, consider, st)
        if st["best"][0] >= moore:
            return
        # Safe fallback: the saturated quadrangle bases plus twin/cover expansion.
        bases = []
        for b in raw:
            bases.append((b[0], _greedy_saturate(b[0], b[1], d, D, rng, deadline)))
        for b in bases:
            consider(b[0], b[1])
        _expansion_loop(d, D, seed, deadline, bases, consider, st)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = 0.85 * time_limit
    deadline = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    st = {"best": lib.haar_graph(d, range(d))}  # K_{d,d}: valid fallback for D >= 2

    def consider(n, e):
        if n > st["best"][0] and lib.is_valid(n, e, d, D):
            st["best"] = (n, e)

    if st["best"][0] < lib._moore_bound(d, D):
        try:
            _run(d, D, seed, start, total, deadline, rng, consider, st)
        except Exception:
            pass

    n, e = st["best"]
    if not lib.is_valid(n, e, d, D):
        return lib.haar_graph(d, range(d))
    return n, e
