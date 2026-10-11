import itertools
import random
import time

import lib

# New idea in this version: a degree-preserving 2-switch plateau walk (_switch / _ils).
# Each move rewires two cross-side edges (a,b),(c,e) into (a,e),(c,b). This keeps every
# degree and the bipartition. A move is kept only if the diameter stays <= D. After a
# kept move, the code tries to regrow a vertex, because the reshuffled balls may now
# admit a full cover. Vertex removal + refill is interleaved as a kick.


# ----------------------------------------------------------------------------
# Base constructions: PG(2,q) for D = 3, generalized quadrangle W(q) for D >= 4.
# ----------------------------------------------------------------------------

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


def _gq_bases(d, count):
    out = []
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            out.append(_gq_w(q))
            if len(out) == count:
                break
    return out


def _pg_bases(d, count):
    out = []
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            out.append(lib.projective_plane_incidence(q))
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


def _remove_vertex(n, edges, x):
    last = n - 1

    def m(v):
        return x if v == last else v

    new = [(m(u), m(v)) for u, v in edges if u != x and v != x]
    return n - 1, new


# ----------------------------------------------------------------------------
# Growth: spare-degree saturation, cover-based vertex addition, fill.
# ----------------------------------------------------------------------------

def _greedy_saturate(n, edges, d, D, rng, deadline, samples=300):
    """Add cross-side edges between spare-degree vertices, greedily maximising the
    number of distance-(D-1) ball differences they create. Never breaks validity."""
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


def _add_one(n, edges, d, D, rng):
    """Add one vertex whose neighbours cover every vertex within distance D-1."""
    adj = _adjacency(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    ball = _balls_radius(n, adj, D - 1)
    full = (1 << n) - 1
    sides = [0, 1]
    rng.shuffle(sides)
    for c in sides:
        cands = [s for s in range(n) if color[s] == c and deg[s] < d]
        if not cands:
            continue
        chosen = None
        for attempt in range(30):
            chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
            if chosen:
                break
        if chosen:
            v = n
            new_edges = list(edges)
            for s in chosen:
                new_edges.append((s, v))
            return n + 1, new_edges
    return None


def _fill(n, edges, d, D, rng, deadline):
    while time.monotonic() < deadline:
        r = _add_one(n, edges, d, D, rng)
        if r is None:
            break
        n, edges = r
    edges = _greedy_saturate(n, edges, d, D, rng, deadline)
    return n, edges


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
                j = rng.choice([x for x in users[u] if inS[x]])
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
    chosen = _pack(R, capv, n, rng, deadline, iters)
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


def _expand(n, edges, d, D, deadline, rng, rounds=6):
    cur_n, cur_e = n, list(edges)
    for _ in range(rounds):
        if time.monotonic() >= deadline:
            break
        n0 = cur_n
        for side in (0, 1):
            cur_n, cur_e = _twin_pass(cur_n, cur_e, d, side, rng, deadline,
                                      rng.choice([3000, 10000, 30000]))
        cur_n, cur_e = _fill(cur_n, cur_e, d, D, rng, deadline)
        if cur_n == n0:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# NEW: degree-preserving bipartite 2-switch plateau walk with regrowth.
# ----------------------------------------------------------------------------

def _switch(n, edges, rng, tries=20):
    """Propose (a,b),(c,e) -> (a,e),(c,b) with a,c on side 0 and b,e on side 1.
    Degrees and bipartiteness are preserved. Returns the new edge list or None."""
    adj = _adjacency(n, edges)
    color = _bipartition(n, adj)
    E = list(edges)
    S = {(min(u, v), max(u, v)) for u, v in E}
    m = len(E)
    if m < 2:
        return None
    for _ in range(tries):
        i, j = rng.randrange(m), rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        if color[a]:
            a, b = b, a
        c, e = E[j]
        if color[c]:
            c, e = e, c
        if a == c or b == e:
            continue
        na = (min(a, e), max(a, e))
        nb = (min(c, b), max(c, b))
        if na in S or nb in S:
            continue
        E2 = list(E)
        E2[i] = (a, e)
        E2[j] = (c, b)
        return E2
    return None


def _ils(n, edges, d, D, deadline, rng, holder):
    """Mix switch-walk moves (with regrowth) and vertex kick + refill moves.
    holder[0] tracks the best (n, edges) seen; each stored graph was verified valid."""
    cn, ce = n, list(edges)
    while time.monotonic() < deadline:
        if rng.random() < 0.6:
            E2 = _switch(cn, ce, rng)
            if E2 is None or not lib.within_diameter(cn, E2, D):
                continue
            ce = E2
            r = _add_one(cn, ce, d, D, rng)
            if r is not None:
                cn, ce = r
        else:
            x = rng.randrange(cn)
            rn, re = _remove_vertex(cn, ce, x)
            if rn <= 0 or not lib.within_diameter(rn, re, D):
                continue
            rn, re = _fill(rn, re, d, D, rng, deadline)
            if rn >= cn:
                cn, ce = rn, re
        if cn > holder[0][0]:
            holder[0] = (cn, list(ce))


# ----------------------------------------------------------------------------
# Search phases.
# ----------------------------------------------------------------------------

def _expansion(d, D, seed, deadline, bases, consider, st):
    target = lib._moore_bound(d, D)
    attempt = 0
    while time.monotonic() < deadline and st["best"][0] < target:
        attempt += 1
        arng = random.Random(seed * 1000003 + attempt)
        src = st["best"] if arng.random() < 0.35 else bases[attempt % len(bases)]
        n2, e2 = _expand(src[0], src[1], d, D, deadline, arng)
        consider(n2, e2)


def _run(d, D, seed, start, total, rng, consider, st):
    if D == 2:
        return  # K_{d,d} already has the Moore order 2d for D = 2
    if d == 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])  # even cycle C_{2D}
        return

    raw = _pg_bases(d, 2) if D == 3 else _gq_bases(d, 2)
    if not raw:
        return
    bases = []
    for n0, e0 in raw:
        consider(n0, e0)
        e1 = _greedy_saturate(n0, e0, d, D, rng, start + total)
        consider(n0, e1)
        bases.append((n0, e1))
    if st["best"][0] >= lib._moore_bound(d, D):
        return

    _expansion(d, D, seed, start + 0.35 * total, bases, consider, st)
    holder = [st["best"]]
    _ils(st["best"][0], st["best"][1], d, D, start + total, rng, holder)
    if holder[0][0] > st["best"][0]:
        consider(holder[0][0], holder[0][1])


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = 0.85 * time_limit
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
            _run(d, D, seed, start, total, rng, consider, st)
        except Exception:
            pass

    n, e = st["best"]
    if not lib.is_valid(n, e, d, D):
        return lib.haar_graph(d, range(d))
    return n, e
