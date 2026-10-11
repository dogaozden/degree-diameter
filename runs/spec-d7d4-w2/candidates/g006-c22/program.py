import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions: PG(2, q) incidence graphs (D = 3) and the generalized
# quadrangle W(q) incidence graphs (D >= 4).
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

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


# ----------------------------------------------------------------------------
# Graph utilities.
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


def _balls(n, adj, r):
    """Bitmask of all vertices within distance r of each vertex."""
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
    """Delete vertex x; the last vertex takes its label. Returns (n-1, edges)."""
    last = n - 1

    def m(v):
        return x if v == last else v

    return n - 1, [(m(u), m(v)) for u, v in edges if u != x and v != x]


# ----------------------------------------------------------------------------
# Greedy cover extension: a new vertex on side 1-c is adjacent to a set S of
# side-c vertices whose radius-(D-1) balls cover everything. This keeps the
# diameter at most D.
# ----------------------------------------------------------------------------

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
    """Add one vertex by a degree-respecting cover; return (n+1, edges) or None."""
    adj = _adjacency(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    ball = _balls(n, adj, D - 1)
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


def _extend_cover(n, edges, d, D, deadline, rng):
    """Repeatedly add cover vertices while possible."""
    edges = list(edges)
    while time.monotonic() < deadline:
        r = _add_one(n, edges, d, D, rng)
        if r is None:
            break
        n, edges = r
    return n, edges


def _saturate_edges(n, edges, d, rng):
    """Add random edges between non-adjacent opposite-side vertices with spare degree."""
    edges = list(edges)
    adj = _adjacency(n, edges)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
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


def _fill(n, edges, d, D, rng, deadline):
    """Add cover vertices while possible, then saturate spare slots."""
    n, edges = _extend_cover(n, edges, d, D, deadline, rng)
    edges = _saturate_edges(n, edges, d, rng)
    return n, edges


# ----------------------------------------------------------------------------
# Twin blow-up with spare-capacity packing. Twinning v keeps the diameter and
# bipartiteness when every neighbour of v has a spare degree slot.
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
    """Alternate twin packing on both sides with cover growth while the graph grows."""
    cur_n, cur_e = n, list(edges)
    for _ in range(rounds):
        if time.monotonic() >= deadline:
            break
        n0 = cur_n
        for side in (0, 1):
            iters = rng.choice([3000, 10000])
            cur_n, cur_e = _twin_pass(cur_n, cur_e, d, side, rng, deadline, iters)
        cur_n, cur_e = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        cur_e = _saturate_edges(cur_n, cur_e, d, rng)
        if cur_n == n0:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# NEW MOVE: degree-preserving 2-switch. Two edges a1-b1, a2-b2 (a on side 0,
# b on side 1) become a1-b2, a2-b1. Degrees and bipartiteness are preserved,
# so the move is a free plateau walk that can unlock new vertex insertions.
# A switch is kept only if the diameter stays within D.
# ----------------------------------------------------------------------------

def _two_switch(n, edges, D, rng, attempts=12):
    m = len(edges)
    if m < 2:
        return None
    color = _bipartition(n, _adjacency(n, edges))
    existing = {(min(u, v), max(u, v)) for u, v in edges}
    for _ in range(attempts):
        i, j = rng.randrange(m), rng.randrange(m)
        if i == j:
            continue
        a1, b1 = edges[i]
        a2, b2 = edges[j]
        if color[a1] == 1:
            a1, b1 = b1, a1
        if color[a2] == 1:
            a2, b2 = b2, a2
        if a1 == a2 or b1 == b2:
            continue
        k1 = (min(a1, b2), max(a1, b2))
        k2 = (min(a2, b1), max(a2, b1))
        if k1 in existing or k2 in existing:
            continue
        new_edges = list(edges)
        new_edges[i] = (a1, b2)
        new_edges[j] = (a2, b1)
        if lib.within_diameter(n, new_edges, D):
            return new_edges
    return None


# ----------------------------------------------------------------------------
# Iterated local search: excision moves (delete vertices, repair, regrow)
# alternate with 2-switch plateau moves followed by a regrowth attempt.
# ----------------------------------------------------------------------------

def _ils(n, edges, d, D, deadline, rng, holder, stall_limit=400):
    cn, ce = n, list(edges)
    stall = 0
    while time.monotonic() < deadline:
        if rng.random() < 0.5:
            # Excision move.
            x = rng.randrange(cn)
            rn, re = _remove_vertex(cn, ce, x)
            if rn >= 2 and rng.random() < 0.2:
                rn, re = _remove_vertex(rn, re, rng.randrange(rn))
            if rn < 2:
                stall += 1
                continue
            if not lib.within_diameter(rn, re, D):
                re = _saturate_edges(rn, re, d, rng)
                if not lib.within_diameter(rn, re, D):
                    stall += 1
                    continue
            rn, re = _fill(rn, re, d, D, rng, deadline)
            if rn >= cn:
                if rn > cn:
                    stall = 0
                cn, ce = rn, re
            else:
                stall += 1
        else:
            # 2-switch plateau move, then try to grow.
            se = _two_switch(cn, ce, D, rng)
            if se is None:
                stall += 1
                continue
            rn, re = _fill(cn, se, d, D, rng, deadline)
            if rn > cn:
                stall = 0
            else:
                stall += 1
            cn, ce = rn, re

        if cn > holder[0][0] and lib.is_valid(cn, ce, d, D):
            holder[0] = (cn, list(ce))
            stall = 0
        if stall > stall_limit:
            cn, ce = holder[0][0], list(holder[0][1])
            stall = 0


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    expand_deadline = start + 0.35 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    bases = []
    if D == 3:
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            bases.append(lib.projective_plane_incidence(q))
    elif D >= 4:
        qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:3]
        for q in qs:
            if time.monotonic() >= expand_deadline:
                break
            bases.append(_gq_w(q))

    for b in bases:
        consider(b[0], b[1])

    if best[0] >= lib.moore_bound(d, D):
        return best

    # Phase 1: growth from bases (and occasionally from the best graph).
    rot = 0
    idle = 0
    while bases and time.monotonic() < expand_deadline and idle < 4:
        if rng.random() < 0.3:
            src = best
        else:
            src = bases[rot % len(bases)]
            rot += 1
        before = best[0]
        n2, e2 = _expand(src[0], src[1], d, D, expand_deadline, rng)
        consider(n2, e2)
        idle = idle + 1 if best[0] == before else 0

    # Phase 2: iterated local search on the best graph found.
    if time.monotonic() < deadline and best[0] >= 2:
        holder = [best]
        _ils(best[0], best[1], d, D, deadline, rng, holder)
        if holder[0][0] > best[0] and lib.is_valid(holder[0][0], holder[0][1], d, D):
            best = holder[0]

    return best
