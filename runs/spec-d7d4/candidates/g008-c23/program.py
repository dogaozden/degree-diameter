import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases: projective plane (D = 3) and generalized quadrangle W(q) (D = 4).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
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


# ----------------------------------------------------------------------------
# Shared helpers.
# ----------------------------------------------------------------------------

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


def _saturate_edges(n, edges, d, rng):
    """Join deficient opposite-side vertices with spare degree (never increases distances)."""
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


# ----------------------------------------------------------------------------
# Twin augmentation: a twin of x has x's neighbourhood, so distances are kept.
# ----------------------------------------------------------------------------

def _twin_packing(n, adj, slack, rng, deadline):
    cand = [x for x in range(n) if adj[x] and all(slack[w] > 0 for w in adj[x])]
    if not cand:
        return []
    inset = [False] * n
    load = [0] * n

    def take(x):
        inset[x] = True
        for w in adj[x]:
            load[w] += 1

    def drop(x):
        inset[x] = False
        for w in adj[x]:
            load[w] -= 1

    def fill(order):
        for x in order:
            if not inset[x] and all(load[w] < slack[w] for w in adj[x]):
                take(x)

    order = cand[:]
    rng.shuffle(order)
    fill(order)
    best = [x for x in cand if inset[x]]
    while time.monotonic() < deadline:
        chosen = [x for x in cand if inset[x]]
        if not chosen:
            break
        for x in rng.sample(chosen, min(rng.randint(1, 3), len(chosen))):
            drop(x)
        order = cand[:]
        rng.shuffle(order)
        fill(order)
        cur = sum(1 for x in cand if inset[x])
        if cur > len(best):
            best = [x for x in cand if inset[x]]
        elif cur < len(best) - 2 or rng.random() < 0.01:
            for x in cand:
                if inset[x]:
                    drop(x)
            for x in best:
                take(x)
    return best


def _twin_augment(n, edges, d, rng, deadline):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    slack = [max(0, d - len(a)) for a in adj]
    chosen = _twin_packing(n, adj, slack, rng, deadline)
    E = list(edges)
    N = n
    for x in chosen:
        for w in adj[x]:
            E.append((N, w))
        N += 1
    return N, E


# ----------------------------------------------------------------------------
# Degree-conserving repair annealing: insert one vertex and anneal the number
# of pairs at distance > D to zero using 2-switches, transfers and links.
# ----------------------------------------------------------------------------

def _bad_count(n, adj, D):
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _apply_ops(adj, ops):
    for t, x, y in ops:
        if t == 'a':
            adj[x].add(y)
            adj[y].add(x)
        else:
            adj[x].discard(y)
            adj[y].discard(x)


def _undo_ops(adj, ops):
    for t, x, y in reversed(ops):
        if t == 'a':
            adj[x].discard(y)
            adj[y].discard(x)
        else:
            adj[x].add(y)
            adj[y].add(x)


def _propose(N, adj, color, d, rng):
    r = rng.random()
    if r < 0.4:
        p = rng.randrange(N)
        if not adj[p]:
            return None
        q = rng.choice(tuple(adj[p]))
        a, b = (p, q) if color[p] == 0 else (q, p)
        p = rng.randrange(N)
        if not adj[p]:
            return None
        q = rng.choice(tuple(adj[p]))
        c, e = (p, q) if color[p] == 0 else (q, p)
        if a == c or b == e or e in adj[a] or b in adj[c]:
            return None
        return [('d', a, b), ('d', c, e), ('a', a, e), ('a', c, b)]
    defs = [[], []]
    for v in range(N):
        if len(adj[v]) < d:
            defs[color[v]].append(v)
    if r < 0.8:
        s = rng.randrange(2)
        if not defs[s]:
            return None
        x = rng.choice(defs[s])
        b = rng.randrange(N)
        if color[b] == s or not adj[b] or b in adj[x]:
            return None
        a = rng.choice(tuple(adj[b]))
        return [('d', a, b), ('a', x, b)]
    if not defs[0] or not defs[1]:
        return None
    x = rng.choice(defs[0])
    y = rng.choice(defs[1])
    if y in adj[x]:
        return None
    return [('a', x, y)]


def _repair_anneal(n, edges, d, D, deadline, rng):
    adj0 = [[] for _ in range(n)]
    for u, v in edges:
        adj0[u].append(v)
        adj0[v].append(u)
    color = _bipartition(n, adj0)
    N = n + 1
    color.append(rng.randrange(2))
    adj = [set(a) for a in adj0] + [set()]

    cur = _bad_count(N, adj, D)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - t0) / span
        T = 1.0 * (0.03 ** frac)
        ops = _propose(N, adj, color, d, rng)
        if ops is None:
            continue
        _apply_ops(adj, ops)
        new = _bad_count(N, adj, D)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
        else:
            _undo_ops(adj, ops)
    out = [(a, b) for a in range(N) if color[a] == 0 for b in adj[a]]
    return N, out


# ----------------------------------------------------------------------------
# Main driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and degree d.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    try:
        if D == 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if lib.is_valid(pg[0], pg[1], d, D):
                    e2 = _saturate_edges(pg[0], pg[1], d, rng)
                    consider(pg[0], e2)

        elif D >= 4:
            # Bases: generalized quadrangles W(q) with q + 1 <= d.
            qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
            bases = []
            for q in qs:
                if time.monotonic() >= start + 0.2 * time_limit:
                    break
                gn, ge = _gq_w(q)
                consider(gn, ge)
                if lib.is_valid(gn, ge, d, D):
                    bases.append((gn, ge))
            if bases:
                # Phase A: twin augmentation of each base, then saturation.
                phase_end = start + 0.35 * time_limit
                for idx, (gn, ge) in enumerate(bases):
                    now = time.monotonic()
                    if now >= phase_end:
                        break
                    share = (phase_end - now) / (len(bases) - idx)
                    tn, te = _twin_augment(gn, ge, d, rng, now + share)
                    te = _saturate_edges(tn, te, d, rng)
                    consider(tn, te)

            # Phase B: alternate twin re-augmentation of the current best with
            # repair insertions (new vertex annealed into diameter D).
            fails = 0
            while time.monotonic() < deadline - 0.5:
                r = rng.random()
                if r < 0.5 or fails >= 4:
                    short = min(deadline, time.monotonic() + 0.05 * time_limit)
                    tn, te = _twin_augment(best[0], best[1], d, rng, short)
                    te = _saturate_edges(tn, te, d, rng)
                    consider(tn, te)
                    fails = 0 if tn > best[0] else fails
                    if fails >= 4:
                        fails = 0
                else:
                    now = time.monotonic()
                    slice_end = min(deadline, now + max(2.0, 0.12 * time_limit))
                    res = _repair_anneal(best[0], best[1], d, D, slice_end, rng)
                    if res is not None and lib.is_valid(res[0], res[1], d, D):
                        consider(res[0], res[1])
                        fails = 0
                    else:
                        fails += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
