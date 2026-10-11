import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases: projective plane (D = 3) and generalized quadrangle W(q) (D >= 4).
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
# Basic graph helpers.
# ----------------------------------------------------------------------------

def _adj(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


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


def _bad(n, adj, D):
    return sum(n - b.bit_count() for b in _balls(n, adj, D)) // 2


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


# ----------------------------------------------------------------------------
# Twin augmentation: twins keep distances and bipartiteness; they need spare
# degree at every neighbour. Chosen twins are packed by randomized greedy.
# ----------------------------------------------------------------------------

def _twin_augment(n, edges, d, rng, deadline, max_iter=200):
    adj = _adj(n, edges)
    slack = [max(0, d - len(a)) for a in adj]
    cand = [x for x in range(n) if adj[x] and all(slack[w] > 0 for w in adj[x])]
    best = []
    it = 0
    while cand and it < max_iter and time.monotonic() < deadline:
        it += 1
        load = [0] * n
        chosen = []
        order = cand[:]
        rng.shuffle(order)
        for x in order:
            if all(load[w] < slack[w] for w in adj[x]):
                chosen.append(x)
                for w in adj[x]:
                    load[w] += 1
        if len(chosen) > len(best):
            best = chosen
    E = list(edges)
    N = n
    for x in best:
        for w in adj[x]:
            E.append((N, w))
        N += 1
    return N, E


# ----------------------------------------------------------------------------
# Cover-based growth: a new vertex joined to S keeps the diameter bound iff the
# radius-(D-1) balls of S cover all vertices on the other side of the bound.
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


def _extend_cover(n, edges, d, D, deadline, rng, restarts):
    if D < 2:
        return n, list(edges)
    edges = list(edges)
    adj = _adj(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        N = len(adj)
        full = (1 << N) - 1
        ball = _balls(N, adj, D - 1)
        added = False
        for c in (0, 1):
            cands = [s for s in range(N) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for att in range(restarts):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, att > 0)
                if chosen:
                    break
            if chosen:
                v = N
                adj.append([])
                deg.append(0)
                color.append(1 - c)
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
    return len(adj), edges


def _saturate_edges(n, edges, d, rng):
    """Add random edges between non-adjacent opposite-side vertices with spare degree."""
    edges = list(edges)
    adj = _adj(n, edges)
    existing = {(min(u, v), max(u, v)) for u, v in edges}
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng, restarts=100):
    cur_n, cur_e = n, list(edges)
    for _ in range(6):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, restarts)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Excision: delete one vertex (chosen as the best of k random tries by bad
# pairs). Saturation is used to repair the diameter; the candidate is only
# kept if it is fully diameter-valid.
# ----------------------------------------------------------------------------

def _remove_vertex(n, edges, x):
    def mp(v):
        return v if v < x else v - 1
    e2 = [(mp(u), mp(v)) for u, v in edges if u != x and v != x]
    return n - 1, e2


def _excise(n, edges, d, D, rng, k):
    best = None
    for _ in range(k):
        x = rng.randrange(n)
        n2, e2 = _remove_vertex(n, edges, x)
        if n2 < 2:
            continue
        b = _bad(n2, _adj(n2, e2), D)
        if b > 0:
            e2 = _saturate_edges(n2, e2, d, rng)
            b = _bad(n2, _adj(n2, e2), D)
        if best is None or b < best[0]:
            best = (b, n2, e2)
    if best is None or best[0] > 0:
        return None
    return best[1], best[2]


# ----------------------------------------------------------------------------
# Main driver.
#   Phase 0: structured bases (PG(2,q), Araujo-Pardo-Lopez, W(q)).
#   Phase 1: expansion by twin packing plus cover growth.
#   Phase 2: iterated local search with plateau acceptance (excise + regrow,
#            or twin + regrow). Every stored graph is verified with lib.is_valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # ---- Phase 0: bases -----------------------------------------------------
    bases = []
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                try:
                    pg = lib.projective_plane_incidence(q)
                    bases.append(pg)
                    consider(pg[0], pg[1])
                except Exception:
                    pass
                break
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                ar = lib.araujo_lopez_graph(d - 2)
                bases.append(ar)
                consider(ar[0], ar[1])
            except Exception:
                pass
    else:
        qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
        for q in qs:
            if time.monotonic() >= start + 0.15 * T:
                break
            try:
                gq = _gq_w(q)
                bases.append(gq)
                consider(gq[0], gq[1])
            except Exception:
                pass

    # Calibration shortcut: already at the Moore bound.
    if best_n >= lib.moore_bound(d, D):
        return best

    expand_dl = start + 0.35 * T
    ils_dl = start + 0.85 * T

    # ---- Phase 1: expansion -------------------------------------------------
    while time.monotonic() < expand_dl:
        if bases and rng.random() < 0.5:
            src = bases[rng.randrange(len(bases))]
        else:
            src = best
        cn, ce = src[0], list(src[1])
        for _ in range(4):
            if time.monotonic() >= expand_dl:
                break
            n_prev = cn
            try:
                cn, ce = _twin_augment(cn, ce, d, rng,
                                       min(expand_dl, time.monotonic() + 0.05 * T))
                cn, ce = _grow(cn, ce, d, D, expand_dl, rng, 100)
            except Exception:
                break
            if cn == n_prev:
                break
        consider(cn, ce)

    # ---- Phase 2: iterated local search with plateau acceptance -------------
    cn, ce = best_n, list(best[1])
    while time.monotonic() < ils_dl:
        try:
            if rng.random() < 0.2:
                tn, te = _twin_augment(cn, ce, d, rng,
                                       min(ils_dl, time.monotonic() + 0.02 * T), 30)
            else:
                res = _excise(cn, ce, d, D, rng, 4)
                if res is None:
                    continue
                tn, te = res
            tn, te = _grow(tn, te, d, D, ils_dl, rng, 60)
        except Exception:
            continue
        if tn >= cn:
            cn, ce = tn, te
            if tn > best_n:
                consider(tn, te)

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
