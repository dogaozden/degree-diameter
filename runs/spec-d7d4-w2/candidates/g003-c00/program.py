import itertools
import math
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
# NEW: vertex-transitive group lifts of a small bipartite base.
#
# Base: s A-vertices and s B-vertices with darts (i, j, g) of a d-regular
# multigraph. Lift over a group G of order M: A(i,x) ~ B(j, x*g) for every
# dart and every x in G. Left multiplication by h is an automorphism, so each
# fibre is transitive and diameter <= 4 is equivalent to every base vertex
# A(i,e), B(j,e) reaching all 2*s*M vertices within 4 steps.
# Search: simulated annealing over the dart group elements, minimising the
# total number of unreached vertices.
# ----------------------------------------------------------------------------

_LIFT_DIAM = 4


def _groups(M):
    """All semidirect products Z_m x| Z_k (m*k = M, m >= 2) as (m, k, r) triples."""
    out = []
    for k in range(1, M + 1):
        if M % k:
            continue
        m = M // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _unreached(s, M, from_A, into_B, MT, start, D):
    N = 2 * s * M
    off = s * M
    seen = bytearray(N)
    seen[start] = 1
    frontier = [start]
    reached = 1
    for _ in range(D):
        nxt = []
        for v in frontier:
            if v < off:
                i, x = divmod(v, M)
                row = MT[x]
                for j, g in from_A[i]:
                    w = off + j * M + row[g]
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            else:
                j, y = divmod(v - off, M)
                row = MT[y]
                for i, gi in into_B[j]:
                    w = i * M + row[gi]
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
        reached += len(nxt)
        frontier = nxt
        if not frontier:
            break
    return N - reached


def _cost(s, M, darts, MT, INV, D):
    from_A = [[] for _ in range(s)]
    into_B = [[] for _ in range(s)]
    for i, j, g in darts:
        from_A[i].append((j, g))
        into_B[j].append((i, INV[g]))
    off = s * M
    total = 0
    for i in range(s):
        total += _unreached(s, M, from_A, into_B, MT, i * M, D)
    for j in range(s):
        total += _unreached(s, M, from_A, into_B, MT, off + j * M, D)
    return total


def _anneal_once(s, M, d, rng, deadline):
    groups = _groups(M)
    if not groups:
        return None
    m, k, r = rng.choice(groups)
    order, mul, inv = lib.semidirect_group(m, k, r)
    if order != M:
        return None
    MT = [[mul(x, y) for y in range(M)] for x in range(M)]
    INV = [inv(x) for x in range(M)]

    if s == 2:
        kk = rng.randint(1, d - 1)
        cnt = [[kk, d - kk], [d - kk, kk]]
    else:
        cnt = [[d]]
    darts = []
    for i in range(s):
        for j in range(s):
            for g in rng.sample(range(M), cnt[i][j]):
                darts.append([i, j, g])

    cur = _cost(s, M, darts, MT, INV, _LIFT_DIAM)
    steps = 2500
    for step in range(steps):
        if cur == 0 or time.monotonic() >= deadline:
            break
        temp = 2.0 * (1.0 - step / steps) + 0.1
        t = rng.randrange(len(darts))
        i, j, old = darts[t]
        used = {g for a, b, g in darts if a == i and b == j}
        free = [g for g in range(M) if g not in used]
        if not free:
            continue
        darts[t][2] = rng.choice(free)
        nc = _cost(s, M, darts, MT, INV, _LIFT_DIAM)
        if nc <= cur or rng.random() < math.exp(-(nc - cur) / temp):
            cur = nc
        else:
            darts[t][2] = old

    if cur != 0:
        return None
    off = s * M
    edges = []
    for i, j, g in darts:
        for x in range(M):
            edges.append((i * M + x, off + j * M + MT[x][g]))
    n = 2 * s * M
    if lib.is_valid(n, edges, d, _LIFT_DIAM):
        return (n, edges)
    return None


def _lift_search(d, s, M_lo, M_hi, rng, deadline):
    """Ascend M while annealing succeeds; return the largest valid (n, edges) found."""
    best = None
    M = M_lo
    while M <= M_hi and time.monotonic() < deadline:
        slice_end = min(deadline, time.monotonic() + (8.0 if s == 2 else 12.0))
        res = None
        while res is None and time.monotonic() < slice_end:
            res = _anneal_once(s, M, d, rng, slice_end)
        if res is None:
            break
        best = res
        M += 1
    return best


# ----------------------------------------------------------------------------
# Twin augmentation: add twins of a packed vertex set within spare degree.
# ----------------------------------------------------------------------------

def _twin_augment(n, edges, d, rng, deadline):
    adj = _adj(n, edges)
    slack = [max(0, d - len(a)) for a in adj]
    cand = [x for x in range(n) if adj[x] and all(slack[w] > 0 for w in adj[x])]
    best = []
    while True:
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
        if time.monotonic() >= deadline or not cand:
            break
    E = list(edges)
    N = n
    for x in best:
        for w in adj[x]:
            E.append((N, w))
        N += 1
    return N, E


# ----------------------------------------------------------------------------
# Cover-based vertex extension (diameter-preserving) and edge saturation.
# A new vertex v joined to a set S keeps the diameter bound iff the balls of
# radius D-1 around S cover all existing vertices.
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
# Drop-and-refill local search.
# ----------------------------------------------------------------------------

def _remove_vertex(n, edges, x):
    def mp(v):
        return v if v < x else v - 1
    e2 = [(mp(u), mp(v)) for u, v in edges if u != x and v != x]
    return n - 1, e2


def _drop_refill(n, edges, d, D, rng, deadline, tries=12):
    best = None
    for _ in range(tries):
        if time.monotonic() >= deadline:
            break
        x = rng.randrange(n)
        n2, e2 = _remove_vertex(n, edges, x)
        b = _bad(n2, _adj(n2, e2), D)
        if best is None or b < best[0]:
            best = (b, n2, e2)
    if best is None:
        return None
    _, n2, e2 = best
    m3, e3 = _grow(n2, e2, d, D, deadline, rng, 60)
    if m3 > n and lib.is_valid(m3, e3, d, D):
        return m3, e3
    return None


# ----------------------------------------------------------------------------
# Legacy pipeline (previous parent), used as fallback and for non-target cases.
# ----------------------------------------------------------------------------

def _legacy_build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    deadline = start + 0.84 * T
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # ---- Phase 0: structured bases ------------------------------------------
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                try:
                    pg = lib.projective_plane_incidence(q)
                    consider(pg[0], pg[1])
                except Exception:
                    pass
                break
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                ar = lib.araujo_lopez_graph(d - 2)
                consider(ar[0], ar[1])
            except Exception:
                pass
    elif D >= 4:
        qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
        twin_deadline = start + 0.30 * T
        for idx, q in enumerate(qs):
            now = time.monotonic()
            if now >= twin_deadline:
                break
            try:
                gq = _gq_w(q)
                consider(gq[0], gq[1])
                share = (twin_deadline - now) / (len(qs) - idx)
                tn, te = _twin_augment(gq[0], gq[1], d, rng, time.monotonic() + share)
                consider(tn, te)
                n2, e2 = _grow(tn, te, d, D, min(deadline, time.monotonic() + 0.05 * T), rng, 200)
                consider(n2, e2)
            except Exception:
                pass

    # ---- Main search: drop-and-refill, twins, and regrowth -------------------
    while time.monotonic() < deadline and best_n < lib.moore_bound(d, D):
        try:
            r = rng.random()
            if r < 0.6:
                res = _drop_refill(best_n, best[1], d, D, rng, deadline)
                if res is not None:
                    consider(res[0], res[1])
            elif r < 0.85:
                short = min(deadline, time.monotonic() + 0.04 * T)
                tn, te = _twin_augment(best_n, best[1], d, rng, short)
                consider(tn, te)
                n2, e2 = _grow(tn, te, d, D, min(deadline, time.monotonic() + 0.02 * T), rng, 200)
                consider(n2, e2)
            else:
                short = min(deadline, time.monotonic() + 0.05 * T)
                n2, e2 = _grow(best_n, best[1], d, D, short, rng, 200)
                consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)

    if not (D == 4 and d == 7):
        try:
            return _legacy_build(d, D, seed, T)
        except Exception:
            return lib.haar_graph(d, range(d))

    # Target case: legacy result first as a safe fallback, then group-lift search.
    try:
        best = _legacy_build(d, D, seed, 0.38 * T)
    except Exception:
        best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    rng = random.Random(seed)
    for s, M_lo, M_hi, dl in ((2, 90, 129, start + 0.60 * T),
                              (1, 179, 259, start + 0.85 * T)):
        try:
            cand = _lift_search(d, s, M_lo, M_hi, rng, dl)
        except Exception:
            cand = None
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand
    return best
