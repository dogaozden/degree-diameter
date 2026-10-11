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
# NEW: add-and-repair with 2-switch annealing.
#
# A "2-switch" takes two edges a-b and c-e (a, c on side A; b, e on side B)
# and rewires them to a-e and c-b. Every degree is preserved and bipartiteness
# is kept automatically, so the search can repair a graph freely within the
# degree budget. The new step: attach one extra vertex on the cover-greedy
# set S of the opposite side (possibly leaving some vertices uncovered), then
# run 2-switch moves that minimise the number of pairs at distance > D until
# none remain. Accepted results are strictly larger graphs, saturated and
# re-checked by lib.is_valid.
# ----------------------------------------------------------------------------

def _pick_cover(pool, ball, d, rng):
    """Greedily pick up to d vertices from pool maximising newly covered balls."""
    pool = list(pool)
    rng.shuffle(pool)
    covered = 0
    chosen = []
    while pool and len(chosen) < d:
        best = -1
        opts = []
        for idx, s in enumerate(pool):
            g = (ball[s] & ~covered).bit_count()
            if g > best:
                best = g
                opts = [idx]
            elif g == best:
                opts.append(idx)
        if best <= 0:
            break
        i = rng.choice(opts)
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen


def _two_switch_repair(n, E, d, D, rng, deadline):
    """E: list of (a, b) with a on side 0 and b on side 1. Returns repaired E or None."""
    E = list(E)
    m = len(E)
    S = set(E)
    cur = _bad(n, _adj(n, E), D)
    if cur == 0:
        return E
    if m < 2:
        return None
    while cur > 0 and time.monotonic() < deadline:
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c2, e = E[j]
        if a == c2 or b == e:
            continue
        n1 = (a, e)
        n2 = (c2, b)
        if n1 in S or n2 in S:
            continue
        E2 = E[:]
        E2[i] = n1
        E2[j] = n2
        b2 = _bad(n, _adj(n, E2), D)
        if b2 <= cur or rng.random() < 0.002:
            E = E2
            S.discard((a, b))
            S.discard((c2, e))
            S.add(n1)
            S.add(n2)
            cur = b2
    return E if cur == 0 else None


def _add_and_repair(n, edges, d, D, rng, deadline):
    adj = _adj(n, edges)
    color = _bipartition(n, adj)
    deg = [len(a) for a in adj]
    c = rng.randrange(2)
    pool = [s for s in range(n) if color[s] == c and deg[s] < d]
    if not pool:
        return None
    ball = _balls(n, adj, D - 1)
    S = _pick_cover(pool, ball, d, rng)
    if not S:
        return None
    v = n
    N = n + 1
    E = list(edges) + [(s, v) for s in S]
    col = color + [1 - c]
    E = [(u, w) if col[u] == 0 else (w, u) for u, w in E]
    E = _two_switch_repair(N, E, d, D, rng, deadline)
    if E is None:
        return None
    E = _saturate_edges(N, E, d, rng)
    return N, E


# ----------------------------------------------------------------------------
# Main driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
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

    # ---- Main search ---------------------------------------------------------
    while time.monotonic() < deadline and best_n < lib.moore_bound(d, D):
        try:
            r = rng.random()
            if r < 0.4:
                res = _drop_refill(best_n, best[1], d, D, rng, deadline)
                if res is not None:
                    consider(res[0], res[1])
            elif r < 0.7:
                dl = min(deadline, time.monotonic() + 0.10 * T)
                res = _add_and_repair(best_n, best[1], d, D, rng, dl)
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
