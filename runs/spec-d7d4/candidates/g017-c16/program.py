"""Experimental D>=4 search: generalized-quadrangle deletion with saturation.

Pipeline for D >= 4:
  1. Twin/cover expansion of W(q) bases (the parent's construction, kept as a safe baseline).
  2. A different construction: start from W(q) with q the smallest prime power >= d,
     which has degree q+1 > d. Delete vertices by simulated annealing until all
     remaining degrees are <= d and the diameter bound holds (cost = bad pairs +
     degree excess). Then add opposite-side edges between spare-capacity vertices
     that are more than D apart. Every candidate is verified with lib.is_valid.
Fallback: K_{d,d}, always verified.
"""
import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base graphs.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of W(q); points 0..P-1, lines P..2P-1; diameter 4."""
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


def _ball_masks(n, nbl, alive, r):
    """Radius-r balls (bitmasks) in the subgraph induced by alive vertices; dead vertices get 0."""
    ball = [(1 << v) if alive[v] else 0 for v in range(n)]
    for _ in range(r):
        new = ball[:]
        changed = False
        for v in range(n):
            if alive[v]:
                x = ball[v]
                for u in nbl[v]:
                    x |= ball[u]
                if x != ball[v]:
                    new[v] = x
                    changed = True
        ball = new
        if not changed:
            break
    return ball


# ----------------------------------------------------------------------------
# Twin blow-up with spare-capacity packing (parent construction).
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


# ----------------------------------------------------------------------------
# Cover-based vertex extension (diameter-preserving growth).
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


def _exact_ball_cover(cands, ball, full, d, budget):
    nodes = [0]

    def rec(covered, chosen):
        unc = full & ~covered
        if unc == 0:
            return chosen
        room = d - len(chosen)
        if room <= 0:
            return None
        nodes[0] += 1
        if nodes[0] > budget:
            return None
        gains = [(ball[s] & unc).bit_count() for s in cands]
        mx = max(gains, default=0)
        if mx == 0 or unc.bit_count() > room * mx:
            return None
        w = (unc & -unc).bit_length() - 1
        opts = [i for i, s in enumerate(cands) if gains[i] > 0 and (ball[s] >> w) & 1]
        opts.sort(key=lambda i: -gains[i])
        for i in opts:
            res = rec(covered | ball[cands[i]], chosen + [cands[i]])
            if res is not None:
                return res
            if nodes[0] > budget:
                return None
        return None

    return rec(0, [])


def _extend_cover(n, edges, d, D, deadline, rng, always_random=False):
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = _adjacency(n, edges)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            if D >= 4 and time.monotonic() < deadline:
                chosen = _exact_ball_cover(cands, ball, full, d, 2000)
            if not chosen:
                for attempt in range(200):
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


def _saturate_edges(n, edges, d, rng):
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


def _grow(n, edges, d, D, deadline, rng, always_random=False):
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, always_random)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _expand(n, edges, d, D, deadline, rng, rounds=6):
    cur_n, cur_e = n, list(edges)
    for _ in range(rounds):
        if time.monotonic() >= deadline:
            break
        n0 = cur_n
        for side in (0, 1):
            iters = rng.choice([3000, 10000, 30000])
            cur_n, cur_e = _twin_pass(cur_n, cur_e, d, side, rng, deadline, iters)
        cur_n, cur_e = _grow(cur_n, cur_e, d, D, deadline, rng)
        if cur_n == n0:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# New construction: deletion search on W(q) with saturation repair.
# ----------------------------------------------------------------------------

def _alive_cost(n, adj, alive, d, D):
    """Cost = bad pairs (distance > D, alive only) + 4 * degree excess over d."""
    nb = [[u for u in adj[v] if alive[u]] if alive[v] else [] for v in range(n)]
    A = sum(alive)
    ball = _ball_masks(n, nb, alive, D)
    bad = 0
    exc = 0
    for v in range(n):
        if alive[v]:
            bad += A - ball[v].bit_count()
            k = len(nb[v])
            if k > d:
                exc += k - d
    return bad // 2 + 4 * exc, bad // 2, exc


def _saturate_lists(n, nb, alive, color, d, D, rng, rounds=30):
    """Greedily add opposite-side edges between spare-capacity alive vertices that are > D apart."""
    nbset = [set(x) for x in nb]
    alive_v = [v for v in range(n) if alive[v]]
    for _ in range(rounds):
        ball = _ball_masks(n, nbset, alive, D)
        deg = [len(s) for s in nbset]
        L = [v for v in alive_v if color[v] == 0 and deg[v] < d]
        R = [v for v in alive_v if color[v] == 1 and deg[v] < d]
        cands = [(a, b) for a in L for b in R if not (ball[a] >> b) & 1]
        if not cands:
            break
        rng.shuffle(cands)
        added = 0
        for a, b in cands:
            if len(nbset[a]) < d and len(nbset[b]) < d and b not in nbset[a]:
                nbset[a].add(b)
                nbset[b].add(a)
                added += 1
        if added == 0:
            break
    return [list(s) for s in nbset]


def _finish(n, adj, alive, color, d, D, rng, consider):
    """Saturate the current alive subgraph, relabel it, and offer it to `consider` (which verifies)."""
    nb = [[u for u in adj[v] if alive[u]] if alive[v] else [] for v in range(n)]
    nb = _saturate_lists(n, nb, alive, color, d, D, rng)
    idx = {}
    for v in range(n):
        if alive[v]:
            idx[v] = len(idx)
    E = set()
    for v in range(n):
        if alive[v]:
            for u in nb[v]:
                a, b = idx[v], idx[u]
                if a < b:
                    E.add((a, b))
    if idx:
        consider(len(idx), sorted(E))


def _deletion_search(q, d, D, deadline, rng, consider):
    n, edges = _gq_w(q)
    P = n // 2
    adj = _adjacency(n, edges)
    color = [0 if v < P else 1 for v in range(n)]
    alive = [True] * n

    # Initial pruning: delete random alive neighbours of over-full vertices.
    for v in range(n):
        while alive[v] and sum(1 for u in adj[v] if alive[u]) > d:
            cands = [u for u in adj[v] if alive[u]]
            alive[rng.choice(cands)] = False

    cost, _, _ = _alive_cost(n, adj, alive, d, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    it = 0
    while time.monotonic() < deadline:
        it += 1
        x = rng.randrange(n)
        alive[x] = not alive[x]
        c2, _, _ = _alive_cost(n, adj, alive, d, D)
        frac = min(1.0, (time.monotonic() - t0) / span)
        T = 0.2 + 5.0 * (1.0 - frac)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            alive[x] = not alive[x]
        if it % 150 == 0:
            _finish(n, adj, alive, color, d, D, rng, consider)
    _finish(n, adj, alive, color, d, D, rng, consider)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    hard = start + 0.85 * time_limit
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

    if best[0] >= lib._moore_bound(d, D):
        return best

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        return best

    if D == 2:
        return best

    # D >= 4: bases and baseline expansion.
    bases = []
    qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)][:2]
    for q in qs:
        gq = _gq_w(q)
        bases.append(gq)
        consider(gq[0], gq[1])

    # Phase 1: baseline twin/cover expansion of the bases.
    expand_deadline = start + 0.25 * time_limit
    rot = 0
    while bases and time.monotonic() < expand_deadline:
        if best[0] > 0 and rng.random() < 0.3:
            src = best
        else:
            src = bases[rot % len(bases)]
            rot += 1
        slice_end = min(expand_deadline, time.monotonic() + 0.12 * time_limit)
        n2, e2 = _expand(src[0], src[1], d, D, slice_end, rng)
        consider(n2, e2)

    # Phase 2: deletion search on W(q), q the smallest prime power >= d (degree q+1 > d).
    qd = next((q for q in range(max(2, d), 10) if lib.is_prime_power(q)), None)
    if qd is not None and time.monotonic() < hard - 1.0:
        try:
            _deletion_search(qd, d, D, hard, rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
