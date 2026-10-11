import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases: generalized quadrangle W(q) (diameter 4) and projective plane (diameter 3).
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
    edges = []
    j = 0
    for i in range(P):
        x = pts[i]
        for k in range(i + 1, P):
            if (i, k) in covered:
                continue
            y = pts[k]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[t]), F.mul(b, y[t])) for t in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            for p in L:
                edges.append((p, P + j))
                for r in L:
                    if p < r:
                        covered.add((p, r))
            j += 1
    return 2 * P, edges


def _gq_base(d):
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _pg_base(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Diameter-preserving growth by cover vertices (greedy set cover), then saturation.
# ----------------------------------------------------------------------------

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


def _extend_cover(n, edges, d, D, deadline, rng):
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
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
            for attempt in range(200):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
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
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# NEW: edge-splice insertion + degree-preserving 2-switch annealing repair.
#
# Insert a point v and a line w (joined to each other) without changing any
# degree: pick d-1 edges (p_i, l_i) with distinct endpoints, replace each by
# (v, l_i) and add (p_i, w). Both new vertices get degree exactly d. Diameter
# is then repaired by annealing over bipartite-preserving 2-switches, with
# cost = number of vertex pairs at distance > D.
# ----------------------------------------------------------------------------

def _state(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _bipartition(n, adj)
    nb = [set() for _ in range(n)]
    E = []
    for u, v in edges:
        p, l = (u, v) if color[u] == 0 else (v, u)
        E.append((p, l))
        nb[p].add(l)
        nb[l].add(p)
    return n, E, nb


def _bad(n, nb, D):
    """Number of unordered vertex pairs at distance > D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in nb[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _replace(E, nb, i, new):
    old = E[i]
    nb[old[0]].discard(old[1])
    nb[old[1]].discard(old[0])
    nb[new[0]].add(new[1])
    nb[new[1]].add(new[0])
    E[i] = new


def _insert(n, E, nb, d, rng):
    """Degree-preserving splice inserting a point (n) and a line (n+1). Returns new n or None."""
    v, w = n, n + 1
    nb.append(set())
    nb.append(set())
    idx = list(range(len(E)))
    rng.shuffle(idx)
    used_p, used_l, chosen = set(), set(), []
    for i in idx:
        p, l = E[i]
        if p in used_p or l in used_l:
            continue
        used_p.add(p)
        used_l.add(l)
        chosen.append(i)
        if len(chosen) == d - 1:
            break
    if len(chosen) < d - 1:
        return None
    for i in chosen:
        p, l = E[i]
        _replace(E, nb, i, (v, l))
        E.append((p, w))
        nb[p].add(w)
        nb[w].add(p)
    E.append((v, w))
    nb[v].add(w)
    nb[w].add(v)
    return n + 2


def _anneal(n, E, nb, D, rng, iters, deadline):
    """Anneal with 2-switches; returns final cost (0 means valid)."""
    cost = _bad(n, nb, D)
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 1.0 * (0.03 ** (it / iters))
        i, j = rng.sample(range(len(E)), 2)
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in nb[a] or b in nb[c]:
            continue
        _replace(E, nb, i, (a, e))
        _replace(E, nb, j, (c, b))
        new = _bad(n, nb, D)
        if new <= cost or rng.random() < math.exp(-(new - cost) / T):
            cost = new
        else:
            _replace(E, nb, j, (c, e))
            _replace(E, nb, i, (a, b))
    return cost


def _splice(n, E, nb, d, D, deadline, rng, moore):
    best = (n, list(E))
    while time.monotonic() < deadline and n + 2 <= moore:
        snap_E = list(E)
        snap_nb = [set(s) for s in nb]
        snap_n = n
        new_n = _insert(n, E, nb, d, rng)
        if new_n is None:
            E[:] = snap_E
            nb[:] = snap_nb
            break
        cost = _anneal(new_n, E, nb, D, rng, 200, deadline)
        if cost == 0:
            n = new_n
            best = (n, list(E))
        else:
            E[:] = snap_E
            nb[:] = snap_nb
            n = snap_n
    return best


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    rng = random.Random(seed)
    best_n, best_e = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    moore = lib._moore_bound(d, D)

    base = None
    if D >= 4:
        base = _gq_base(d)
    if base is None and D >= 3:
        base = _pg_base(d)

    if base is not None:
        n, edges = base
        n1, e1 = _grow(n, edges, d, D, start + 0.4 * time_limit, rng)
        n_s, E, nb = _state(n1, e1)
        if _bad(n_s, nb, D) == 0:
            n_b, E_b = _splice(n_s, E, nb, d, D, deadline, rng, moore)
            if n_b > best_n and lib.is_valid(n_b, E_b, d, D):
                best_n, best_e = n_b, E_b

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
