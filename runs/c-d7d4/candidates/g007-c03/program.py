import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured bases.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Degree q + 1, diameter 4, order 2(q+1)(q^2+1).
    """
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


def _best_gq(d):
    """W(q) incidence graph for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared graph helpers.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
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
    """Two-colouring of a bipartite graph given by adjacency lists or sets."""
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


def _to_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidates. Returns list or None."""
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
    """Greedily add vertices whose neighbourhoods are covers of the vertices at distance D-1."""
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
    """Greedily join deficient opposite-side vertices in random order. Only shortens distances."""
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


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
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
# Twin duplication: a non-adjacent twin w of v (N(w) = N(v)) keeps all distances
# to other vertices, is at distance 2 from v, stays on v's side, and only needs
# spare degree on the neighbours of v.
# ----------------------------------------------------------------------------

def _duplicate_twins(n, edges, d, rng):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    changed = True
    while changed:
        changed = False
        order = list(range(len(adj)))
        rng.shuffle(order)
        for v in order:
            nb = adj[v]
            if not nb or len(nb) > d:
                continue
            if any(len(adj[u]) >= d for u in nb):
                continue
            w = len(adj)
            adj.append(set(nb))
            for u in nb:
                adj[u].add(w)
            changed = True
    out = [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]
    return len(adj), out


def _trial(base_n, base_e, d, D, rng, deadline):
    """One randomized pipeline mixing twin duplication, cover growth and saturation."""
    mode = rng.randrange(3)
    n, e = base_n, list(base_e)
    if mode == 0:
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    elif mode == 1:
        n, e = _grow(n, e, d, D, deadline, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    else:
        e = _saturate_edges(n, e, d, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    return n, e


# ----------------------------------------------------------------------------
# NEW: bi-Cayley (Haar-type) graphs over small finite groups.
#
# Vertices a_x (x in G) and b_y (y in G); a_x ~ b_y iff x^{-1} y in S, |S| = d.
# Left multiplication is an automorphism, so every pair is equivalent to a pair
# involving a_1 or b_1. Diameter <= D holds iff the D-ball of a_1 and the D-ball
# of b_1 both cover everything. This gives a cheap, smooth hill-climb cost over
# the connection set S, and non-abelian groups avoid the abelian collisions.
# ----------------------------------------------------------------------------

def _make_group(G, rng):
    """Return (G, mulT, invT) for a random group of order G (cyclic or semidirect), or None."""
    if G < 2:
        return None
    if rng.random() < 0.25:
        order, mul, inv = lib.cyclic_group(G)
    else:
        ks = [k for k in range(2, G + 1) if G % k == 0 and G // k >= 2]
        if not ks:
            return None
        k = rng.choice(ks)
        m = G // k
        cands = []
        for r in rng.sample(range(1, m), min(m - 1, 60)):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                cands.append(r)
        if not cands:
            return None
        r = rng.choice(cands)
        try:
            order, mul, inv = lib.semidirect_group(m, k, r)
        except ValueError:
            return None
    if order != G:
        return None
    mulT = [[mul(x, y) for y in range(G)] for x in range(G)]
    invT = [inv(x) for x in range(G)]
    return G, mulT, invT


def _bicay_cost(G, S, mulT, invT, D):
    """Number of unreached vertices from a_1 and from b_1 within distance D (0 iff diameter <= D)."""
    Sinv = [invT[s] for s in S]
    N = 2 * G

    def reach(src):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < G:
                    row = mulT[v]
                    nb = [G + row[s] for s in S]
                else:
                    row = mulT[v - G]
                    nb = [row[si] for si in Sinv]
                for u in nb:
                    if not seen[u]:
                        seen[u] = 1
                        nxt.append(u)
                        cnt += 1
            if not nxt:
                break
            frontier = nxt
        return cnt

    return (N - reach(0)) + (N - reach(G))


def _hill_bicay(G, d, D, mulT, invT, rng, iters, deadline):
    """Hill-climb a d-element connection set S. Returns S with diameter <= D, or None."""
    S = rng.sample(range(G), d)
    cur = _bicay_cost(G, S, mulT, invT, D)
    for _ in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            return None
        i = rng.randrange(d)
        t = rng.randrange(G)
        if t in S:
            continue
        old = S[i]
        S[i] = t
        c = _bicay_cost(G, S, mulT, invT, D)
        if c <= cur:
            cur = c
        else:
            S[i] = old
    return S if cur == 0 else None


def _bicay_edges(G, S, mulT):
    """Edges of the bi-Cayley graph: a_x = x, b_y = G + y."""
    return [(x, G + mulT[x][s]) for x in range(G) for s in S]


def _bicayley_phase(d, D, best, moore, rng, deadline, consider):
    """Push the bi-Cayley order upward: find a group and S giving diameter <= D on 2G vertices."""
    while time.monotonic() < deadline and best["n"] < moore:
        G = max(best["n"] // 2 + 1, d) + rng.randrange(0, 3)
        for _ in range(6):
            if time.monotonic() >= deadline:
                return
            grp = _make_group(G, rng)
            if grp is None:
                continue
            Gg, mulT, invT = grp
            S = _hill_bicay(Gg, d, D, mulT, invT, rng, 1200, deadline)
            if S is not None:
                consider(2 * Gg, _bicay_edges(Gg, S, mulT))
                break


# ----------------------------------------------------------------------------
# Repair search: add a vertex, free the degree it needs, then anneal with
# bipartite double-edge switches until the diameter bound holds again.
# ----------------------------------------------------------------------------

def _cost(adj, D):
    """Number of vertex pairs at distance more than D."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _add_vertex(adj, color, d, D, side, rng):
    """Append a vertex on the opposite side of `side`, joined to a greedy cover of `side`."""
    n = len(adj)
    ball = _balls_radius(n, adj, D - 1)
    covered = 0
    chosen = []
    cands = [s for s in range(n) if color[s] == side]
    for _ in range(d):
        best_s, best_g = None, -1.0
        for s in cands:
            if s in chosen:
                continue
            g = (ball[s] & ~covered).bit_count() + 0.5 * rng.random()
            if g > best_g:
                best_s, best_g = s, g
        if best_s is None:
            break
        chosen.append(best_s)
        covered |= ball[best_s]
    v = n
    adj.append(set())
    color.append(1 - side)
    for s in chosen:
        if len(adj[s]) >= d:
            t = rng.choice(tuple(adj[s]))
            adj[s].discard(t)
            adj[t].discard(s)
        adj[s].add(v)
        adj[v].add(s)
    return v


def _fill(adj, color, d, rng):
    """Add cross-side edges between deficient vertices (only helps the diameter)."""
    n = len(adj)
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)


def _anneal(adj, color, d, D, rng, iters, deadline):
    """Bipartite double-edge switches (degrees kept) minimising bad pairs. True if cost reaches 0."""
    cur = _cost(adj, D)
    side0 = [v for v in range(len(adj)) if color[v] == 0]
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        a = rng.choice(side0)
        if not adj[a]:
            continue
        b = rng.choice(tuple(adj[a]))
        c = rng.choice(side0)
        if c == a or not adj[c]:
            continue
        e = rng.choice(tuple(adj[c]))
        if e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new = _cost(adj, D)
        if new <= cur or (new == cur + 1 and rng.random() < 0.1):
            cur = new
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    return cur == 0


def _repair(d, D, n, edges, deadline, rng, consider):
    """Repeatedly try to add one vertex to the current valid graph, repairing by annealing."""
    adj = _to_sets(n, edges)
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        snap_adj = [set(s) for s in adj]
        snap_color = list(color)
        side = rng.randrange(2)
        _add_vertex(adj, color, d, D, side, rng)
        _fill(adj, color, d, rng)
        if _anneal(adj, color, d, D, rng, 1500, deadline):
            m = len(adj)
            e = [(u, v) for u in range(m) for v in adj[u] if u < v]
            consider(m, e)
        else:
            adj[:] = snap_adj
            color[:] = snap_color


# ----------------------------------------------------------------------------
# Voltage lifts over non-cyclic groups (semidirect products Z_m x| Z_k2).
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product of order G, or None."""
    for _ in range(60):
        k2 = rng.randint(1, 12)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 40))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _group_search(d, D, k, G, rng, iters, deadline):
    """Hill-climb dart voltages in a group of order about G over a random d-regular base."""
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    if order < 2:
        return None
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(order)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.group_lift(2 * k, [tuple(x) for x in darts], order, mul)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        j = rng.randrange(len(darts))
        old = darts[j][2]
        darts[j][2] = (old + rng.randrange(1, order)) % order
        n2, e2, c2 = evaluate()
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            darts[j][2] = old
    if c == 0:
        return n, e
    return None


def _group_phase(d, D, best, rng, deadline, consider):
    """Adaptive group-lift search; `best` is a dict holding the current best 'n'."""
    group_sizes = [1, 2, 3, 4]
    state = {k: {"G": 1, "step": 1, "miss": 0} for k in group_sizes}
    while time.monotonic() < deadline:
        k = rng.choice(group_sizes)
        st = state[k]
        floor = best["n"] // (2 * k) + 1
        G = max(st["G"], floor, 2)
        res = _group_search(d, D, k, G, rng, 200, deadline)
        if res is not None:
            consider(res[0], res[1])
            st["G"] = G + st["step"]
            st["step"] = min(st["step"] * 2, max(1, G // 10))
            st["miss"] = 0
        else:
            st["G"] = G
            st["miss"] += 1
            if st["miss"] >= 3:
                st["step"] = 1
                st["miss"] = 0
                st["G"] = floor


# ----------------------------------------------------------------------------
# Main build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.88 * time_limit
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best = {"n": fb_n, "e": list(fb_e)}
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        if n > best["n"] and lib.is_valid(n, e, d, D):
            best["n"] = n
            best["e"] = list(e)

    # Structured base: W(q) for D >= 4, PG(2, q) for D = 3.
    base_n, base_e = best["n"], list(best["e"])
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            n1, e1 = _grow(n0, e0, d, D, start + 0.10 * time_limit, rng)
            consider(n1, e1)

    # NEW: bi-Cayley family over non-abelian groups, a different construction from
    # the structured bases. Skipped when the Moore-type ceiling is already reached.
    if D >= 3 and d >= 2 and best["n"] < moore:
        _bicayley_phase(d, D, best, moore, rng, start + 0.50 * time_limit, consider)

    # Group-lift family: alternative structure, mainly useful for D >= 4.
    if D >= 4 and best["n"] < moore:
        _group_phase(d, D, best, rng, start + 0.58 * time_limit, consider)

    # Randomized twin / growth pipelines from the structured base and the best graph.
    if D >= 2 and best["n"] < moore:
        trial_end = start + 0.70 * time_limit
        while time.monotonic() < trial_end:
            if rng.random() < 0.5:
                src_n, src_e = base_n, base_e
            else:
                src_n, src_e = best["n"], best["e"]
            n, e = _trial(src_n, src_e, d, D, rng, trial_end)
            consider(n, e)

    # Repair stage: add vertices to the largest valid graph and anneal back to validity.
    if D >= 2 and best["n"] < moore and time.monotonic() < deadline:
        _repair(d, D, best["n"], best["e"], deadline, rng, consider)

    n_out, e_out = best["n"], best["e"]
    if not lib.is_valid(n_out, e_out, d, D):
        return lib.haar_graph(d, range(d))
    return n_out, list(e_out)
