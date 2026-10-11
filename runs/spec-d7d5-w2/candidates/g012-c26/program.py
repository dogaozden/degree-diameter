import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families.
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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l pairs A_i with B_{layers[l][i]} through voltage s: A_{i,g} ~ B_{p,g*s}.
# Every layer is a permutation, so every vertex gets degree d exactly.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                r = None
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e))."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = g*s
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b is set when representative block b is within distance D."""
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _unreached(k, N, reach):
    """Number of unreached (representative, vertex) pairs."""
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters):
    """Simulated annealing over voltages, layer swaps and defect-targeted moves. Returns (n, edges) or None."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    reach = _reach(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
            l = rng.randrange(d)
            if block < k:
                i = block
            else:
                i = layers[l].index(block - k)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        r2 = _reach(k, G, D, nbr, d)
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


# ----------------------------------------------------------------------------
# Bipartition colouring.
# ----------------------------------------------------------------------------

def _two_color(n, edges):
    """Return a proper 2-colouring (list of 0/1) of the graph, or None if it is not bipartite."""
    adj = lib.adjacency(n, edges)
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
                elif color[v] == color[u]:
                    return None
    return color


# ----------------------------------------------------------------------------
# Redundancy-aware pair insertion (kept from the parent).
# ----------------------------------------------------------------------------

def _edge_slack(n, edges, R):
    """Per-edge redundancy: popcount of (ball_R(u) & ball_R(v)) for each edge (u, v)."""
    balls = lib._balls(n, edges, max(1, R))
    return [(balls[u] & balls[v]).bit_count() for u, v in edges]


def _extend_redundant(n, edges, d, D, rng, deadline, max_fails=60):
    """Grow the order by 2 per accepted step, preferring high-redundancy edges to remove."""
    if d < 1 or not edges:
        return n, edges
    color = _two_color(n, edges)
    if color is None:
        return n, edges
    edges = list(edges)
    color = list(color)
    fails = 0
    while time.monotonic() < deadline and fails < max_fails:
        slack = _edge_slack(n, edges, D - 1)
        keys = [slack[t] * (0.8 + 0.4 * rng.random()) for t in range(len(edges))]
        order = sorted(range(len(edges)), key=lambda t: -keys[t])
        chosen = []
        used_a, used_b = set(), set()
        for t in order:
            if len(chosen) == d - 1:
                break
            u, v = edges[t]
            a, b = (u, v) if color[u] == 0 else (v, u)
            if a in used_a or b in used_b:
                continue
            chosen.append(t)
            used_a.add(a)
            used_b.add(b)
        if len(chosen) < d - 1:
            break
        x, y = n, n + 1
        cs = set(chosen)
        cand = [e for t, e in enumerate(edges) if t not in cs]
        for t in chosen:
            u, v = edges[t]
            a, b = (u, v) if color[u] == 0 else (v, u)
            cand.append((x, b))
            cand.append((y, a))
        cand.append((x, y))
        if lib.is_valid(n + 2, cand, d, D):
            edges = cand
            n += 2
            color.extend([0, 1])
            fails = 0
        else:
            fails += 1
    return n, edges


# ----------------------------------------------------------------------------
# NEW: defect-driven 2-switch repair after random pair insertion.
#
# A bipartite 2-switch takes edges (P,q1) and (p2,Q) with P,p2 on one side and
# q1,Q on the other, and replaces them with (P,Q) and (p2,q1). Every degree and
# the bipartition are preserved. Pair insertion adds two vertices x, y (degree d)
# but may leave many pairs too far apart. Instead of rejecting such a grown
# graph, we repair it: pick a defective pair (u, v), aim a new edge from u to a
# vertex x on the opposite side that is within distance 2 of v, and accept the
# switch when the number of bad pairs does not increase. This grows the order
# by 2 with a valid result only if the repair reaches zero bad pairs.
# ----------------------------------------------------------------------------

def _sw_apply(nb, P, Q, q1, p2, forward):
    """Apply (forward) or undo the switch (P,q1),(p2,Q) -> (P,Q),(p2,q1) on adjacency sets."""
    if forward:
        nb[P].discard(q1); nb[q1].discard(P)
        nb[Q].discard(p2); nb[p2].discard(Q)
        nb[P].add(Q); nb[Q].add(P)
        nb[p2].add(q1); nb[q1].add(p2)
    else:
        nb[P].discard(Q); nb[Q].discard(P)
        nb[p2].discard(q1); nb[q1].discard(p2)
        nb[P].add(q1); nb[q1].add(P)
        nb[Q].add(p2); nb[p2].add(Q)


def _switch_repair(n, E0, color, D, rng, deadline, max_evals):
    """Degree-preserving bipartite 2-switches driven by defects. Returns edges with zero bad pairs, or None."""
    nb = [set() for _ in range(n)]
    for u, v in E0:
        nb[u].add(v)
        nb[v].add(u)

    def edge_list():
        return [(u, v) for u in range(n) for v in nb[u] if u < v]

    full = (1 << n) - 1
    reach = lib._balls(n, edge_list(), D)
    cur = sum(n - r.bit_count() for r in reach) // 2
    evals = 0
    while cur > 0 and evals < max_evals and time.monotonic() < deadline:
        defect = [w for w in range(n) if reach[w] != full]
        if not defect:
            break
        u = defect[rng.randrange(len(defect))]
        miss = full ^ reach[u]
        missing = [w for w in range(n) if (miss >> w) & 1]
        v = missing[rng.randrange(len(missing))]

        # Candidate partners x: opposite side to u, at distance <= 2 from v.
        cands = set()
        if color[v] != color[u]:
            cands.add(v)
        for c in nb[v]:
            if color[c] != color[u]:
                cands.add(c)
            for y in nb[c]:
                if color[y] != color[u]:
                    cands.add(y)
        cands.discard(u)
        evals += 1
        if not cands or not nb[u]:
            continue

        P = u
        Q = rng.choice(tuple(cands))
        if Q in nb[P] or not nb[Q]:
            continue
        q1 = rng.choice(tuple(nb[P]))
        p2 = rng.choice(tuple(nb[Q]))
        if q1 == Q or p2 == P or q1 in nb[p2]:
            continue

        _sw_apply(nb, P, Q, q1, p2, True)
        new_reach = lib._balls(n, edge_list(), D)
        new_cost = sum(n - r.bit_count() for r in new_reach) // 2
        if new_cost <= cur:
            cur, reach = new_cost, new_reach
        else:
            _sw_apply(nb, P, Q, q1, p2, False)

    if cur == 0:
        return edge_list()
    return None


def _random_pair_insertion(n, edges, color, d, rng):
    """Pair insertion with random edge choice. Returns (n+2, edges, color) or None."""
    if d < 2 or not edges:
        return None
    order = list(range(len(edges)))
    rng.shuffle(order)
    chosen, ua, ub = [], set(), set()
    for t in order:
        if len(chosen) == d - 1:
            break
        u, v = edges[t]
        a, b = (u, v) if color[u] == 0 else (v, u)
        if a in ua or b in ub:
            continue
        chosen.append((a, b))
        ua.add(a)
        ub.add(b)
    if len(chosen) < d - 1:
        return None
    drop = {(min(a, b), max(a, b)) for a, b in chosen}
    x, y = n, n + 1
    cand = [(u, v) for (u, v) in edges if (min(u, v), max(u, v)) not in drop]
    for a, b in chosen:
        cand.append((x, b))
        cand.append((y, a))
    cand.append((x, y))
    return n + 2, cand, list(color) + [0, 1]


def _grow_repair(n, edges, d, D, rng, deadline, steps=12, evals=250):
    """Repeatedly pair-insert then switch-repair; keep each step only when fully repaired."""
    color = _two_color(n, edges)
    if color is None or d < 2 or not edges:
        return n, edges
    cur_e = list(edges)
    cur_c = list(color)
    for _ in range(steps):
        if time.monotonic() >= deadline:
            break
        pi = _random_pair_insertion(n, cur_e, cur_c, d, rng)
        if pi is None:
            break
        n2, e2, c2 = pi
        res = _switch_repair(n2, e2, c2, D, rng, deadline, evals)
        if res is None:
            break
        n, cur_e, cur_c = n2, res, c2
    return n, cur_e


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.90 * time_limit, time_limit - 5.0))
    deadline = start + budget
    search_deadline = start + 0.75 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < search_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < search_deadline:
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, search_deadline, 4000)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Redundancy-aware pair insertion (valid-only steps).
    try:
        n2, e2 = _extend_redundant(best_n, best[1], d, D, rng, start + 0.85 * budget)
        if n2 > best_n:
            consider(n2, e2)
    except Exception:
        pass

    # Defect-driven switch repair after random pair insertion.
    try:
        n3, e3 = _grow_repair(best_n, best[1], d, D, rng, deadline)
        if n3 > best_n:
            consider(n3, e3)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
