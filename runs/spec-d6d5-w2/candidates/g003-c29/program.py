import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Projective-plane baselines: PG(2,q) incidence, Araujo-Pardo-Lopez, arc
# extensions, and cover/saturation growth.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, point_lines, line_points):
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


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


def _extend_cover(n, edges, d, D, deadline, rng, randomize=False):
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
                chosen = _greedy_cover(cands, ball, full, d, rng, randomize or attempt > 0)
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


def _grow(n, edges, d, D, deadline, rng, randomize=False):
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, randomize)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# NEW: Frobenius-group bi-Cayley graphs.
#
# A bi-Cayley graph over a group G with connection set S (|S| = d):
#   A_g ~ B_{g*s} for s in S.
# Left multiplication acts transitively on A and on B, so the graph has
# diameter <= D iff BFS from A_e and from B_e reaches everything within D.
# Groups are Z_m x|_r Z_k with k | m-1 and m prime (Frobenius-type, e.g.
# AGL(1,19) of order 342 = 19*18), and the search cost is evaluated with
# vectorised numpy BFS over the group multiplication table.
# ----------------------------------------------------------------------------

def _is_prime(n):
    return n >= 2 and all(n % p for p in range(2, int(n ** 0.5) + 1))


def _group_table(m, k, r):
    """Multiplication table of Z_m x|_r Z_k, element (a, b) coded as a*k+b (matches lib.semidirect_group)."""
    G = m * k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    X = np.arange(G, dtype=np.int64)
    a, b = X // k, X % k
    Ax, Bx = a[:, None], b[:, None]
    Ay, By = a[None, :], b[None, :]
    return ((Ax + pw[Bx] * Ay) % m) * k + (Bx + By) % k


def _candidate_groups(lo, hi, rng):
    """(G, m, k, r) tuples with lo <= m*k <= hi. Frobenius-type first (sorted by order), then the rest."""
    fro, gen = [], []
    for m in range(2, hi + 1):
        for k in range(1, hi // m + 1):
            G = m * k
            if G < lo or G > hi:
                continue
            if k == 1:
                gen.append((G, m, 1, 1))
                continue
            rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
            if not rs:
                continue
            rng.shuffle(rs)
            is_fro = _is_prime(m) and (m - 1) % k == 0
            for r in rs[:2]:
                (fro if is_fro else gen).append((G, m, k, r))
    fro.sort()
    rng.shuffle(gen)
    return fro + gen


def _bfs_unreached(Mt, S, Sinv, G, D, side):
    """Pairs unreached within D from the base vertex of `side` (0 = A, 1 = B), counted on both sides."""
    visA = np.zeros(G, dtype=bool)
    visB = np.zeros(G, dtype=bool)
    fr = np.array([0], dtype=np.int64)
    if side == 0:
        visA[0] = True
    else:
        visB[0] = True
    cur = side
    for _ in range(D):
        if fr.size == 0:
            break
        if cur == 0:
            cand = Mt[fr[:, None], S[None, :]].ravel()
            cand = cand[~visB[cand]]
            new = np.unique(cand)
            visB[new] = True
        else:
            cand = Mt[fr[:, None], Sinv[None, :]].ravel()
            cand = cand[~visA[cand]]
            new = np.unique(cand)
            visA[new] = True
        fr = new
        cur ^= 1
    return (G - int(visA.sum())) + (G - int(visB.sum()))


def _anneal_bicayley(Mt, sinv, G, d, D, rng, deadline):
    """Anneal a d-element connection set S (returned as a numpy array) with zero unreached pairs, or None."""
    if G < d + 1:
        return None
    S = np.array(rng.sample(range(G), d), dtype=np.int64)

    def cost(SS):
        si = sinv[SS]
        return _bfs_unreached(Mt, SS, si, G, D, 0) + _bfs_unreached(Mt, SS, si, G, D, 1)

    c = cost(S)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while c > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = 3.0 * (0.2 / 3.0) ** min(1.0, (now - t0) / span)
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        old = int(S[i])
        S[i] = x
        c2 = cost(S)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            c = c2
        else:
            S[i] = old
    return S if c == 0 else None


def _bicayley_graph(Mt, G, S):
    E = [(g, G + int(Mt[g, s])) for g in range(G) for s in S]
    return 2 * G, E


def _frobenius_search(d, D, lo, hi, rng, deadline, consider, budget):
    cands = _candidate_groups(lo, hi, rng)
    for G, m, k, r in cands:
        now = time.monotonic()
        if now >= deadline:
            break
        Mt = _group_table(m, k, r)
        sinv = np.argmax(Mt == 0, axis=1).astype(np.int64)
        S = _anneal_bicayley(Mt, sinv, G, d, D, rng, min(deadline, now + budget))
        if S is not None:
            consider(*_bicayley_graph(Mt, G, [int(x) for x in S]))


# ----------------------------------------------------------------------------
# Voltage lifts over semidirect products Z_m x| Z_k2 (secondary family).
# ----------------------------------------------------------------------------

def _sample_group(G, rng, k2_choices=None):
    choices = k2_choices or [1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    for _ in range(80):
        k2 = rng.choice(choices)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
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


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms, limit=float("inf")):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return 10 ** 9
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
        if total > limit:
            return total
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _random_darts(d, k, G, rng):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    return darts


def _anneal_lift(d, D, k, G, mul, rng, deadline, iters):
    darts = _random_darts(d, k, G, rng)
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)
        limit = cost - T * math.log(1.0 - rng.random())
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old_s, old_perm = darts[idx][2], perms[idx]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


def _lift_loop(d, D, rng, deadline, cur_best, consider):
    ks = [1, 1, 1, 2, 2, 3, 4]
    k2_pool = [2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = cur_best() // (2 * k)
        lo = max(2, base + 1)
        hi = lo + (max(3, lo // 4) if k == 1 else max(3, lo // 8))
        G = rng.randint(lo, hi)
        g = _sample_group(G, rng, k2_pool) if rng.random() < 0.8 else None
        if g is None:
            g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal_lift(d, D, k, order, mul, rng, deadline, 1500 if k == 1 else 400)
        if res is not None:
            consider(*res)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.88 * time_limit
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.12 * time_limit, rng)
            consider(n2, e2)
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])
        for n_c, e_c in _arc_extensions(d, start + 0.2 * time_limit,
                                        random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

    if D >= 5 and d >= 3:
        # New: Frobenius-group bi-Cayley search over orders just above best_n / 2.
        lo = best_n // 2 + 1
        _frobenius_search(d, D, lo, lo + 200, rng, start + 0.6 * time_limit,
                          consider, 1.0)
        # Remaining time: voltage lifts over semidirect products.
        _lift_loop(d, D, rng, deadline, lambda: best_n, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
