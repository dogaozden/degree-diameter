import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline families: projective plane, Araujo-Pardo-Lopez (D = 3), and the
# generalized quadrangle W(q) (D = 4, Moore-optimal for its degree).
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
# NEW: signed double cover (Z_2 voltage lift) with focused annealing.
#
# Given a simple base graph on n vertices, a 2-lift has 2n vertices:
# base edge (u, v) with sign s becomes (u, v + s*n) and (u + n, v + (1-s)*n).
# Degrees are preserved, and the lift stays bipartite if the base is bipartite
# (every cover of a bipartite graph is bipartite; colour lift vertex x by the
# base colour of x mod n). Diameter is the only thing to fix: we anneal over
# signs, with each move flipping an edge incident to a currently far-off lift
# vertex, and score by the bitmask count of pairs at distance > D.
# ----------------------------------------------------------------------------

def _lift2(n, edges, signs):
    """Signed double cover of a base graph on n vertices. Returns (2n, edges)."""
    E = []
    for (u, v), s in zip(edges, signs):
        E.append((u, v + s * n))
        E.append((u + n, v + (1 - s) * n))
    return 2 * n, E


def _ball_info(N, adj, D):
    """Return (total ordered pairs at distance > D, per-vertex deficit) via bitmask balls."""
    ball = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    deficit = [N - b.bit_count() for b in ball]
    return sum(deficit), deficit


def _signed_lift_search(n, edges, D, deadline, rng):
    """Anneal signs so the 2-lift of a simple base graph has diameter <= D. Returns (N, E) or None."""
    m = len(edges)
    if m == 0:
        return None
    inc = [[] for _ in range(n)]
    for i, (u, v) in enumerate(edges):
        inc[u].append(i)
        inc[v].append(i)
    signs = [rng.randrange(2) for _ in range(m)]

    def evaluate(sg):
        N, E = _lift2(n, edges, sg)
        adj = [[] for _ in range(N)]
        for x, y in E:
            adj[x].append(y)
            adj[y].append(x)
        return _ball_info(N, adj, D)

    cost, deficit = evaluate(signs)
    T = 5.0
    while cost > 0:
        if time.monotonic() > deadline:
            return None
        T = max(0.5, T * 0.999)
        bad = [x for x in range(2 * n) if deficit[x] > 0]
        i = rng.randrange(m)
        if bad and rng.random() < 0.7:
            x = rng.choice(bad)
            cand = inc[x % n]
            if cand:
                i = rng.choice(cand)
        signs[i] ^= 1
        c2, d2 = evaluate(signs)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost, deficit = c2, d2
        else:
            signs[i] ^= 1
    return _lift2(n, edges, signs)


# ----------------------------------------------------------------------------
# Group voltage lifts over Z_m x| Z_k (parent's secondary family, simplified).
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 2, 3, 4, 5, 6, 8])
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


def _group_cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return 10 ** 9
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            a = i * G + g
            b = (k + j) * G + pm[g]
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
    return total


def _group_anneal(d, D, k, G, mul, rng, deadline, iters):
    """Anneal voltages over a group; return (n, edges) if valid, else None."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    cost = _group_cost(k, G, D, darts, perms)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)
        idx = rng.randrange(len(darts))
        old_s, old_p = darts[idx][2], perms[idx]
        new_s = rng.randrange(G)
        darts[idx][2] = new_s
        perms[idx] = [mul(g, new_s) for g in range(G)]
        c2 = _group_cost(k, G, D, darts, perms)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            darts[idx][2] = old_s
            perms[idx] = old_p
    if cost != 0:
        return None
    E = set()
    for (i, j, _), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _group_phase(d, D, get_n, deadline, rng, consider):
    """Repeatedly try group lifts sized just above the current best."""
    ks = [1, 1, 2, 3] if D >= 5 else [1, 2]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        lo = max(2, get_n() // (2 * k) + 1)
        G = rng.randint(lo, lo + max(3, lo // 8))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _group_anneal(d, D, k, order, mul, rng, deadline, 800)
        if res is not None:
            consider(res[0], res[1])


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.8 * time_limit
    lift_end = start + 0.55 * time_limit
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

    def get_n():
        return best_n

    bound = lib.moore_bound(d, D)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Calibration cases that already meet the Moore-type bound return immediately.
    if best_n >= bound:
        return best

    # NEW: iterated signed double covers of the current best graph.
    if D >= 4 and d >= 4:
        cur_n, cur_e = best
        while time.monotonic() < lift_end:
            now = time.monotonic()
            budget_end = min(lift_end, now + 0.45 * (lift_end - now))
            r = _signed_lift_search(cur_n, cur_e, D, budget_end, rng)
            if r is None:
                continue
            cur_n, cur_e = r
            consider(cur_n, cur_e)
            if best_n < cur_n:
                # Should not happen: consider rejected a lift that search certified.
                cur_n, cur_e = best

    # Group voltage lifts for the remaining time.
    if time.monotonic() < end:
        _group_phase(d, D, get_n, end, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
