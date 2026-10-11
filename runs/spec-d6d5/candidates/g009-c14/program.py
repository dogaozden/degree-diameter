import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New family in this version: affine bi-Cayley lifts.
#
# The group is a subgroup of AGL(1, q) = {t -> a*t + b : a, b in GF(q)}. It
# consists of the maps with a in the order-h subgroup of GF(q)*, so |G| = q*h.
# Such groups are non-abelian for h > 1 and are not semidirect products
# Z_m x| Z_k, so they add structure the other families do not provide.
# Orders q*h near the record divisors (e.g. 19*18 = 342, 27*13 = 351,
# 25*8 = 200) give lifts of the sizes needed to beat 684.
#
# Lifts: vertices A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h. Dart (i, j, s)
# joins A_{i,g} to B_{j, g*s}. Left multiplication by G is an automorphism, so
# the diameter is checked from one representative per base vertex.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9
_REPAIR_MAX_COST = 60
_GF = {}
_AFF = {}


# ----------------------------------------------------------------------------
# Baseline constructions (used for D = 3 and as seeds).
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


# ----------------------------------------------------------------------------
# Affine groups.
# ----------------------------------------------------------------------------

def _field(q):
    if q not in _GF:
        _GF[q] = lib.GF(q)
    return _GF[q]


def _affine_group(q, h):
    """Group of maps t -> a*t + b with a in the order-h subgroup of GF(q)*.

    Element (b, a) is coded as index(a)*q + b, so the identity is coded 0.
    Returns (order, mul) with order = q*h.
    """
    key = (q, h)
    if key in _AFF:
        return _AFF[key]
    F = _field(q)
    g = F.primitive_element()
    step = (q - 1) // h
    H = [F.pow(g, j * step) for j in range(h)]  # H[0] == 1
    hidx = {a: i for i, a in enumerate(H)}
    addl = F.add_table.tolist()
    mull = F.mul_table.tolist()
    mh = [[hidx[mull[H[i]][H[j]]] for j in range(h)] for i in range(h)]

    def mul(x, y):
        # (b1, a1) * (b2, a2) = (a1*b2 + b1, a1*a2), i.e. composition of affine maps.
        hi, b1 = divmod(x, q)
        hj, b2 = divmod(y, q)
        return mh[hi][hj] * q + addl[b1][mull[H[hi]][b2]]

    res = (q * h, mul)
    _AFF[key] = res
    return res


def _affine_pool(lo, hi):
    """All (q, h, order) with q a prime power, h | q-1, and lo <= q*h <= hi."""
    out = []
    for q in range(3, 65):
        if not lib.is_prime_power(q):
            continue
        for h in range(1, q):
            if (q - 1) % h:
                continue
            order = q * h
            if lo <= order <= hi:
                out.append((q, h, order))
    return out


def _sample_semidirect(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G: returns (order, mul, desc) or None."""
    choices = [1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]
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
        return order, mul, ('s', m, k2, r)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lift machinery: cost, annealing, and repair.
# ----------------------------------------------------------------------------

def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms, limit=float("inf")):
    """Number of (representative, vertex) pairs not reached within D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
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


def _perturb(darts, G, rng, flips):
    out = [list(x) for x in darts]
    for _ in range(flips):
        idx = rng.randrange(len(out))
        out[idx][2] = rng.randrange(G)
    return out


def _focused_move(k, G, D, darts, perms, mul, rng, cost, limit, samples):
    idx = rng.randrange(len(darts))
    old_s = darts[idx][2]
    old_perm = perms[idx]
    best_c, best_s = None, None
    for _ in range(samples):
        s = rng.randrange(G)
        if s == old_s:
            continue
        darts[idx][2] = s
        perms[idx] = _right_perm(mul, G, s)
        c = _cost(k, G, D, darts, perms, limit if best_c is None else best_c)
        if best_c is None or c < best_c:
            best_c, best_s = c, s
    darts[idx][2] = old_s
    perms[idx] = old_perm
    if best_c is None or best_c > limit:
        return cost
    darts[idx][2] = best_s
    perms[idx] = _right_perm(mul, G, best_s)
    return best_c


def _anneal(d, D, k, G, mul, rng, deadline, iters, start_darts=None, T0=1.0):
    """Simulated annealing over voltages and per-layer B-assignments.

    Returns (edges_or_None, darts, cost).
    """
    if start_darts is None:
        darts = _random_darts(d, k, G, rng)
    else:
        darts = [list(x) for x in start_darts]
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = T0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)
        limit = cost - T * math.log(1.0 - rng.random())

        r = rng.random()
        if r < 0.25:
            cost = _focused_move(k, G, D, darts, perms, mul, rng, cost, limit, 4)
        elif r < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
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
        return _edges(k, G, darts, perms), darts, 0
    return None, darts, cost


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


def _compact(n, edges, keep):
    new = {}
    for v in range(n):
        if keep[v]:
            new[v] = len(new)
    E = [(new[u], new[v]) for u, v in edges if keep[u] and keep[v]]
    return len(new), E


def _repair(n, edges, D, deadline, rng):
    """Delete far-off vertices in batches until the diameter is at most D. Returns (n, edges) or None."""
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        if cur_n == 0:
            return None
        adj = [[] for _ in range(cur_n)]
        for u, v in cur_e:
            adj[u].append(v)
            adj[v].append(u)
        ball = _balls_radius(cur_n, adj, D)
        bad = [cur_n - b.bit_count() for b in ball]
        if not any(bad):
            return cur_n, cur_e
        bad_v = [v for v in range(cur_n) if bad[v] > 0]
        rng.shuffle(bad_v)
        bad_v.sort(key=lambda v: -bad[v])
        batch = max(1, len(bad_v) // 12)
        dead = set(bad_v[:batch])
        keep = [v not in dead for v in range(cur_n)]
        cur_n, cur_e = _compact(cur_n, cur_e, keep)
    return None


def _saturate_edges(n, edges, d, rng):
    """Greedily add opposite-side edges between deficient vertices (only adds edges)."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
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


def _lift_repair(d, D, k, G, mul, darts, deadline, rng):
    """Build the full lift from darts, repair it by vertex deletion, then saturate."""
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    N, E = _edges(k, G, darts, perms)
    rep = _repair(N, E, D, deadline, rng)
    if rep is None:
        return None
    n, e = rep
    e = _saturate_edges(n, e, d, rng)
    return n, e


# ----------------------------------------------------------------------------
# Search driver.
# ----------------------------------------------------------------------------

def _offer(state, n, e, d, D):
    """Replace the incumbent if (n, e) is larger and passes the full validity check."""
    if n > state[0][0] and lib.is_valid(n, e, d, D):
        state[0] = (n, e)


def _lift_search(d, D, deadline, rng, state):
    """Anneal bi-Cayley lifts over affine and semidirect groups, with elite restarts and repair."""
    elite = {}
    while time.monotonic() < deadline:
        best_n = state[0][0]
        k = rng.choice([1, 1, 1, 2, 2, 3, 4])
        base = best_n // (2 * k)
        lo = max(2, base + 1)
        hi = int(base * 1.25) + 2

        cand = None
        if rng.random() < 0.6:
            pool = _affine_pool(lo, hi)
            if pool:
                q, h, _G = rng.choice(pool)
                order, mul = _affine_group(q, h)
                cand = (order, mul, ('a', q, h))
        if cand is None:
            G = rng.randint(lo, lo + max(3, base // 8))
            cand = _sample_semidirect(G, rng)
            if cand is None:
                continue
        order, mul, desc = cand
        key = (k, order, desc)

        start_darts, T0 = None, 1.0
        if key in elite and rng.random() < 0.5:
            _, st = elite[key]
            start_darts = _perturb(st, order, rng, rng.randint(1, 3))
            T0 = 0.5

        iters = 1000 if k == 1 else 400
        res, darts_out, c = _anneal(d, D, k, order, mul, rng, deadline, iters,
                                    start_darts, T0)
        if res is not None:
            _offer(state, res[0], res[1], d, D)
            continue

        if key not in elite or c < elite[key][0]:
            elite[key] = (c, darts_out)

        if c <= _REPAIR_MAX_COST and rng.random() < 0.35 and time.monotonic() < deadline:
            rep_deadline = min(deadline, time.monotonic() + 4.0)
            out = _lift_repair(d, D, k, order, mul, darts_out, rep_deadline, rng)
            if out is not None:
                _offer(state, out[0], out[1], d, D)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    state = [lib.haar_graph(d, range(d))]
    try:
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                _offer(state, pg[0], pg[1], d, D)
            ar = _araujo(d)
            if ar is not None:
                _offer(state, ar[0], ar[1], d, D)
        if D >= 4:
            _lift_search(d, D, deadline, rng, state)
    except Exception:
        pass

    best = state[0]
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
