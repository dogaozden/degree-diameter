import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Time fractions (of time_limit). Lift search ends at FRAC_LIFT; the remaining
# time goes to repair-growth on the best candidates, finishing by FRAC_REPAIR.
# ----------------------------------------------------------------------------
FRAC_LIFT = 0.50
FRAC_REPAIR = 0.90
GQ_Q_MAX = 9
REPAIR_FAILS = 8          # consecutive failed attempts before giving up on a candidate
ATTEMPT_ITERS = 1200      # swap-annealing steps per repair attempt
_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Algebraic bases: projective plane (D = 3) and generalized quadrangle (D >= 4).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
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
    """W(q) for the largest prime power q <= min(d - 1, GQ_Q_MAX)."""
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Generic graph utilities (list-based, fast for a few hundred vertices).
# ----------------------------------------------------------------------------

def _adj_lists(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
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


def _bad_count(n, edges, D):
    """Number of unordered vertex pairs at distance more than D."""
    ball = _balls_radius(n, _adj_lists(n, edges), D)
    return sum(n - b.bit_count() for b in ball) // 2


def _greedy_pick(cands, ball, full, d, rng, randomize):
    """Pick up to d candidates maximising newly covered vertices; returns (chosen, fully_covered)."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.3:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen, covered == full


def _saturate(n, edges, color, d, rng):
    """Greedily join deficient opposite-colour vertices in random order (only shortens distances)."""
    edges = list(edges)
    deg = [0] * n
    existing = set()
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        existing.add((min(u, v), max(u, v)))
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


def _cover_grow(n, edges, color, d, D, deadline, rng):
    """Add vertices whose neighbourhoods cover everything within D-1; always keeps validity."""
    edges = list(edges)
    color = list(color)
    while time.monotonic() < deadline:
        adj = _adj_lists(n, edges)
        deg = [len(a) for a in adj]
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        grew = False
        for c in rng.sample([0, 1], 2):
            cands = [s for s in range(n) if color[s] == 1 - c and deg[s] < d]
            ok, chosen = False, []
            for attempt in range(20):
                chosen, ok = _greedy_pick(cands, ball, full, d, rng, attempt > 0)
                if ok:
                    break
            if ok and chosen:
                v = n
                n += 1
                color.append(c)
                for s in chosen:
                    edges.append((s, v))
                grew = True
                break
        if not grew:
            break
    return n, edges, color


# ----------------------------------------------------------------------------
# NEW: repair-growth. Attach one new vertex with a partial cover (even if it
# does not reach everything), saturate spare degree, then anneal
# degree-preserving double-edge swaps (keeps bipartiteness and degrees) with
# cost = number of pairs at distance > D. Success means a valid graph one
# vertex larger. Swaps are the only moves, so the degree sequence is fixed.
# ----------------------------------------------------------------------------

def _repair_add(n, edges, color, d, D, deadline, rng, iters):
    """Try to grow by one vertex; return (n+1, edges, color) or None."""
    adj = _adj_lists(n, edges)
    deg = [len(a) for a in adj]
    ball = _balls_radius(n, adj, D - 1)
    full = (1 << n) - 1
    c = rng.randrange(2)
    cands = [s for s in range(n) if color[s] == 1 - c and deg[s] < d]
    if not cands:
        return None
    chosen, _ = _greedy_pick(cands, ball, full, d, rng, True)
    if not chosen:
        return None

    N = n + 1
    v = n
    col = list(color) + [c]
    E = list(edges) + [(s, v) for s in chosen]
    E = _saturate(N, E, col, d, rng)
    E = list(E)
    cur = _bad_count(N, E, D)
    if cur == 0:
        return N, E, col

    existing = set((min(u, w), max(u, w)) for u, w in E)
    T0, T1 = 1.0, 0.15
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        orig_i, orig_j = E[i], E[j]
        a, b = orig_i
        x, y = orig_j
        if col[a] == 1:
            a, b = b, a
        if col[x] == 1:
            x, y = y, x
        # Now a and x are colour 0; b and y are colour 1.
        if a == x or b == y:
            continue
        k1 = (min(a, y), max(a, y))
        k2 = (min(x, b), max(x, b))
        if k1 in existing or k2 in existing:
            continue
        old1 = (min(a, b), max(a, b))
        old2 = (min(x, y), max(x, y))
        E[i] = (a, y)
        E[j] = (x, b)
        new_cost = _bad_count(N, E, D)
        delta = new_cost - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new_cost
            existing.discard(old1)
            existing.discard(old2)
            existing.add(k1)
            existing.add(k2)
        else:
            E[i] = orig_i
            E[j] = orig_j

    if cur == 0:
        return N, E, col
    return None


def _repair_grow(n, edges, color, d, D, deadline, rng):
    """Repeatedly apply _repair_add until it fails REPAIR_FAILS times in a row."""
    cur = (n, list(edges), list(color))
    fails = 0
    while time.monotonic() < deadline and fails < REPAIR_FAILS:
        res = _repair_add(cur[0], cur[1], cur[2], d, D, deadline, rng, ATTEMPT_ITERS)
        if res is None:
            fails += 1
        else:
            cur = res
            fails = 0
    return cur


# ----------------------------------------------------------------------------
# Group voltage lifts over Z_m x| Z_k2, annealed.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
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
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
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
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    if cost < _BIG:
        T0 = max(1.0, 0.05 * cost)
    else:
        T0 = 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    lift_deadline = start + FRAC_LIFT * time_limit
    final_deadline = start + FRAC_REPAIR * time_limit
    rng = random.Random(seed)

    # Trivial cases.
    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    # K_{d,d} has diameter 2 and is the always-valid fallback.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    best = fallback
    pool = [fallback]
    moore = lib._moore_bound(d, D)

    def consider(c):
        nonlocal best
        if c is None:
            return
        n, e = c
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            pool.append(best)
            pool.sort(key=lambda item: -item[0])
            del pool[4:]

    # Algebraic bases.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg)
            if pg[0] >= moore:
                return best
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)
            if gq[0] >= moore:
                return best

    # Main search: annealed group voltage lifts.
    try:
        if D >= 5:
            ks = [1, 1, 2, 2, 3, 4]
            anneal_iters = 1500
        else:
            ks = [1, 2, 2, 3, 4]
            anneal_iters = 400
        while time.monotonic() < lift_deadline and best[0] < moore:
            k = rng.choice(ks)
            base = best[0] // (2 * k)
            if D >= 5:
                G = max(2, base + 1 + rng.randrange(0, 3))
            else:
                G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, lift_deadline, anneal_iters)
            if res is not None:
                consider(res)
    except Exception:
        pass

    # Final stage: cover-grow, then repair-grow the top candidates.
    try:
        top = sorted(pool, key=lambda c: -c[0])[:2]
        for idx, c in enumerate(top):
            now = time.monotonic()
            if now >= final_deadline:
                break
            slice_end = now + (final_deadline - now) / (len(top) - idx)
            color = _bipartition(c[0], _adj_lists(c[0], c[1]))
            gn, ge, gc = _cover_grow(c[0], c[1], color, d, D,
                                     now + 0.2 * (slice_end - now), rng)
            consider((gn, ge))
            rn, re_, _rc = _repair_grow(gn, ge, gc, d, D, slice_end, rng)
            consider((rn, re_))
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
