import itertools
import math
import random
import time

import lib

MAX_GROUPS = 12        # groups tried per bi-Cayley attempt
ITERS = 600            # annealing steps per (group) try
T_HOT = 1.5            # initial annealing temperature (unreached-pair units)
T_COLD = 0.15          # final annealing temperature
GROUP_MOVE_PROB = 0.5  # chance a move proposes a product of two set elements
MULTI_PROB = 0.25      # chance a loop iteration tries a multi-base lift
MULTI_ITERS = 600      # annealing steps for multi-base lifts
BUDGET_START = 1.5     # seconds per bi-Cayley attempt at the start
BUDGET_CAP = 6.0       # cap on per-attempt seconds as passes fail
MAX_TABLE_N = 1200     # largest group order whose full multiplication table we build
TABLE_CACHE_SIZE = 16
BIG = 10 ** 9

_GROUPS_CACHE = {}
_TABLE_CACHE = {}


# ----------------------------------------------------------------------------
# Baselines: K_{d,d}, projective planes, generalized quadrangles, and
# diameter-preserving growth by cover vertices and saturating edges.
# ----------------------------------------------------------------------------

def _fallback(d, D):
    """Always-valid fallback: K_{d,d} (diameter 2), or K_2 for D = 1."""
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    return lib.haar_graph(d, range(d))


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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 5 for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices; None if it fails."""
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
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1."""
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
    """Greedily join deficient opposite-side vertices in random order."""
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
    """Extend by cover vertices first, then saturate edges with the leftover spare degree."""
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
# Bi-Cayley lifts over Z_m x|_r Z_k (one base vertex per side).
# Vertices A_x, B_y (x, y in G); edge A_x -- B_{x s} for s in S, |S| = d.
# Left multiplication is an automorphism, so eccentricities from A_0 and B_0
# decide the diameter. Identity is WLOG in S.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    hit = _GROUPS_CACHE.get(N)
    if hit is not None:
        return hit
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    _GROUPS_CACHE[N] = out
    return out


def _tables(m, k, r):
    """Cached (T, invs) for Z_m x|_r Z_k, with T[x][g] = x*g and invs[g] = g^-1."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (T, invs)
    if len(_TABLE_CACHE) >= TABLE_CACHE_SIZE:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D, limit):
    """Count (source, vertex) pairs not within distance D, for sources A_0 and B_0.

    Early exit: once the running total exceeds `limit`, the partial total is
    returned. Any value above `limit` means the set is rejected.
    """
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
        if total > limit:
            return total
    return total


def _anneal(N, T, invs, d, D, rng, iters, deadline):
    """Annealing over S = {0, s_1, ..., s_{d-1}} to zero unreached pairs.

    Acceptance uses a pre-drawn threshold: accept iff v - cur <= -temp*ln(u),
    which is the Metropolis rule. This lets the evaluation exit early.
    """
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D, BIG)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i = rng.randrange(1, d)
        if rng.random() < GROUP_MOVE_PROB:
            c = T[S[rng.randrange(d)]][S[rng.randrange(d)]]
        else:
            c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        lim = cur - temp * math.log(max(rng.random(), 1e-12))
        v = _unreached(N, T, invs, S2, D, lim)
        if v <= lim:
            S, cur = S2, v
    return S if cur == 0 else None


def _attempt(N, d, D, rng, deadline):
    """Try groups of order N until one yields a valid connection set, or time runs out."""
    groups = list(_groups(N))
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        T, invs = _tables(m, k, r)
        S = _anneal(N, T, invs, d, D, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


# ----------------------------------------------------------------------------
# Multi-base voltage lifts with k base vertices per side over a group G.
# Layer L is a permutation p_L of the k base vertices, each dart carrying a
# group voltage s; A_{i,g} ~ B_{p(i), g*s}.
# ----------------------------------------------------------------------------

def _right_perm(mul, G, s):
    """Permutation g -> g*s of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return BIG
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


def _edges_multi(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal_multi(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer base permutations."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T0 = max(1.0, 0.05 * cost) if cost < BIG else 1.0
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
        return _edges_multi(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def _build(d, D, seed, time_limit, holder):
    """Fill holder[0] with the best valid (n, edges) found so far."""
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 4.0))
    rng = random.Random(seed)

    if d < 1 or D < 1 or D <= 2:
        return  # K_{d,d} (or K_2, or the trivial graph) is already optimal here

    def consider(n, e):
        if n > holder[0][0] and lib.is_valid(n, e, d, D):
            holder[0] = (n, e)

    moore = lib._moore_bound(d, D)

    # Projective plane meets the Moore bound for D = 3.
    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(*pg)
            if holder[0][0] < moore:
                consider(*_grow(pg[0], pg[1], d, D, start + 0.1 * (deadline - start), rng))

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(*gq)
            if holder[0][0] < moore:
                consider(*_grow(gq[0], gq[1], d, D,
                                start + 0.2 * (deadline - start), rng))

    if d < 2:
        return

    Nmax = min(moore // 2, MAX_TABLE_N)
    if Nmax < d + 1:
        return
    base_top = min(Nmax, max(Nmax // 2 + 6, d + 1))
    floor = max(d + 1, int(0.95 * base_top))
    budget = BUDGET_START
    fails = 0

    while time.monotonic() < deadline:
        n_best = holder[0][0]
        bestN = n_best // 2

        if rng.random() < MULTI_PROB:
            k = rng.choice((2, 3))
            lo_G = n_best // (2 * k) + 1
            if lo_G >= 2 and lo_G <= MAX_TABLE_N and 2 * k * lo_G <= moore:
                G = lo_G + rng.randrange(max(2, lo_G // 10))
                if 2 * k * G <= moore and G <= MAX_TABLE_N:
                    m, k2, r = rng.choice(_groups(G))
                    order, mul, _ = lib.semidirect_group(m, k2, r)
                    res = _anneal_multi(d, D, k, order, mul, rng, deadline, MULTI_ITERS)
                    if res is not None:
                        consider(res[0], res[1])
            continue

        lo = max(floor, bestN + 1)
        if lo > Nmax:
            break
        top = min(Nmax, max(base_top, bestN + 6))
        cands = list(range(lo, top + 1))
        if not cands:
            break
        weights = [max(1, len(_groups(N))) for N in cands]
        N = rng.choices(cands, weights=weights, k=1)[0]

        att_deadline = min(deadline, time.monotonic() + budget)
        res = _attempt(N, d, D, rng, att_deadline)
        if res is None:
            fails += 1
            if fails >= len(cands):
                fails = 0
                if budget < BUDGET_CAP:
                    budget = min(BUDGET_CAP, budget * 1.5)
                elif floor > d + 1:
                    floor -= 1
        else:
            T, S = res
            consider(2 * N, [(x, N + T[x][g]) for x in range(N) for g in S])
            fails = 0


def build(d, D, seed, time_limit):
    holder = [_fallback(d, D)]
    try:
        _build(d, D, seed, time_limit, holder)
    except Exception:
        pass
    n, e = holder[0]
    if lib.is_valid(n, e, d, D):
        return n, e
    return _fallback(d, D)
