import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Tunables.
# ----------------------------------------------------------------------------

MAX_GROUPS = 10        # groups tried per bi-Cayley order N
CLIMB_ITERS = 400      # annealing steps per (group, connection set) try
RESTARTS = 2           # random restarts of the connection set per group
ANNEAL_ITERS = 800     # annealing steps for multi-base lifts
SWEEP_WINDOW = 12      # bi-Cayley orders considered above the lower bound
WEIGHTED_PICK_PROB = 0.3
SA_SHARE = 0.65        # share of the budget given to direct bipartite annealing (D >= 5)
SA_ATTEMPT_SHARE = 0.4 # share of the remaining SA time given to one size attempt
_BIG = 10 ** 9
_TABLE_CACHE = {}
_TABLE_CACHE_CAP = 12


# ----------------------------------------------------------------------------
# D = 3 and D = 4 baselines.
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 5 for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# NEW: direct annealing over bipartite graphs with a fixed side size.
#
# State: a simple bipartite graph with sides A = {0..n-1}, B = {n..2n-1}, each
# vertex of degree <= d. Moves are 2-switches (a1-b1, a2-b2 -> a1-b2, a2-b1),
# which keep degrees and bipartiteness. Cost = number of ordered vertex pairs
# at distance > D, computed by boolean ball expansion.
# ----------------------------------------------------------------------------

def _bad_pairs_bool(N, d, edges, D):
    """Number of ordered pairs (u, v) with dist(u, v) > D, via bool ball expansion."""
    adj = [[] for _ in range(N)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    nb = np.empty((N, d), dtype=np.int64)
    for v in range(N):
        row = adj[v][:d]
        row = row + [v] * (d - len(row))  # pad with self (harmless for reach)
        nb[v] = row
    R = np.eye(N, dtype=bool)
    for _ in range(D):
        new = R.copy()
        for k in range(d):
            new |= R[nb[:, k]]
        if np.array_equal(new, R):
            break
        R = new
    return N * N - int(np.count_nonzero(R))


def _sa_bipartite(d, D, n, rng, deadline):
    """Anneal a bipartite graph with sides of size n; return (2n, edges) on success, else None."""
    N = 2 * n
    eset = set()
    edges = []
    for _ in range(d):
        perm = list(range(n))
        rng.shuffle(perm)
        for a in range(n):
            e = (a, n + perm[a])
            if e not in eset:
                eset.add(e)
                edges.append(e)
    cost = _bad_pairs_bool(N, d, edges, D)
    if cost == 0:
        return N, edges

    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    T0 = max(1.0, 0.03 * cost)
    T_end = 0.3
    m = len(edges)
    temp = T0
    steps = 0
    while cost > 0:
        if (steps & 7) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            frac = min(1.0, (now - t0) / span)
            temp = T0 * (T_end / T0) ** frac
        steps += 1

        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        old1, old2 = edges[i], edges[j]
        a1, b1 = old1
        a2, b2 = old2
        ne1 = (a1, b2)
        ne2 = (a2, b1)
        if ne1 in eset or ne2 in eset or ne1 == ne2:
            continue

        edges[i] = ne1
        edges[j] = ne2
        eset.discard(old1)
        eset.discard(old2)
        eset.add(ne1)
        eset.add(ne2)

        c2 = _bad_pairs_bool(N, d, edges, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cost = c2
        else:
            edges[i] = old1
            edges[j] = old2
            eset.discard(ne1)
            eset.discard(ne2)
            eset.add(old1)
            eset.add(old2)

    if cost == 0:
        return N, list(edges)
    return None


def _sa_search(d, D, moore, best_n, rng, sa_deadline):
    """Grow the side size while annealing succeeds; yield valid (n, edges) candidates."""
    out = []
    n_side = max(2, best_n // 2 + 1)
    while time.monotonic() < sa_deadline and 2 * n_side <= moore:
        now = time.monotonic()
        attempt_dl = min(sa_deadline, now + max(3.0, SA_ATTEMPT_SHARE * (sa_deadline - now)))
        res = _sa_bipartite(d, D, n_side, rng, attempt_dl)
        if res is None:
            break
        out.append(res)
        n_side += max(1, n_side // 25)
    return out


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x|_r Z_k with an annealed connection set.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _pick_order(lo, hi, rng):
    """Pick N in [lo, hi), weighted by the number of semidirect groups of that order."""
    cands = list(range(lo, hi))
    weights = [max(1, len(_groups(N))) for N in cands]
    return rng.choices(cands, weights=weights, k=1)[0]


def _tables(m, k, r):
    """Cached (order, mul, T, invs) for Z_m x|_r Z_k, where T[x][g] = x*g and invs[g] = g^-1."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, mul, T, invs)
    if len(_TABLE_CACHE) >= _TABLE_CACHE_CAP:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Count vertex pairs (source, target) not within distance D, from A_0 and B_0."""
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
    return total


def _climb(N, T, invs, d, D, rng, iters, deadline):
    """Anneal a connection set S (identity fixed in S) to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        temp = 0.3 + 1.5 * (1.0 - it / iters)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _bicayley_search(N, d, D, rng, deadline):
    """Try groups of order N with restarts; return (T, S) on success, else None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        _, _, T, invs = _tables(m, k, r)
        for _ in range(RESTARTS):
            if time.monotonic() > deadline:
                break
            S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
            if S is not None:
                return T, S
    return None


# ----------------------------------------------------------------------------
# Multi-base voltage lifts over semidirect products, annealed.
# ----------------------------------------------------------------------------

def _right_perm(mul, G, s):
    """Permutation g -> g*s of the group."""
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
    """Edge list of the lift, A-vertices first, B-vertices after."""
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

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    temp = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(T_end, temp * decay)

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
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
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
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and meets the Moore bound 2d for D = 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Structured baselines.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if best[0] < moore:
            for n_c, e_c in _arc_extensions_safe(d, start + 0.3 * budget, seed):
                consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # NEW: direct bipartite annealing for D >= 5 (cases where lifts stall).
    if D >= 5 and d >= 3 and best[0] < moore:
        sa_deadline = start + SA_SHARE * budget
        try:
            for n_c, e_c in _sa_search(d, D, moore, best[0], rng, sa_deadline):
                consider(n_c, e_c)
        except Exception:
            pass

    # Main search: aim strictly above the current best order.
    bicayley_prob = 0.7 if D >= 4 else 0.5
    sweep = None
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]

        if d >= 2 and rng.random() < bicayley_prob:
            lo = n_best // 2 + 1
            if lo > moore // 2:
                break
            hi = min(lo + SWEEP_WINDOW, moore // 2 + 1)
            if rng.random() < WEIGHTED_PICK_PROB:
                N = _pick_order(lo, hi, rng)
            else:
                if sweep is None or sweep < lo or sweep >= hi:
                    sweep = lo
                N = sweep
                sweep += 1
            found = _bicayley_search(N, d, D, rng, deadline)
            if found is not None:
                T, S = found
                consider(2 * N, [(x, N + T[x][g]) for x in range(N) for g in S])
        else:
            k = rng.choice((2, 3))
            lo = n_best // (2 * k) + 1
            if 2 * k * lo > moore:
                continue
            G = lo + rng.randrange(max(2, lo // 10))
            groups = _groups(G)
            if not groups:
                continue
            m, k2, r = rng.choice(groups)
            order, mul, _ = lib.semidirect_group(m, k2, r)
            res = _anneal(d, D, k, order, mul, rng, deadline, ANNEAL_ITERS)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best


# ----------------------------------------------------------------------------
# Safe wrapper for the D = 3 arc extension path (kept small and guarded).
# ----------------------------------------------------------------------------

def _arc_extensions_safe(d, deadline, seed):
    """Return candidate (n, edges) graphs from PG(2, q) with extra arc vertices; empty on error."""
    try:
        out = []
        for q in range(2, min(d - 1, 23) + 1):
            if not lib.is_prime_power(q) or time.monotonic() > deadline:
                continue
            s = d - q - 1
            if s < 1:
                continue
            n2, edges = lib.projective_plane_incidence(q)
            m = n2 // 2
            point_lines = [[] for _ in range(m)]
            line_points = [[] for _ in range(m)]
            for u, v in edges:
                point_lines[u].append(v - m)
                line_points[v - m].append(u)
            rng = random.Random(seed * 7919 + q)
            S = []
            order = list(range(m))
            for _ in range(20):
                if time.monotonic() > deadline:
                    break
                rng.shuffle(order)
                cl = [0] * m
                cp = [0] * m
                cur = []
                for P in order:
                    if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                        cur.append(P)
                        for L in point_lines[P]:
                            cl[L] += 1
                        for Q in line_points[P]:
                            cp[Q] += 1
                if len(cur) > len(S):
                    S = cur
            if not S:
                continue
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
            out.append((n, E))
        return out
    except Exception:
        return []
