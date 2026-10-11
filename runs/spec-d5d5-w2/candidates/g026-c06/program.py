import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# D = 3 baseline (projective plane) and D = 4 baseline (generalized quadrangle).
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 7 for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# NEW for D = 5: cyclic multi-base lifts over Z_N, evaluated with bitmasks.
#
# Vertices: A_{i,g} = i*N + g and B_{j,g} = (k+j)*N + g.
# Dart (i, j, s) gives edges A_{i,g} -- B_{j,(g+s) mod N} for every g.
# Each layer is a permutation of the k base vertices, so every vertex gets degree d.
# Translation by Z_N is an automorphism, so eccentricities of the 2k
# representatives A_{i,0} and B_{j,0} decide diameter validity for the whole graph.
# Each BFS level is a rotation of an N-bit mask per base vertex.
# ----------------------------------------------------------------------------

CYC_ITERS = 2500
CYC_PROB = 0.8
CYC_KS = (1, 2, 3, 4, 5, 6, 8)


def _cyc_cost(k, N, darts, D, full):
    """Number of (source, vertex) pairs unreached within D over the 2k representatives."""
    size = 2 * k * N
    total = 0
    sources = [(0, i) for i in range(k)] + [(1, j) for j in range(k)]
    for side, part in sources:
        vA = [0] * k
        vB = [0] * k
        fA = [0] * k
        fB = [0] * k
        if side == 0:
            vA[part] = 1
            fA[part] = 1
        else:
            vB[part] = 1
            fB[part] = 1
        for _ in range(D):
            nA = [0] * k
            nB = [0] * k
            for i, j, s in darts:
                x = fA[i]
                if x:
                    nB[j] |= ((x << s) | (x >> (N - s))) & full
                y = fB[j]
                if y:
                    t = (N - s) % N
                    nA[i] |= ((y << t) | (y >> (N - t))) & full
            grew = False
            for j in range(k):
                nb = nB[j] & ~vB[j]
                vB[j] |= nb
                fB[j] = nb
                if nb:
                    grew = True
            for i in range(k):
                na = nA[i] & ~vA[i]
                vA[i] |= na
                fA[i] = na
                if na:
                    grew = True
            if not grew:
                break
        cnt = sum(v.bit_count() for v in vA) + sum(v.bit_count() for v in vB)
        total += size - cnt
    return total


def _cyc_edges(k, N, darts):
    E = set()
    for i, j, s in darts:
        for g in range(N):
            E.add((i * N + g, (k + j) * N + (g + s) % N))
    return 2 * k * N, sorted(E)


def _cyc_anneal(d, D, k, N, rng, deadline, iters):
    """Anneal voltages and layer permutations; return (n, edges) if valid, else None."""
    if d < 2 or N < d:
        return None
    full = (1 << N) - 1
    darts = []
    for L in range(d):
        p = list(range(k)) if L == 0 else rng.sample(range(k), k)
        for i in range(k):
            s = 0 if L == 0 else rng.randrange(N)
            darts.append([i, p[i], s])

    def score(ds):
        dup = len(ds) - len({(a, b, c) for a, b, c in ds})
        return _cyc_cost(k, N, ds, D, full) + 20 * dup

    cost = score(darts)
    T0, T1 = 2.0, 0.05
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(k, d * k)
            new = rng.randrange(N)
            old = darts[idx][2]
            if new == old:
                continue
            darts[idx][2] = new
            c2 = score(darts)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(1, d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = score(darts)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0 and len({(a, b, c) for a, b, c in darts}) == len(darts):
        return _cyc_edges(k, N, darts)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x|_r Z_k (kept from the previous search).
# ----------------------------------------------------------------------------

MAX_GROUPS = 12
CLIMB_ITERS = 1000
ANNEAL_ITERS = 800
_BIG = 10 ** 9
_TABLE_CACHE = {}


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


def _tables(m, k, r):
    """Cached (order, mul, T, invs) for Z_m x|_r Z_k."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, mul, T, invs)
    if len(_TABLE_CACHE) >= 48:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Count vertex pairs not within distance D, from A_0 and B_0 of a bi-Cayley graph."""
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
    """Simulated annealing over a connection set S of size d containing the identity."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    best_S, best_v = S, cur
    T0 = 4.0 + 0.05 * cur
    for step in range(iters):
        if best_v == 0 or time.monotonic() > deadline:
            break
        temp = T0 * (1.0 - step / iters) + 0.2
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S, cur = S2, v
            if cur < best_v:
                best_S, best_v = S, cur
    return best_S if best_v == 0 else None


# ----------------------------------------------------------------------------
# General multi-base voltage lifts over semidirect products, annealed.
# ----------------------------------------------------------------------------

def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _gcost(k, G, D, darts, perms):
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


def _gedges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _gcost(k, G, D, darts, perms)

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
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
            c2 = _gcost(k, G, D, darts, perms)
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
            c2 = _gcost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _gedges(k, G, darts, perms)
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

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every d >= 1.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    ks = (2, 3)
    bicayley_prob = 0.85 if D >= 4 else 0.6
    tried = {}
    try:
        while best[0] < moore and time.monotonic() < deadline:
            n_best = best[0]

            # New family for D = 5: cyclic multi-base lifts with bitmask evaluation.
            if D == 5 and d >= 2 and rng.random() < CYC_PROB:
                k = rng.choice(CYC_KS)
                N = n_best // (2 * k) + 1 + rng.randrange(3)
                if N < d or 2 * k * N > moore:
                    continue
                res = _cyc_anneal(d, D, k, N, rng, deadline, CYC_ITERS)
                if res is not None:
                    consider(res[0], res[1])
                continue

            if rng.random() < bicayley_prob:
                lo = n_best // 2 + 1
                if lo > moore // 2:
                    break
                window = max(2, lo // 10)
                hi = min(lo + window, moore // 2 + 1)
                N = min(range(lo, hi),
                        key=lambda x: (tried.get(x, 0), rng.random()))
                tried[N] = tried.get(N, 0) + 1
                if N < d:
                    continue
                groups = _groups(N)
                rng.shuffle(groups)
                found = None
                for m, k2, r in groups[:MAX_GROUPS]:
                    if time.monotonic() > deadline:
                        break
                    _, _, T, invs = _tables(m, k2, r)
                    S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
                    if S is not None:
                        found = (T, S)
                        break
                if found is not None:
                    T, S = found
                    edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                    consider(2 * N, edges)
            else:
                k = rng.choice(ks)
                lo = n_best // (2 * k) + 1
                if 2 * k * lo > moore:
                    continue
                G = lo + rng.randrange(max(2, lo // 10))
                if G < 2:
                    continue
                m, k2, r = rng.choice(_groups(G))
                order, mul, _ = lib.semidirect_group(m, k2, r)
                res = _anneal(d, D, k, order, mul, rng, deadline, ANNEAL_ITERS)
                if res is not None:
                    consider(res[0], res[1])
    except Exception:
        pass  # keep the best valid graph found so far

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
