import itertools
import math
import random
import time

import lib


_BIG = 10 ** 9


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
# Group voltage lifts with simulated annealing.
#
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,g*s for every g in the group.
# Left multiplication by any element is an automorphism, so the diameter is
# certified by BFS from one A representative and one B representative per base
# vertex.
#
# New in this version:
#   * _groups_of_order enumerates every semidirect product Z_m x| Z_k2 of a given
#     order (not a random sample), so the search can target a fixed order exactly.
#   * _anneal runs simulated annealing with two move types. A voltage change is
#     the usual move. A target swap exchanges the B-endpoints of two darts in the
#     same layer, which keeps every layer a permutation, so degrees stay exact.
#   * Restarts are chunked by time, so each group order gets several tries.
# ----------------------------------------------------------------------------

def _right_perm(mul, G, s):
    """Permutation g -> g*s of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    N = 2 * k * G
    seen_keys = set()
    adj = [[] for _ in range(N)]
    for (i, j, s), pm in zip(darts, perms):
        key = (i, j, s)
        if key in seen_keys:
            return _BIG  # duplicate darts would create duplicate edges
        seen_keys.add(key)
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
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
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _groups_of_order(G, rng):
    """All (or a random few per factorization) multiplication functions of Z_m x| Z_k2 with m*k2 = G."""
    out = []
    for k2 in range(1, 13):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            out.append(lib.semidirect_group(m, 1, 1)[1])
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if not rs:
            continue
        for r in rng.sample(rs, min(len(rs), 3)):
            out.append(lib.semidirect_group(m, k2, r)[1])
    return out


def _anneal(d, D, k, G, mul, rng, deadline, max_iters):
    """Simulated annealing over voltages and target swaps. Returns (n, edges) with diameter <= D, or None."""
    layers = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, layers[l][i], rng.randrange(G)] for l in range(d) for i in range(k)]
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)
    best_cost = cost
    best = ([x[:] for x in darts], perms[:])
    nd = len(darts)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    frac = 0.0
    T = 4.0

    for it in range(max_iters):
        if cost == 0:
            break
        if it % 32 == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            frac = min(1.0, (now - t0) / span)
            T = 0.3 + 4.0 * (1.0 - frac)

        idx = rng.randrange(nd)
        if k > 1 and rng.random() < 0.3:
            # Target swap inside one layer: keeps each layer a permutation.
            idx2 = (idx // k) * k + rng.randrange(k)
            if idx2 == idx:
                continue
            darts[idx][1], darts[idx2][1] = darts[idx2][1], darts[idx][1]
            c2 = _cost(k, G, D, darts, perms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][1], darts[idx2][1] = darts[idx2][1], darts[idx][1]
        else:
            # Voltage change.
            old_s = darts[idx][2]
            old_pm = perms[idx]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_pm

        if cost < best_cost:
            best_cost = cost
            best = ([x[:] for x in darts], perms[:])

    if best_cost == 0:
        return _edges(k, G, best[0], best[1])
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
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

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Calibration cases that already meet the Moore bound return immediately.
    if best_n >= lib._moore_bound(d, D):
        return best

    chunk = max(2.0, budget / 6.0)
    while time.monotonic() < deadline:
        k = rng.choice([1, 1, 1, 1, 2, 2, 3])
        Gmin = best_n // (2 * k) + 1  # any larger G gives n > best_n
        G = max(2, Gmin + rng.choice([0, 0, 0, 1, 2]))
        groups = _groups_of_order(G, rng)
        if not groups:
            continue
        mul = rng.choice(groups)
        sub = min(deadline, time.monotonic() + chunk)
        res = _anneal(d, D, k, G, mul, rng, sub, 10 ** 9)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
