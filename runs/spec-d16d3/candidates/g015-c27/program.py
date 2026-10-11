import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bitmask helpers and projective-plane data.
# ----------------------------------------------------------------------------

def _bits(mask):
    """Indices of the set bits of a non-negative integer."""
    out = []
    while mask:
        low = mask & -mask
        out.append(low.bit_length() - 1)
        mask ^= low
    return out


def _largest_prime_power_at_most(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _pg_masks(q):
    """PG(2,q) incidence: m points (0..m-1) and m lines (indices shared with points).

    pl[P] is a bitmask of the lines through point P; lp[L] a bitmask of the points on line L.
    """
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [0] * m
    lp = [0] * m
    for u, v in edges:
        L = v - m
        pl[u] |= 1 << L
        lp[L] |= 1 << u
    return m, edges, pl, lp


def _conic_indices(q):
    """A conic (plus the nucleus for even q): an arc with no three collinear, as point/line indices."""
    F = lib.GF(q)
    index = {p: i for i, p in enumerate(lib.projective_points(q))}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


# ----------------------------------------------------------------------------
# NEW IDEA: pencil-cover vertex families.
#
# In a two-sided diameter-3 graph built on PG(2,q), a new point-side vertex A_v
# may be joined to any set C of lines that covers every point. Its distance to
# every point is then 2, and to every other vertex at most 3. Two such vertices
# need a common neighbour (their line sets must intersect). A pencil (all lines
# through a point) is one such cover; a non-pencil cover of size <= d is another.
# Old lines can absorb at most s = d-q-1 new neighbours. Dually, B-vertices are
# joined to point sets covering all lines. The search below looks for further
# covers by simulated annealing, instead of only the conic arc of the old design.
# ----------------------------------------------------------------------------

def _random_not_in(pool, taken, rng):
    for _ in range(30):
        x = pool[rng.randrange(len(pool))]
        if x not in taken:
            return x
    return None


def _search_cover(cover, m, dmax, allowed, existing, init, rng, iters):
    """Annealing for one new vertex.

    Find a candidate set S (|S| <= dmax, drawn from `allowed`) whose masks in
    `cover` jointly cover all m universe elements, and which meets every
    bitmask in `existing`. Returns S or None.
    """
    pool = list(allowed)
    if not pool:
        return None

    def evaluate(T):
        u = 0
        cm = 0
        for j in T:
            u |= cover[j]
            cm |= 1 << j
        pen = 0
        for e in existing:
            if not (e & cm):
                pen += 1
        return (m - u.bit_count()) + 2 * pen

    if init:
        S = list(init)[:dmax]
    else:
        S = rng.sample(pool, min(dmax, len(pool)))
    cur = evaluate(S)
    for it in range(iters):
        if cur == 0:
            return S
        T = 1.5 * (0.02 ** (it / iters))
        cand = list(S)
        taken = set(cand)
        r = rng.random()
        if r < 0.6 and cand:
            new = _random_not_in(pool, taken, rng)
            if new is None:
                continue
            cand[rng.randrange(len(cand))] = new
        elif r < 0.8 and len(cand) < dmax:
            new = _random_not_in(pool, taken, rng)
            if new is None:
                continue
            cand.append(new)
        elif len(cand) > 1:
            cand.pop(rng.randrange(len(cand)))
        else:
            continue
        nv = evaluate(cand)
        if nv <= cur or rng.random() < math.exp(-(nv - cur) / T):
            S, cur = cand, nv
    return S if cur == 0 else None


def _grow_family(m, cover, pencils, s, dmax, family, usage, rng, deadline, max_fail):
    """Append new covers to `family` (mutating `usage`) until the search fails repeatedly or time runs out."""
    existing = [sum(1 << j for j in C) for C in family]
    fails = 0
    while time.monotonic() < deadline and fails < max_fail:
        allowed = [j for j in range(m) if usage[j] < s]
        init = None
        if allowed and rng.random() < 0.5:
            allowed_set = set(allowed)
            init = [j for j in _bits(pencils[rng.randrange(m)]) if j in allowed_set]
        S = _search_cover(cover, m, dmax, allowed, existing, init, rng, 3000)
        if S is None:
            fails += 1
            continue
        fails = 0
        family.append(S)
        existing.append(sum(1 << j for j in S))
        for j in S:
            usage[j] += 1
    return family


def _assemble(m, edges, fam_a, fam_b):
    """Points 0..m-1, lines m..2m-1, A-vertices (adjacent to lines), B-vertices (adjacent to points)."""
    E = list(edges)
    base = 2 * m
    for t, C in enumerate(fam_a):
        x = base + t
        E.extend((x, m + j) for j in C)
    base2 = base + len(fam_a)
    for t, D in enumerate(fam_b):
        y = base2 + t
        E.extend((j, y) for j in D)
    return base2 + len(fam_b), E


def _build_d3(d, q, seed, deadline):
    """Diameter-3 construction on PG(2,q) with spare degree s = d-q-1."""
    rng = random.Random(seed)
    s = d - q - 1
    m, edges, pl, lp = _pg_masks(q)
    if s <= 0:
        return _assemble(m, edges, [], [])

    # Baseline: conic arc on both sides (pencils through conic points, dual pencils on conic lines).
    conic = _conic_indices(q)
    fam_a = [_bits(pl[P]) for P in conic]
    fam_b = [_bits(lp[L]) for L in conic]
    usage_a = [0] * m
    usage_b = [0] * m
    for C in fam_a:
        for j in C:
            usage_a[j] += 1
    for C in fam_b:
        for j in C:
            usage_b[j] += 1
    if max(usage_a) > s or max(usage_b) > s:
        fam_a, fam_b = [], []
        usage_a = [0] * m
        usage_b = [0] * m

    now = time.monotonic()
    mid = now + 0.5 * (deadline - now)
    # A covers: candidates are lines, universe is points (cover[j] = points on line j).
    _grow_family(m, lp, pl, s, d, fam_a, usage_a, rng, mid, 80)
    # B covers: candidates are points, universe is lines (cover[j] = lines through point j).
    _grow_family(m, pl, lp, s, d, fam_b, usage_b, rng, deadline, 80)
    return _assemble(m, edges, fam_a, fam_b)


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products (fallback for D >= 4).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
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
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms, limit=float("inf")):
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


def _edges_of(k, G, darts, perms):
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
    cost = _cost(k, G, D, darts, perms)

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 1.0 * (0.05 ** (it / iters))
        u = 1.0 - rng.random()
        limit = cost - T * math.log(u)

        if rng.random() < 0.7 or k == 1:
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
        return _edges_of(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # even cycle: diameter D, Moore-optimal for max degree 2
        return n, [(i, (i + 1) % n) for i in range(n)]

    # K_{d,d} has diameter 2 and is Moore-optimal for D = 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2:
        return best_n, best_e

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D == 3:
        q = _largest_prime_power_at_most(d - 1)
        if q is not None:
            n, e = _build_d3(d, q, seed, deadline)
            consider(n, e)
        return best_n, best_e

    # D >= 4: annealed group voltage lifts.
    ks = [1, 2, 2, 3, 4]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, iters=1200)
        if res is not None:
            consider(res[0], res[1])

    return best_n, best_e
