import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions for diameter 3.
# ----------------------------------------------------------------------------

def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _al_base(d):
    """Araujo-Pardo & Lopez record family for d = q + 2, q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New helper: pair insertion with a free apex edge.
#
# Remove k = d-1 edges forming a matching (a_j, b_j). Add two new vertices
# x (A-side) and y (B-side) with x ~ b_j, y ~ a_j for all j, and the apex edge
# x ~ y. Every old vertex keeps its degree, and x, y have degree k + 1 = d.
# Unlike a plain matching swap with k = d, the apex edge x-y gives the new pair
# a direct link, which changes which distance-3 pairs the matching has to cover.
# The matching is chosen by plateau hill climbing on lib.bad_pairs.
# ----------------------------------------------------------------------------

def _ecol(n, edges):
    """Edges oriented as (A, B) according to a 2-colouring of the graph."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
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
    return [(u, v) if color[u] == 0 else (v, u) for u, v in edges]


def _pair_insert(n, Ecol, d, D, deadline, rng):
    """Try to insert one (x, y) pair with an apex edge. Returns (n + 2, edges) or None."""
    k = d - 1
    m_e = len(Ecol)
    if k < 1 or m_e < k:
        return None

    def build(J):
        rem = set(J)
        out = [Ecol[j] for j in range(m_e) if j not in rem]
        x, y = n, n + 1
        for j in J:
            a, b = Ecol[j]
            out.append((x, b))
            out.append((a, y))
        out.append((x, y))
        return n + 2, out

    def cost(J):
        nn, out = build(J)
        return lib.bad_pairs(nn, out, D)

    while time.monotonic() < deadline:
        order = list(range(m_e))
        rng.shuffle(order)
        J, usedA, usedB = [], set(), set()
        for j in order:
            a, b = Ecol[j]
            if a in usedA or b in usedB:
                continue
            J.append(j)
            usedA.add(a)
            usedB.add(b)
            if len(J) == k:
                break
        if len(J) < k:
            return None

        cur = cost(J)
        stall = 0
        while cur > 0 and stall < 300 and time.monotonic() < deadline:
            p = rng.randrange(k)
            old = J[p]
            a_old, b_old = Ecol[old]
            Jset = set(J)
            cand = None
            for _ in range(40):
                c = rng.randrange(m_e)
                if c in Jset:
                    continue
                a, b = Ecol[c]
                if a != a_old and a in usedA:
                    continue
                if b != b_old and b in usedB:
                    continue
                cand = c
                break
            if cand is None:
                stall += 1
                continue
            a, b = Ecol[cand]
            J2 = J[:]
            J2[p] = cand
            c2 = cost(J2)
            if c2 <= cur:
                stall = 0 if c2 < cur else stall + 1
                usedA.discard(a_old)
                usedB.discard(b_old)
                usedA.add(a)
                usedB.add(b)
                J, cur = J2, c2
            else:
                stall += 1

        if cur == 0:
            return build(J)
    return None


def _pair_growth(n, edges, d, D, deadline, rng):
    """Repeatedly insert pairs while the diameter bound holds; returns the largest valid graph."""
    cur = (n, edges)
    while time.monotonic() < deadline:
        Ecol = _ecol(cur[0], cur[1])
        r = _pair_insert(cur[0], Ecol, d, D, deadline, rng)
        if r is None or not lib.is_valid(r[0], r[1], d, D):
            break
        cur = r
    return cur


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products (used for D >= 4).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


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


def _edges(k, G, darts, perms):
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
        return _edges(k, G, darts, perms)
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
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and is optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    bound = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    if D == 3:
        bases = []
        al = _al_base(d)
        if al is not None:
            bases.append(al)
        pg = _pg_best(d)
        if pg is not None:
            bases.append(pg)
        for n_b, e_b in bases:
            consider(n_b, e_b)

        if best_n < bound:
            # Grow from the best base using the pair-insertion helper.
            n2, e2 = _pair_growth(best_n, best[1], d, D, deadline,
                                  random.Random(seed * 31 + d))
            consider(n2, e2)

    else:
        # D >= 4: annealed bi-Cayley voltage lifts.
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < deadline and best_n < bound:
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

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
