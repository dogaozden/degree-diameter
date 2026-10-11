import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Shared Haar-graph machinery.
#
# A Haar graph over a group G with connection set S has A-vertices 0..G-1 and
# B-vertices G..2G-1, with A_x adjacent to B_{x*s} for s in S. Left multiplication
# is transitive on each side, so diameter <= D iff BFS from A_0 and from B_0 both
# reach every vertex within D steps.
# ----------------------------------------------------------------------------

def _reach_bad(G, pairs, D):
    """Number of (source, vertex) pairs not reached within D steps from A_0 and from B_0.

    pairs: list of (f, b) with f[x] = x*s and b[x] = x*s^{-1} as permutations of the group.
    """
    N = 2 * G
    bad = 0
    for src in (0, G):
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < G:
                    for f, _b in pairs:
                        v = G + f[u]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    h = u - G
                    for _f, b in pairs:
                        v = b[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        bad += N - cnt
    return bad


# ----------------------------------------------------------------------------
# NEW: multiplier-symmetric cyclic Haar graphs.
#
# For Z_m and a unit u of small order t, the map x -> u*x is an automorphism of the
# Haar graph H(Z_m, S) whenever S is a union of orbits of <u> on Z_m. Restricting the
# connection set to such unions shrinks the search space from C(m, d) to a few
# orbit combinations, and each move swaps one orbit for another of the same size,
# so |S| = d is preserved. Validity is still checked by BFS (two sources suffice
# because of translation) and by lib.is_valid.
# ----------------------------------------------------------------------------

def _orbits_mult(m, u):
    """Orbits of x -> u*x on Z_m (u a unit), as a list of lists that partition Z_m."""
    seen = bytearray(m)
    orbs = []
    for x in range(m):
        if seen[x]:
            continue
        orb = []
        y = x
        while not seen[y]:
            seen[y] = 1
            orb.append(y)
            y = y * u % m
        orbs.append(orb)
    return orbs


def _pick_unit(m, d, rng):
    """A random unit of multiplicative order <= d (1 with some probability)."""
    if m < 5 or rng.random() < 0.2:
        return 1
    for _ in range(300):
        x = rng.randrange(2, m)
        if math.gcd(x, m) != 1:
            continue
        y, t = x, 1
        while y != 1 and t <= d:
            y = y * x % m
            t += 1
        if y == 1:
            return x
    return 1


def _cyc_perms(m, s, cache):
    p = cache.get(s)
    if p is None:
        p = ([(x + s) % m for x in range(m)], [(x - s) % m for x in range(m)])
        cache[s] = p
    return p


def _cyc_bad(m, S, D, cache):
    pairs = [_cyc_perms(m, s, cache) for s in S]
    return _reach_bad(m, pairs, D)


def _random_orbit_set(usable, d, rng):
    """Distinct orbit indices whose sizes sum to exactly d, or None."""
    for _ in range(60):
        rem = d
        chosen = []
        used = set()
        ok = True
        while rem > 0:
            cand = [i for i, o in enumerate(usable) if i not in used and len(o) <= rem]
            if not cand:
                ok = False
                break
            i = rng.choice(cand)
            chosen.append(i)
            used.add(i)
            rem -= len(usable[i])
        if ok:
            return chosen
    return None


def _orbit_climb(m, orbs, d, D, rng, deadline, cache):
    """Hill-climb over unions of multiplier orbits; returns S (list of Z_m elements) or None."""
    usable = [o for o in orbs if len(o) <= d]
    chosen = _random_orbit_set(usable, d, rng)
    if chosen is None:
        return None

    def elems(ch):
        S = []
        for i in ch:
            S.extend(usable[i])
        return S

    cur = _cyc_bad(m, elems(chosen), D, cache)
    stale = 0
    while cur > 0:
        if time.monotonic() > deadline or stale > 300:
            return None
        i = rng.randrange(len(chosen))
        sz = len(usable[chosen[i]])
        inset = set(chosen)
        cand = [j for j in range(len(usable)) if j not in inset and len(usable[j]) == sz]
        if not cand:
            stale += 1
            continue
        j = rng.choice(cand)
        T = chosen[:]
        T[i] = j
        ct = _cyc_bad(m, elems(T), D, cache)
        if ct <= cur or rng.random() < 0.02:
            if ct < cur:
                stale = 0
            else:
                stale += 1
            chosen, cur = T, ct
        else:
            stale += 1
    return elems(chosen)


def _orbit_attempt(m, orbs, d, D, rng, deadline):
    cache = {}
    for _ in range(6):
        if time.monotonic() >= deadline:
            break
        S = _orbit_climb(m, orbs, d, D, rng, deadline, cache)
        if S is not None:
            return S
    return None


def _orbit_haar_search(d, D, seed, deadline):
    """Search multiplier-symmetric cyclic Haar graphs with growing m; return the largest valid (n, edges)."""
    rng = random.Random(seed * 1000033 + 7 * d + D)
    moore = lib._moore_bound(d, D)
    lo = max(8, (moore // 2) * 40 // 100)
    best = None
    while time.monotonic() < deadline - 0.5:
        span = max(3, lo // 60)
        m = rng.randint(lo, lo + span)
        S = None
        tries = 0
        while S is None and tries < 4 and time.monotonic() < deadline - 0.5:
            tries += 1
            u = _pick_unit(m, d, rng)
            orbs = _orbits_mult(m, u)
            att = min(deadline, time.monotonic() + 1.2)
            S = _orbit_attempt(m, orbs, d, D, rng, att)
        if S is not None:
            edges = [(x, m + (x + s) % m) for x in range(m) for s in S]
            if lib.is_valid(2 * m, edges, d, D):
                best = (2 * m, edges)
                lo = m + 1
    return best


# ----------------------------------------------------------------------------
# General-group Haar graphs (Z_m x| Z_k), hill-climbed connection sets.
# ----------------------------------------------------------------------------

def _group_of_order(G, rng):
    """Random semidirect product Z_m x|_r Z_k of exact order G; returns (order, mul, inv) or None."""
    divs = [k for k in range(1, G + 1) if G % k == 0 and G // k >= 2]
    if not divs:
        return None
    for _ in range(40):
        k = rng.choice(divs)
        m = G // k
        if k == 1:
            r = 1
        else:
            pool = rng.sample(range(1, m), min(m - 1, 120))
            cands = [r for r in pool if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, inv = lib.semidirect_group(m, k, r)
        except ValueError:
            continue
        return order, mul, inv
    return None


def _climb(G, d, D, mul, inv, rng, deadline):
    """Hill-climb a connection set S of size d in the group so the Haar graph has diameter <= D."""
    cache = {}

    def R(s):
        p = cache.get(s)
        if p is None:
            p = [mul(g, s) for g in range(G)]
            cache[s] = p
        return p

    def cost(S):
        pr = [(R(s), R(inv(s))) for s in S]
        return _reach_bad(G, pr, D)

    S = rng.sample(range(G), d)
    c = cost(S)
    stale = 0
    while c > 0:
        if time.monotonic() > deadline:
            return None
        if stale > 400:
            S = rng.sample(range(G), d)
            c = cost(S)
            stale = 0
            continue
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        T = S[:]
        T[i] = x
        ct = cost(T)
        if ct <= c or rng.random() < 0.03:
            if ct < c:
                stale = 0
            else:
                stale += 1
            S, c = T, ct
        else:
            stale += 1
    return S


def _haar_search(d, D, seed, deadline):
    """Search Haar graphs over groups of growing order; return the largest valid (n, edges) or None."""
    rng = random.Random(seed * 1000003 + 17)
    moore = lib._moore_bound(d, D)
    lo = max(4, (moore // 2) * 44 // 100)
    best = None
    while time.monotonic() < deadline - 0.2:
        span = max(4, lo // 40)
        G = rng.randint(lo, lo + span)
        grp = _group_of_order(G, rng)
        if grp is None:
            lo += 1
            continue
        order, mul, inv = grp
        attempt_deadline = min(deadline, time.monotonic() + 4.0)
        S = _climb(G, d, D, mul, inv, rng, attempt_deadline)
        if S is None:
            continue
        edges = []
        for g in range(G):
            for s in S:
                edges.append((g, G + mul(g, s)))
        n = 2 * G
        if lib.is_valid(n, edges, d, D):
            best = (n, edges)
            lo = G + 1
    return best


# ----------------------------------------------------------------------------
# Projective-plane base (diameter 3 and fallback).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Cover-based vertex extension and edge saturation.
# ----------------------------------------------------------------------------

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


def _extend_cover(n, edges, d, D, deadline, rng):
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


def _grow(n, edges, d, D, deadline, rng):
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
# Double-edge-swap growth.
# ----------------------------------------------------------------------------

def _adj_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _bad_ordered(n, adj, D):
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _swap_grow(n, edges, d, D, deadline, rng, max_fail=3, iters=200):
    if n < 2 or not edges:
        return n, list(edges)
    adj = _adj_sets(n, edges)
    color = _bipartition(n, adj)
    E = [((u, v) if color[u] == 0 else (v, u)) for u, v in edges]
    fails = 0
    while fails < max_fail and time.monotonic() < deadline:
        N = n + 1
        v = n
        adj2 = [set(s) for s in adj]
        adj2.append(set())
        E2 = list(E)
        color2 = list(color)
        c = rng.randrange(2)
        color2.append(c)

        opp = [x for x in range(n) if color[x] == 1 - c]
        rng.shuffle(opp)
        opp.sort(key=lambda x: len(adj2[x]))
        for b in opp[:d]:
            if len(adj2[b]) >= d:
                x = rng.choice(list(adj2[b]))
                adj2[b].discard(x)
                adj2[x].discard(b)
                e_rm = (b, x) if color2[b] == 0 else (x, b)
                E2.remove(e_rm)
            adj2[v].add(b)
            adj2[b].add(v)
            E2.append((b, v) if color2[b] == 0 else (v, b))

        def_a = [x for x in range(N) if color2[x] == 0 and len(adj2[x]) < d]
        def_b = [x for x in range(N) if color2[x] == 1 and len(adj2[x]) < d]
        pairs = [(a, b) for a in def_a for b in def_b if b not in adj2[a]]
        rng.shuffle(pairs)
        for a, b in pairs:
            if len(adj2[a]) < d and len(adj2[b]) < d and b not in adj2[a]:
                adj2[a].add(b)
                adj2[b].add(a)
                E2.append((a, b))

        cost = _bad_ordered(N, adj2, D)
        it = 0
        while cost and it < iters and len(E2) >= 2 and time.monotonic() < deadline:
            it += 1
            i = rng.randrange(len(E2))
            j = rng.randrange(len(E2))
            a, b = E2[i]
            c2, e = E2[j]
            if a == c2 or b == e or e in adj2[a] or b in adj2[c2]:
                continue
            adj2[a].discard(b); adj2[b].discard(a)
            adj2[c2].discard(e); adj2[e].discard(c2)
            adj2[a].add(e); adj2[e].add(a)
            adj2[c2].add(b); adj2[b].add(c2)
            new = _bad_ordered(N, adj2, D)
            if new <= cost or rng.random() < 0.02:
                cost = new
                E2[i] = (a, e)
                E2[j] = (c2, b)
            else:
                adj2[a].discard(e); adj2[e].discard(a)
                adj2[c2].discard(b); adj2[b].discard(c2)
                adj2[a].add(b); adj2[b].add(a)
                adj2[c2].add(e); adj2[e].add(c2)

        if cost == 0 and all(len(s) <= d for s in adj2):
            n, adj, color, E = N, adj2, color2, E2
            fails = 0
        else:
            fails += 1
    return n, [(a, b) for a, b in E]


# ----------------------------------------------------------------------------
# Diameter repair by vertex deletion.
# ----------------------------------------------------------------------------

def _compact(n, edges, keep):
    new = {}
    for v in range(n):
        if keep[v]:
            new[v] = len(new)
    E = [(new[u], new[v]) for u, v in edges if keep[u] and keep[v]]
    return len(new), E


def _repair(n, edges, D, deadline, rng):
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


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products, annealed.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9
_REPAIR_MAX_COST = 60


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


def _anneal(d, D, k, G, mul, rng, deadline, iters, start_darts=None, T0=1.0):
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
        return _edges(k, G, darts, perms), darts, 0
    return None, darts, cost


def _lift_repair(d, D, k, G, mul, darts, deadline, rng):
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    N, E = _edges(k, G, darts, perms)
    rep = _repair(N, E, D, deadline, rng)
    if rep is None:
        return None
    n, e = rep
    e = _saturate_edges(n, e, d, rng)
    return n, e


# ----------------------------------------------------------------------------
# Legacy pipeline: projective base, voltage lifts, repair, growth.
# ----------------------------------------------------------------------------

def _legacy_build(d, D, seed, time_limit):
    start = time.monotonic()
    main_deadline = start + 0.70 * time_limit
    hard = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

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
            n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.20 * time_limit, rng)
            consider(n2, e2)

    ks = [1, 1, 1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    k2_pool = [2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12] if D >= 5 else None
    elite = {}
    while time.monotonic() < main_deadline:
        k = rng.choice(ks)
        base = best_n // (2 * k)
        lo = max(2, base + 1)
        if k == 1 and D >= 5:
            hi = lo + max(3, lo // 4)
        else:
            hi = lo + max(3, lo // 8)
        G = rng.randint(lo, hi)
        g = None
        if k2_pool is not None and rng.random() < 0.8:
            g = _sample_group(G, rng, k2_pool)
        if g is None:
            g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        key = (k, order)

        start_darts, T0 = None, 1.0
        mul_use = mul
        if key in elite and rng.random() < 0.5:
            _, st, mul_use = elite[key]
            start_darts = _perturb(st, order, rng, rng.randint(1, 3))
            T0 = 0.5

        iters = 1500 if k == 1 else 400
        res, darts_out, c = _anneal(d, D, k, order, mul_use, rng, main_deadline,
                                    iters, start_darts, T0)
        if res is not None:
            consider(res[0], res[1])
            continue

        if key not in elite or c < elite[key][0]:
            elite[key] = (c, darts_out, mul_use)

        if c <= _REPAIR_MAX_COST and rng.random() < 0.35 and time.monotonic() < main_deadline:
            rep_deadline = min(main_deadline, time.monotonic() + 4.0)
            out = _lift_repair(d, D, k, order, mul_use, darts_out, rep_deadline, rng)
            if out is not None:
                consider(out[0], out[1])
                grow_deadline = min(main_deadline, time.monotonic() + 3.0)
                n3, e3 = _grow(out[0], out[1], d, D, grow_deadline, rng)
                consider(n3, e3)

    if D >= 3 and best_n >= 2 and time.monotonic() < hard:
        n_s, e_s = _swap_grow(best[0], best[1], d, D, hard, rng)
        consider(n_s, e_s)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    total = 0.80 * time_limit
    best = None

    def consider(c):
        nonlocal best
        if c is None:
            return
        if best is not None and c[0] <= best[0]:
            return
        if lib.is_valid(c[0], c[1], d, D):
            best = c

    # Symmetric cyclic Haar search gets the largest share for D >= 5.
    if D >= 5 and d >= 4:
        try:
            consider(_orbit_haar_search(d, D, seed, t0 + 0.55 * total))
        except Exception:
            pass
        try:
            consider(_haar_search(d, D, seed, t0 + 0.70 * total))
        except Exception:
            pass

    remaining = max(1.0, total - (time.monotonic() - t0))
    try:
        consider(_legacy_build(d, D, seed, remaining))
    except Exception:
        pass

    if best is None or not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
