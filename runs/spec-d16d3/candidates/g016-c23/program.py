import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Projective plane base: PG(2, q) incidence with neighbour lists.
# Points are 0..m-1 and lines are 0..m-1 (vertex m + j in the incidence graph).
# The incidence relation is symmetric, so nbr[i] serves as both the lines
# through point i and the points on line i.
# ----------------------------------------------------------------------------

def _pg(q):
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    nbr = [[] for _ in range(m)]
    for u, v in edges:
        nbr[u].append(v - m)
    return m, edges, nbr


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3).
#
# Pick S, a set of point indices. Add an A-vertex per P in S, joined to the
# lines through P, and a B-vertex per L in S, joined to the points on L.
# Every point and line gains degree load[j] = #{v in S : j in nbr[v]}, so we
# need load[j] <= s = d - q - 1 for all j. Order is 2m + 2|S|, and diameter
# stays 3 for any S (checked by reasoning and by lib.is_valid).
# ----------------------------------------------------------------------------

def _arc_search(m, nbr, s, rng, deadline):
    """Local search maximising |S| subject to load[j] <= s for every j.

    Moves: free additions when possible, otherwise a swap that adds a random
    non-member after removing at most two conflicting members. Recently
    removed members are tabu. The search perturbs when it stalls.
    """
    if s < 1:
        return []
    inS = [False] * m
    members = set()
    load = [0] * m
    tabu = [0] * m
    best = []
    it = 0
    stall = 0

    def add(v):
        inS[v] = True
        members.add(v)
        for j in nbr[v]:
            load[j] += 1

    def rem(v):
        inS[v] = False
        members.discard(v)
        for j in nbr[v]:
            load[j] -= 1

    while time.monotonic() < deadline:
        it += 1
        free = [v for v in range(m)
                if not inS[v] and tabu[v] <= it and all(load[j] < s for j in nbr[v])]
        if free:
            add(rng.choice(free))
        else:
            pool = [v for v in range(m) if not inS[v] and tabu[v] <= it]
            if not pool:
                tabu = [0] * m
                continue
            v = rng.choice(pool)
            rm = []
            for j in nbr[v]:
                while load[j] >= s:
                    opts = [x for x in nbr[j] if inS[x]]
                    x = rng.choice(opts)
                    rem(x)
                    rm.append(x)
                if len(rm) > 2:
                    break
            if len(rm) > 2:
                for x in rm:
                    add(x)
                continue
            add(v)
            for x in rm:
                tabu[x] = it + 7

        if len(members) > len(best):
            best = sorted(members)
            stall = 0
        else:
            stall += 1
        if stall > 3000 and members:
            for x in rng.sample(sorted(members), max(1, len(members) // 3)):
                rem(x)
                tabu[x] = it + 10
            stall = 0
    return best


def _arc_graph(m, edges, nbr, S):
    """Projective incidence plus an A-vertex and a B-vertex for each element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in nbr[P]:
            E.append((x, m + L))
    for t, L in enumerate(S):
        b = 2 * m + k + t
        for Q in nbr[L]:
            E.append((Q, b))
    return n, E


# ----------------------------------------------------------------------------
# Cover-based vertex extension (diameter-preserving growth).
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


def _extend_cover(n, edges, d, D, deadline, rng, attempts=20):
    """Add vertices whose neighbourhoods cover all vertices within distance D-1."""
    if D < 2:
        return n, list(edges)
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
            for att in range(attempts):
                chosen = _greedy_cover(cands, ball, full, d, rng, att > 0)
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


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2 (used for D >= 4).
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 6])
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


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
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
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    U = 0.8 * time_limit          # usable budget, leaving a safety margin
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

    if D >= 3:
        # Two largest prime powers q with q + 1 <= d; spare degree s = d - q - 1.
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:2]
        if D == 3:
            fracs = [0.7, 0.9]
        else:
            fracs = [0.4, 0.6]
        for idx, q in enumerate(qs):
            s = d - q - 1
            m, edges, nbr = _pg(q)
            consider(2 * m, edges)  # plain incidence graph as baseline
            if s < 1:
                continue
            dl = start + fracs[idx] * U
            S = _arc_search(m, nbr, s, random.Random(seed * 7919 + q), dl)
            if S:
                n_c, e_c = _arc_graph(m, edges, nbr, S)
                consider(n_c, e_c)

        if D == 3:
            # Use leftover spare degree by cover-based vertex growth.
            n2, e2 = _extend_cover(best[0], best[1], d, D, start + U, rng)
            consider(n2, e2)

    if D >= 4:
        # Annealed bi-Cayley voltage lifts for larger diameters.
        ks = [1, 2, 3]
        while time.monotonic() < start + U:
            k = rng.choice(ks)
            G0 = max(2, best_n // (2 * k))
            G = max(2, G0 + 1 + rng.randrange(0, max(3, G0 // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, start + U, 400)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
