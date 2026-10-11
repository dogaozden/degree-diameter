import math
import random
import time

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Baseline: projective plane incidence graph (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# NEW: orbit-closed extension of a (d-1)-regular bi-Cayley lift.
#
# Base: k A-vertices and k B-vertices per group element, joined by d-1
# "layers". Each layer is a perfect matching between the A-orbits and the
# B-orbits, realised as darts (i, j, s): A_{i,g} ~ B_{j, g*s}.  Every base
# vertex then has degree d-1, i.e. one spare slot.
#
# Extension: two new orbits X (side B) and Y (side A), each of size G.
#   X_h ~ A_{i, h*x_i}   for each i  (uses the spare slot of every A-orbit once)
#   Y_h ~ B_{j, h*y_j}   for each j  (uses the spare slot of every B-orbit once)
#   X_h ~ Y_{h*u}        for d-k distinct u (regularises X and Y to degree d)
# The result is a d-regular bipartite graph on 2G(k+1) vertices. Left
# multiplication by the group is an automorphism, so the diameter check only
# needs one BFS per orbit type (2k+2 sources). Annealing searches the
# voltages of all darts jointly, with the full diameter cost as objective.
# ----------------------------------------------------------------------------

def _full_cost(N, adj, reps, D, limit=float("inf")):
    """Number of (source, vertex) pairs not reached within distance D over the sources in reps."""
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


def _ext_edges(k, G, T, layers, xs, ys, us):
    """Edge list of the extended graph. T[g][s] = g*s in the group."""
    X0 = 2 * k * G
    Y0 = X0 + G
    E = []
    for layer in layers:
        for i, j, s in layer:
            for g in range(G):
                E.append((i * G + g, (k + j) * G + T[g][s]))
    for i in range(k):
        s = xs[i]
        for h in range(G):
            E.append((i * G + T[h][s], X0 + h))
    for j in range(k):
        s = ys[j]
        for h in range(G):
            E.append(((k + j) * G + T[h][s], Y0 + h))
    for u in us:
        for h in range(G):
            E.append((X0 + h, Y0 + T[h][u]))
    return 2 * G * (k + 1), E


def _ext_cost(k, G, T, layers, xs, ys, us, D, limit):
    """Diameter-violation count of the extended graph; _BIG if base darts repeat."""
    keys = {(i, j, s) for layer in layers for i, j, s in layer}
    if len(keys) < len(layers) * k:
        return _BIG
    N, E = _ext_edges(k, G, T, layers, xs, ys, us)
    adj = [[] for _ in range(N)]
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    X0 = 2 * k * G
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)] + [X0, X0 + G]
    return _full_cost(N, adj, reps, D, limit)


def _anneal_ext(d, D, k, G, T, rng, deadline, iters):
    """Anneal the joint voltage structure of the extended graph; return (n, edges) or None."""
    nxy = d - k
    if nxy < 0 or nxy > G:
        return None
    layers = []
    for _ in range(d - 1):
        p = rng.sample(range(k), k)
        layers.append([[i, p[i], rng.randrange(G)] for i in range(k)])
    xs = [rng.randrange(G) for _ in range(k)]
    ys = [rng.randrange(G) for _ in range(k)]
    us = rng.sample(range(G), nxy)

    cost = _ext_cost(k, G, T, layers, xs, ys, us, D, float("inf"))
    temp = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.05, temp * 0.997)
        limit = cost - temp * math.log(1.0 - rng.random())
        r = rng.random()

        if r < 0.45:
            # Change one base dart voltage.
            l = rng.randrange(d - 1)
            i = rng.randrange(k)
            old = layers[l][i][2]
            new = rng.randrange(G)
            if new == old:
                continue
            layers[l][i][2] = new
            c2 = _ext_cost(k, G, T, layers, xs, ys, us, D, limit)
            if c2 <= limit:
                cost = c2
            else:
                layers[l][i][2] = old

        elif r < 0.6 and k >= 2:
            # Swap B-destinations inside one base layer (keeps it a matching).
            l = rng.randrange(d - 1)
            a, b = rng.sample(range(k), 2)
            la = layers[l]
            la[a][1], la[b][1] = la[b][1], la[a][1]
            c2 = _ext_cost(k, G, T, layers, xs, ys, us, D, limit)
            if c2 <= limit:
                cost = c2
            else:
                la[a][1], la[b][1] = la[b][1], la[a][1]

        elif r < 0.8:
            # Change one voltage of the X (A-side) or Y (B-side) orbit.
            arr = xs if rng.random() < 0.5 else ys
            i = rng.randrange(k)
            old = arr[i]
            new = rng.randrange(G)
            if new == old:
                continue
            arr[i] = new
            c2 = _ext_cost(k, G, T, layers, xs, ys, us, D, limit)
            if c2 <= limit:
                cost = c2
            else:
                arr[i] = old

        elif nxy >= 1:
            # Change one X-Y voltage, keeping the set of u distinct.
            idx = rng.randrange(nxy)
            new = rng.randrange(G)
            if new in us:
                continue
            old = us[idx]
            us[idx] = new
            c2 = _ext_cost(k, G, T, layers, xs, ys, us, D, limit)
            if c2 <= limit:
                cost = c2
            else:
                us[idx] = old

    if cost == 0:
        return _ext_edges(k, G, T, layers, xs, ys, us)
    return None


def _try_ext(d, D, best_n, rng, deadline):
    """One attempt of the extended-lift family aimed above the current best order."""
    k = rng.choice([kk for kk in (1, 2, 3, 4) if kk <= d])
    need = best_n // (2 * (k + 1)) + 1
    G = need + rng.randrange(0, 4)
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    T = [[mul(x, s) for s in range(order)] for x in range(order)]
    return _anneal_ext(d, D, k, order, T, rng, deadline, iters=700)


# ----------------------------------------------------------------------------
# Parent family: annealed d-regular bi-Cayley lifts over Z_m x| Z_k2.
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


def _cost(k, G, D, darts, perms, limit=float("inf")):
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
    return _full_cost(N, adj, reps, D, limit)


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

    T = 1.0
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
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Haar graph hill-climb (small D, secondary family).
# ----------------------------------------------------------------------------

def _search_haar(d, D, m, rng, deadline, iters):
    """Hill-climb a connection set S (|S| = d, containing 0) in Z_m so the Haar graph has diameter <= D."""
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T_ = S[:]
        T_[i] = rng.choice(cand)
        ct = cost(T_)
        if ct <= c:
            S, c = T_, ct
    return S if c == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
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
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3:
                return best

    ks = [1, 2, 2, 3, 4]
    haar_m, haar_miss = d + 1, 0
    while time.monotonic() < deadline:
        # New family: spare-slot orbit extension of (d-1)-regular lifts.
        if D >= 4 and d >= 2 and rng.random() < 0.6:
            res = _try_ext(d, D, best_n, rng, deadline)
            if res is not None:
                consider(res[0], res[1])
            continue

        if D <= 4 and haar_miss < 4 and rng.random() < 0.1:
            S = _search_haar(d, D, haar_m, rng, deadline, 120)
            if S is not None:
                n, e = lib.haar_graph(haar_m, S)
                consider(n, e)
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1
            continue

        k = rng.choice(ks)
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, iters=400)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
