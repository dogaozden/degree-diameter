import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Time fractions (of time_limit).
# ----------------------------------------------------------------------------
FRAC_CAY = 0.50      # bipartite Cayley-graph search ends here
FRAC_TOTAL = 0.80    # voltage-lift annealing ends here
CAY_ITERS = 150      # hill-climb steps per sampled group
CAY_G_MAX = 400      # cap on group order (keeps tables small)
_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Projective plane base (D = 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bipartite Cayley graphs: A_g ~ B_{g*s} for s in S, group G of order G.
# Left multiplication is an automorphism that is transitive on each side,
# so distances only need to be checked from A_e and B_e.
# S always contains the identity (WLOG, by relabelling B).
# ----------------------------------------------------------------------------

def _sample_table(G, rng):
    """Return (order, table) for a random semidirect product Z_m x| Z_k of order G, or None."""
    divs = [k for k in range(1, G + 1) if G % k == 0 and G // k >= 2]
    for _ in range(40):
        k2 = rng.choice(divs)
        m = G // k2
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 40))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        tab = [[mul(x, y) for y in range(order)] for x in range(order)]
        if any(tab[0][y] != y for y in range(order)):
            continue
        return order, tab
    return None


def _inverses(tab, G):
    inv = [0] * G
    for x in range(G):
        row = tab[x]
        for y in range(G):
            if row[y] == 0:
                inv[x] = y
                break
    return inv


def _cay_unreached(G, tab, inv, S, D, src):
    """Number of vertices of the bipartite Cayley graph not within distance D of src."""
    N = 2 * G
    invS = [inv[s] for s in S]
    seen = bytearray(N)
    seen[src] = 1
    frontier = [src]
    count = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            if u < G:
                row = tab[u]
                for s in S:
                    v = G + row[s]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            else:
                row = tab[u - G]
                for t in invS:
                    v = row[t]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
        count += len(nxt)
        frontier = nxt
        if not frontier:
            break
    return N - count


def _cay_cost(G, tab, inv, S, D):
    return _cay_unreached(G, tab, inv, S, D, 0) + _cay_unreached(G, tab, inv, S, D, G)


def _cay_search(d, D, G, tab, inv, rng, iters, deadline):
    """Hill-climb a connection set S (|S| = d, containing 0) so the Cayley graph has diameter <= D."""
    nonid = list(range(1, G))
    if len(nonid) < d - 1:
        return None
    S = [0] + rng.sample(nonid, d - 1)
    c = _cay_cost(G, tab, inv, S, D)
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        cand = rng.choice(nonid)
        if cand in S:
            continue
        T = S[:]
        T[i] = cand
        ct = _cay_cost(G, tab, inv, T, D)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def _cayley_edges(G, tab, S):
    return 2 * G, [(g, G + tab[g][s]) for g in range(G) for s in S]


# ----------------------------------------------------------------------------
# Group voltage lifts over Z_m x| Z_k2, annealed (fallback family).
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
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    cay_deadline = start + FRAC_CAY * time_limit
    deadline = start + FRAC_TOTAL * time_limit
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
    moore = lib._moore_bound(d, D)

    def consider(c):
        nonlocal best
        if c is None:
            return
        n, e = c
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    try:
        # Algebraic base for D = 3 (meets the Moore bound when d - 1 is a prime power).
        if D == 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg)
                if pg[0] >= moore:
                    return best

        # Main new family: bipartite Cayley graphs over random groups.
        G_hi = min(moore // 2, CAY_G_MAX)
        while time.monotonic() < cay_deadline:
            lo = best[0] // 2 + 1
            if lo > G_hi:
                break
            G = rng.randint(lo, G_hi)
            g = _sample_table(G, rng)
            if g is None:
                continue
            order, tab = g
            inv = _inverses(tab, order)
            S = _cay_search(d, D, order, tab, inv, rng, CAY_ITERS, cay_deadline)
            if S is not None:
                consider(_cayley_edges(order, tab, S))

        # Fallback family: annealed group voltage lifts for the remaining time.
        ks = [1, 1, 2, 2, 3, 4]
        while time.monotonic() < deadline and best[0] < moore:
            k = rng.choice(ks)
            base = best[0] // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, 3))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, deadline, 1500)
            if res is not None:
                consider(res)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
