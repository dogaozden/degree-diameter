import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline: projective plane incidence graphs and K_{d,d}.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Different construction: random configuration-model group lifts.
#
# Base graph: k vertices on each side, each with d "stubs". A random perfect
# matching between A-stubs and B-stubs gives the base multigraph (so degrees
# are d but the base is NOT forced to be a union of permutation layers).
# Each dart carries a voltage v in a group G = Z_m x| Z_k2, and the lift is
#     A(i, x) ~ B(j, x*v).
# Left multiplication by G is an automorphism, so distances from the k
# representatives A(i, e) and B(j, e) to all vertices decide the diameter.
# Simulated annealing moves: re-voltage a dart (defect-targeted) or swap two
# B-endpoints of the base matching. Cost = unreached (representative, vertex)
# pairs plus a penalty per duplicated dart (which would make a parallel edge).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs). Element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e).

    Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h.
    """
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _build_nbr(k, G, d, Ts, Invs, pi, V):
    """Neighbour table (N, d) of the lift, plus the number of duplicated darts.

    A-stub s = i*d + e belongs to A-block i and column e.
    B-stub t = j*d + f belongs to B-block j and column f; pi[s] = t.
    """
    N = 2 * k * G
    nbr = np.empty((N, d), dtype=np.int64)
    seen = set()
    dups = 0
    for s in range(k * d):
        i, e = divmod(s, d)
        j, f = divmod(pi[s], d)
        v = V[s]
        key = (i, j, v)
        if key in seen:
            dups += 1
        else:
            seen.add(key)
        nbr[i * G:(i + 1) * G, e] = (k + j) * G + Ts[v]
        nbr[(k + j) * G:(k + j + 1) * G, f] = i * G + Invs[v]
    return nbr, dups


def _cost(k, G, d, D, nbr, dups):
    """Return (cost, reach). reach[v] is a bitmask over the 2k representatives."""
    N = nbr.shape[0]
    reach = np.zeros(N, dtype=np.int64)
    for a in range(2 * k):
        reach[a * G] = 1 << a
    for _ in range(D):
        new = reach.copy()
        for e in range(d):
            new |= reach[nbr[:, e]]
        if np.array_equal(new, reach):
            break
        reach = new
    unreached = 2 * k * N - int(_POP[reach].sum())
    return unreached + _PENALTY * dups, reach


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters):
    """Simulated annealing over base matchings and voltages. Returns (n, edges) or None."""
    full = (1 << (2 * k)) - 1
    nd = k * d
    pi = list(range(nd))
    rng.shuffle(pi)
    V = [rng.randrange(G) for _ in range(nd)]
    nbr, dups = _build_nbr(k, G, d, Ts, Invs, pi, V)
    cost, reach = _cost(k, G, d, D, nbr, dups)
    c0 = float(max(cost, 1))

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.3, 0.02 * c0 * (1.0 - it / iters))
        old_pi = pi[:]
        old_V = V[:]

        if rng.random() < 0.25:
            # Rematch move: swap the B-endpoints of two darts.
            s1, s2 = rng.sample(range(nd), 2)
            pi[s1], pi[s2] = pi[s2], pi[s1]
        else:
            pinv = [0] * nd
            for s, t in enumerate(pi):
                pinv[t] = s
            s = None
            if rng.random() < 0.4:
                bad = np.flatnonzero(reach != full)
                if bad.size:
                    u = int(bad[rng.randrange(bad.size)])
                    blk = u // G
                    if blk < k:
                        s = blk * d + rng.randrange(d)
                    else:
                        j = blk - k
                        s = pinv[j * d + rng.randrange(d)]
            if s is None:
                s = rng.randrange(nd)
            V[s] = rng.randrange(G)

        nbr2, dups2 = _build_nbr(k, G, d, Ts, Invs, pi, V)
        c2, r2 = _cost(k, G, d, D, nbr2, dups2)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach, nbr, dups = c2, r2, nbr2, dups2
        else:
            pi, V = old_pi, old_V

    if cost != 0 or dups != 0:
        return None
    N = nbr.shape[0]
    edges = {(min(u, v), max(u, v)) for u in range(N) for v in nbr[u].tolist()}
    if len(edges) != N * d // 2:
        return None
    return N, sorted(edges)


# ----------------------------------------------------------------------------
# Bipartition colouring and greedy pair insertion (adds 2 vertices per step).
# ----------------------------------------------------------------------------

def _two_color(n, edges):
    adj = lib.adjacency(n, edges)
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
                elif color[v] == color[u]:
                    return None
    return color


def _extend(n, edges, d, D, rng, deadline, max_fail=300):
    if d < 1 or not edges:
        return n, edges
    color = _two_color(n, edges)
    if color is None:
        return n, edges
    edges = list(edges)
    color = list(color)
    fails = 0
    while time.monotonic() < deadline and fails < max_fail:
        order = list(range(len(edges)))
        rng.shuffle(order)
        chosen = []
        used_a, used_b = set(), set()
        for t in order:
            if len(chosen) == d - 1:
                break
            u, v = edges[t]
            a, b = (u, v) if color[u] == 0 else (v, u)
            if a in used_a or b in used_b:
                continue
            chosen.append(t)
            used_a.add(a)
            used_b.add(b)
        if len(chosen) < d - 1:
            break
        x, y = n, n + 1
        cs = set(chosen)
        cand = [e for t, e in enumerate(edges) if t not in cs]
        for t in chosen:
            u, v = edges[t]
            a, b = (u, v) if color[u] == 0 else (v, u)
            cand.append((x, b))
            cand.append((y, a))
        cand.append((x, y))
        if lib.is_valid(n + 2, cand, d, D):
            edges = cand
            n += 2
            color.extend([0, 1])
            fails = 0
        else:
            fails += 1
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    search_deadline = start + 0.8 * budget
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

    # Exact construction for the calibration-style case d-1 prime power, D = 3.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Main search: random configuration-model group lifts.
    try:
        while time.monotonic() < search_deadline:
            k = rng.choice(_KS)
            need = best_n // (2 * k) + 1
            target = max(2, need + rng.randrange(0, max(2, need // 50 + 2)))
            g = _sample_group(target, rng)
            if g is None:
                continue
            m, k2, r = g
            G, Ts, Invs = _semidirect_tables(m, k2, r)
            if 2 * k * G <= best_n:
                continue
            run_deadline = min(search_deadline, time.monotonic() + 6.0)
            res = _search(d, D, k, G, Ts, Invs, rng, run_deadline, 15000)
            if res is not None:
                consider(res[0], res[1])
    except Exception:
        pass

    # Greedy pair insertion on the best graph found so far.
    try:
        n2, e2 = _extend(best_n, best[1], d, D, rng, deadline)
        if n2 > best_n:
            consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
