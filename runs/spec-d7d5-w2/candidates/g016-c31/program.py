"""Bi-Cayley lifts over semidirect products Z_m x| Z_k, searched with tabu local search.

Construction (general D): vertices A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h, where G = Z_m x| Z_k.
Each of the d layers is a permutation pairing A-blocks with B-blocks, with a voltage s, so
A_{i,g} ~ B_{j,g*s}. The result is d-regular and bipartite by construction.

Search: tabu local search over voltages and layer swaps. Each step picks a defect (a vertex
whose reach bitmask is incomplete), evaluates a small random set of moves that touch it,
and applies the best non-tabu one. Cost = unreached (block, vertex) pairs + duplicate-dart penalty.
A found lift is accepted only if lib.is_valid passes. Greedy pair insertion then tries to
extend the best graph. Safe fallback: K_{d,d} (diameter 2), plus exact PG(2,q) / W(q) constructions
where they apply.

Note: this is a heuristic search. Whether it beats a given record is not verified here.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4, 5, 6)
_TENURE = 7
_CANDS = 10


# ----------------------------------------------------------------------------
# Exact / baseline constructions.
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
# Group and lift helpers.
# ----------------------------------------------------------------------------

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
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e)).

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


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for A-block i and B-block j with voltage s (both directions)."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b set when representative block b is within distance D."""
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _unreached(k, N, reach):
    """Number of unreached (representative, vertex) pairs."""
    return 2 * k * N - int(_POP[reach].sum())


def _dups(d, k, layers, S):
    """Number of repeated (A-block, B-block, voltage) keys, i.e. duplicate darts."""
    seen = set()
    dup = 0
    for l in range(d):
        for i in range(k):
            key = (i, layers[l][i], S[l][i])
            if key in seen:
                dup += 1
            else:
                seen.add(key)
    return dup


# ----------------------------------------------------------------------------
# Tabu local search over bi-Cayley lifts.
# ----------------------------------------------------------------------------

def _climb(d, D, k, G, Ts, Invs, rng, deadline, max_steps):
    """Tabu search over voltages and layer swaps. Returns (n, edges) on success, else None."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def evaluate():
        r = _reach(k, G, D, nbr, d)
        c = _unreached(k, N, r) + _PENALTY * _dups(d, k, layers, S)
        return c, r

    def set_volt(l, i, s):
        S[l][i] = s
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], s)

    def swap(l, i1, i2):
        layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
        _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
        _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])

    cost, reach = evaluate()
    best_cost = cost
    last_improve = 0
    tabu = {}

    for step in range(max_steps):
        if cost == 0 or time.monotonic() > deadline:
            break

        bad = np.flatnonzero(reach != full)
        if bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
        else:
            block = rng.randrange(2 * k)

        # Build candidate moves that touch the chosen defect block.
        moves = []
        for _ in range(_CANDS):
            l = rng.randrange(d)
            if k >= 2 and rng.random() < 0.2:
                i1, i2 = rng.sample(range(k), 2)
                moves.append(("s", l, i1, i2, 0))
            else:
                if block < k:
                    i = block
                else:
                    i = layers[l].index(block - k)
                moves.append(("v", l, i, rng.randrange(G), 0))

        best_mv, best_c, best_r = None, None, None
        for mv in moves:
            if mv[0] == "s":
                _, l, i1, i2, _x = mv
                swap(l, i1, i2)
                c2, r2 = evaluate()
                swap(l, i1, i2)
            else:
                _, l, i, new, _x = mv
                old = S[l][i]
                if new == old:
                    continue
                if tabu.get((l, i, new), -1) > step and not (cost > 0 and False):
                    # Tabu move: only allowed if it beats the best cost seen so far.
                    set_volt(l, i, new)
                    c2, r2 = evaluate()
                    set_volt(l, i, old)
                    if c2 >= best_cost:
                        continue
                else:
                    set_volt(l, i, new)
                    c2, r2 = evaluate()
                    set_volt(l, i, old)
            if best_c is None or c2 < best_c:
                best_mv, best_c, best_r = mv, c2, r2

        if best_mv is None:
            continue

        if best_mv[0] == "s":
            _, l, i1, i2, _x = best_mv
            swap(l, i1, i2)
        else:
            _, l, i, new, _x = best_mv
            tabu[(l, i, S[l][i])] = step + _TENURE
            set_volt(l, i, new)
        cost, reach = best_c, best_r

        if cost < best_cost:
            best_cost = cost
            last_improve = step
        elif step - last_improve > 300:
            # Stagnation: random perturbation of a few voltages.
            for _ in range(3):
                set_volt(rng.randrange(d), rng.randrange(k), rng.randrange(G))
            cost, reach = evaluate()
            best_cost = min(best_cost, cost)
            last_improve = step

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


# ----------------------------------------------------------------------------
# Bipartition colouring and greedy pair insertion.
# ----------------------------------------------------------------------------

def _two_color(n, edges):
    """Return a proper 2-colouring (list of 0/1), or None if the graph is not bipartite."""
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


def _extend(n, edges, d, D, rng, deadline, max_attempts=300):
    """Greedy pair insertion: grow the order by 2 per accepted step, keeping validity."""
    if d < 1 or not edges:
        return n, edges
    color = _two_color(n, edges)
    if color is None:
        return n, edges
    edges = list(edges)
    color = list(color)
    attempts = 0
    while time.monotonic() < deadline and attempts < max_attempts:
        attempts += 1
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
    return n, edges


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = start + budget
    search_deadline = start + 0.80 * budget
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
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < search_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: tabu lifts over groups of order just above what the best graph needs.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    while time.monotonic() < search_deadline:
        if rng.random() < 0.5:
            k = rng.choice(_KS)
        else:
            k = max(_KS, key=lambda kk: (wins[kk] + 1) / (trials[kk] + 2) + 0.05 * rng.random())
        gmin = best_n // (2 * k) + 1
        target = gmin + rng.randrange(0, max(2, gmin // 50 + 2))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        attempt_deadline = min(search_deadline, time.monotonic() + 8.0)
        res = _climb(d, D, k, G, Ts, Invs, rng, attempt_deadline, 2000)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Greedy pair insertion on the best graph found so far.
    try:
        n2, e2 = _extend(best_n, best[1], d, D, rng, min(deadline, time.monotonic() + 4.0))
        if n2 > best_n:
            consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
