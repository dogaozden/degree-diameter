import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane based constructions (diameter 3).
#
# Start from the incidence graph of PG(2, q): points 0..m-1, lines m..2m-1.
# Every old vertex has degree q+1, so it has spare s = d - q - 1.
#
# A-side: a family of "A-vertices". Each A-vertex is adjacent to a set N of
#   lines (|N| <= d). Requirements:
#     (a) N covers every point (so A-vertex is within distance 2 of all points),
#     (b) N shares a line with every other A-vertex's set (A-A distance 2),
#     (c) each line lies in at most s A-sets (line degree stays <= d).
#   Pencils (all lines through a point P) are the simplest such sets; they give
#   the classical "arc" construction (sets of size q+1, no three points collinear).
#   Non-pencil covers with extra lines can exceed that arc bound.
# B-side: symmetric with points and lines swapped (dual blocking sets).
#
# A-vertices and B-vertices are always within distance 3 of each other: for an
# A-set N and a B-set M (blocking), any line L in N meets some point of M on L.
# ----------------------------------------------------------------------------

_ITERS = 6000
_LAM = 2


def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, nbr):
    """True if every target t is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements x so that every target is hit by <= s chosen elements."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_bases(d, deadline, rng):
    """Arc-type base graphs (pencil-based) for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, pl, lp, index, pts = _pg_data(q)
        SA = _greedy_side(m, s, pl, rng, 40, deadline)
        SB = _greedy_side(m, s, lp, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, pl):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, lp):
                SB = cs
        if not (_loads_ok(SA, s, m, pl) and _loads_ok(SB, s, m, lp)):
            continue
        n_c, e_c = _arc_graph(m, edges, pl, lp, SA, SB)
        out.append({"q": q, "m": m, "edges": edges, "pl": pl, "lp": lp,
                    "SA": SA, "SB": SB, "n": n_c, "E": e_c})
    return out


def _find_cover(inc, hit_by, nt, ne, elig, E_list, K, rng, deadline):
    """Simulated annealing for K distinct elements of elig whose inc-sets cover all nt targets
    and which intersect every set in E_list. Returns the element list or None."""
    elig_set = set(elig)
    Eof = [[] for _ in range(ne)]
    for idx, E in enumerate(E_list):
        for x in E:
            Eof[x].append(idx)
    nE = len(E_list)

    # Seed: a star (all elements through a random target) padded with random elements.
    t0 = rng.randrange(nt)
    seeds = [e for e in hit_by[t0] if e in elig_set]
    rng.shuffle(seeds)
    N = seeds[:K]
    inN = [False] * ne
    for x in N:
        inN[x] = True
    while len(N) < K:
        x = elig[rng.randrange(len(elig))]
        if not inN[x]:
            inN[x] = True
            N.append(x)

    cnt = [0] * nt
    for x in N:
        for t in inc[x]:
            cnt[t] += 1
    unc = sum(1 for t in range(nt) if cnt[t] == 0)
    hit = [0] * nE
    for x in N:
        for e in Eof[x]:
            hit[e] += 1
    viol = sum(1 for e in range(nE) if hit[e] == 0)
    cost = unc + _LAM * viol

    T0, T1 = 1.0, 0.05
    for it in range(_ITERS):
        if cost == 0:
            break
        if it % 500 == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / _ITERS)
        i = rng.randrange(K)
        x = N[i]
        y = elig[rng.randrange(len(elig))]
        if inN[y]:
            continue
        # remove x
        for t in inc[x]:
            cnt[t] -= 1
            if cnt[t] == 0:
                unc += 1
        for e in Eof[x]:
            hit[e] -= 1
            if hit[e] == 0:
                viol += 1
        # add y
        for t in inc[y]:
            if cnt[t] == 0:
                unc -= 1
            cnt[t] += 1
        for e in Eof[y]:
            if hit[e] == 0:
                viol -= 1
            hit[e] += 1
        new_cost = unc + _LAM * viol
        delta = new_cost - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new_cost
            N[i] = y
            inN[x] = False
            inN[y] = True
        else:
            # revert add y
            for e in Eof[y]:
                hit[e] -= 1
                if hit[e] == 0:
                    viol += 1
            for t in inc[y]:
                cnt[t] -= 1
                if cnt[t] == 0:
                    unc += 1
            # revert remove x
            for e in Eof[x]:
                if hit[e] == 0:
                    viol -= 1
                hit[e] += 1
            for t in inc[x]:
                if cnt[t] == 0:
                    unc -= 1
                cnt[t] += 1

    if cost == 0:
        return N
    return None


def _grow(inc, hit_by, nt, ne, cap, E_init, K, rng, deadline):
    """Greedily add covering sets for one side. cap[x] is the remaining capacity of element x
    (it is decreased in place). Returns the list of new element sets."""
    E_list = [list(E) for E in E_init]
    new = []
    fails = 0
    while fails < 4 and time.monotonic() < deadline:
        elig = [x for x in range(ne) if cap[x] > 0]
        if len(elig) < K:
            break
        N = _find_cover(inc, hit_by, nt, ne, elig, E_list, K, rng, deadline)
        if N is None:
            fails += 1
            continue
        fails = 0
        new.append(N)
        E_list.append(list(N))
        for x in N:
            cap[x] -= 1
    return new


def _grow_candidate(q, d, m, edges, pl, lp, SA, SB, rng, deadline):
    """Extend the arc base (SA, SB) by covering A-sets and blocking B-sets; return (n, edges) or None."""
    s = d - q - 1
    capA = [s] * m          # lines: spare degree for A-vertices
    for P in SA:
        for L in pl[P]:
            capA[L] -= 1
    capB = [s] * m          # points: spare degree for B-vertices
    for j in SB:
        for Q in lp[j]:
            capB[Q] -= 1
    if min(capA) < 0 or min(capB) < 0:
        return None
    K = min(d, m)
    now = time.monotonic()
    mid = now + 0.5 * (deadline - now)
    # A side: element = line, target = point; a line covers its points.
    newA = _grow(lp, pl, m, m, capA, [pl[P] for P in SA], K, rng, mid)
    # B side: element = point, target = line; a point blocks its lines.
    newB = _grow(pl, lp, m, m, capB, [lp[j] for j in SB], K, rng, deadline)

    n0, E0 = _arc_graph(m, edges, pl, lp, SA, SB)
    E = list(E0)
    nn = n0
    for N in newA:
        for L in N:
            E.append((nn, m + L))
        nn += 1
    for M in newB:
        for P in M:
            E.append((P, nn))
        nn += 1
    return nn, E


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
# ----------------------------------------------------------------------------

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
# Simulated annealing over bi-Cayley voltage lifts (fallback for D >= 4).
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g in the group.
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
    """Permutation g -> mul(g, s) of the group."""
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

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        try:
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
        except Exception:
            pass

    if D >= 3:
        arcs = _arc_bases(d, deadline, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda a: -a["n"])
        for a in arcs:
            consider(a["n"], a["E"])

        # Growth only for bases whose order could plausibly beat the current best:
        # each side can gain extra vertices on top of its 2m PG vertices.
        grow_list = [a for a in arcs if 2 * a["m"] + 2 * d > best_n]
        grow_list.sort(key=lambda a: -a["m"])
        for idx, a in enumerate(grow_list):
            now = time.monotonic()
            if now > deadline:
                break
            share = (deadline - now) / (len(grow_list) - idx)
            mid = now + 0.5 * share
            try:
                # (1) grow from scratch on the PG incidence graph
                r = _grow_candidate(a["q"], d, a["m"], a["edges"], a["pl"], a["lp"],
                                    [], [], rng, mid)
                if r is not None:
                    consider(r[0], r[1])
            except Exception:
                pass
            try:
                # (2) grow on top of the arc base
                r = _grow_candidate(a["q"], d, a["m"], a["edges"], a["pl"], a["lp"],
                                    a["SA"], a["SB"], rng, now + share)
                if r is not None:
                    consider(r[0], r[1])
            except Exception:
                pass

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: annealed group voltage lifts (fallback when nothing better was found).
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < deadline:
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
