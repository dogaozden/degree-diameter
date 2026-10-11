import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare capacity
# s = d - q - 1. Choose a point set S with every line holding <= s points of S
# and every point lying on <= s lines indexed by S. Each P in S gets an "A"
# vertex (a pencil: the q+1 lines through P, which covers all points), and
# each j in S gets a "B" vertex (the q+1 points on line j).
#
# NEW (this island): copy-aware pencil augmentation.
# A line-side vertex whose neighbourhood is exactly the points of line L is a
# "copy" of line L; old line L and the B-vertex for L (if L is in the index
# set S) are both copies. Dually for points. Any new point-side vertex adjacent
# to one copy of each line through some point P' reaches every point within 2
# steps, so it is a legitimate new pencil. Each old vertex keeps spare degree,
# so such pencils can be added greedily. Each candidate is checked with
# lib.is_valid and rolled back on failure, so the stored graph is always valid.
# ----------------------------------------------------------------------------

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


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
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


def _arc_graph(m, edges, S, point_lines, line_points):
    """Extended graph; returns (n, edges, Aid, Bid) with Aid[P] and Bid[j] the new vertex ids."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    Aid, Bid = {}, {}
    for t, P in enumerate(S):
        x = 2 * m + t
        Aid[P] = x
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        Bid[j] = b
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E, Aid, Bid


def _arc_candidates(d, deadline, rng):
    """Arc-graph candidates (dicts) for every prime power q with q + 1 <= d, plus sub-arc variants."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, pl, lp, index, pts = _pg_data(q)
        seeds = []
        if s >= 1:
            seeds.append(_greedy_arc(m, s, pl, lp, rng, 40, deadline))
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, pl, lp):
                seeds.append(cs)
        if not seeds:
            seeds.append([])
        for S0 in seeds:
            variants = [S0]
            if len(S0) >= 3:
                variants.append(rng.sample(S0, len(S0) - 2))
            if len(S0) >= 5:
                variants.append(rng.sample(S0, len(S0) - 4))
            for S in variants:
                if not _loads_ok(S, s, m, pl, lp):
                    continue
                n, E, Aid, Bid = _arc_graph(m, edges, S, pl, lp)
                out.append({"n": n, "E": E, "m": m, "pl": pl, "lp": lp,
                            "Aid": Aid, "Bid": Bid, "q": q, "s": s})
    return out


def _augment(c, d, D, rng, deadline):
    """Greedily add copy-aware pencil vertices (point side and line side), validity-checked."""
    n = c["n"]
    E = list(c["E"])
    m, pl, lp = c["m"], c["pl"], c["lp"]
    deg = [0] * n
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    # copies: vertices whose neighbourhood equals the lines through P (point copies)
    # or the points on L (line copies).
    pt_copies = [[P] for P in range(m)]
    ln_copies = [[m + L] for L in range(m)]
    for P, x in c["Aid"].items():
        pt_copies[P].append(x)
    for j, b in c["Bid"].items():
        ln_copies[j].append(b)

    N = n
    improved = True
    while improved and time.monotonic() < deadline:
        improved = False
        centers = [(0, P) for P in range(m)] + [(1, L) for L in range(m)]
        rng.shuffle(centers)
        for kind, ctr in centers:
            if time.monotonic() > deadline:
                break
            if kind == 0:
                sets = [ln_copies[L] for L in pl[ctr]]
            else:
                sets = [pt_copies[Q] for Q in lp[ctr]]
            nb = []
            ok = True
            for st in sets:
                cand = [v for v in st if deg[v] < d]
                if not cand:
                    ok = False
                    break
                cand.sort()  # prefer the original vertices
                nb.append(cand[0] if rng.random() < 0.5 else rng.choice(cand))
            if not ok:
                continue
            x = N
            N += 1
            deg.append(len(nb))
            for v in nb:
                deg[v] += 1
            added = [(x, v) for v in nb]
            E.extend(added)
            if lib.is_valid(N, E, d, D):
                improved = True
                if kind == 0:
                    pt_copies[ctr].append(x)
                else:
                    ln_copies[ctr].append(x)
            else:
                del E[-len(added):]
                for v in nb:
                    deg[v] -= 1
                deg.pop()
                N -= 1
    if lib.is_valid(N, E, d, D):
        return N, E
    return c["n"], c["E"]


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
# Simulated annealing over group voltage lifts (used for D != 3).
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
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        cands = _arc_candidates(d, start + 0.15 * time_limit,
                                random.Random(seed * 7919 + d))
        cands.sort(key=lambda c: -c["n"])
        for c in cands[:5]:
            consider(c["n"], c["E"])
        # Copy-aware pencil augmentation on the most promising bases.
        top = cands[:3]
        for i, c in enumerate(top):
            now = time.monotonic()
            remain = deadline - now
            if remain <= 0:
                break
            sub = now + remain / (len(top) - i)
            n2, e2 = _augment(c, d, D, rng, sub)
            consider(n2, e2)
    else:
        if D >= 4 and time.monotonic() < deadline:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])

        # Annealed group voltage lifts for the remaining cases.
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
