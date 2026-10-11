import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Diameter-3 construction: projective plane PG(2, q) plus extra vertices.
#
# Vertex j (0 <= j < m) is point j and vertex m + j is line j. Let s = d - q - 1
# be the spare degree at every old vertex. A "family" is a list of K index sets
# N_t, each of size d, subsets of 0..m-1 satisfying:
#   (cover) every point x lies on some line j in N_t          (A-vertex reaches all points in 2)
#   (meet)  any two sets N_t, N_u share an index              (A-A distance 2)
#   (load)  every index j lies in at most s sets              (degree <= d for lines and points)
# For each t add an A-vertex joined to the lines N_t and a B-vertex joined to the
# points N_t. By polarity the B-side conditions are the same as the A-side ones,
# so the same family serves both sides. Order is 2m + 2K.
#
# The parent used the conic as the family (K = q + 1 = 14 for d = 16, giving 394).
# This version starts from the parent's pencil family, padded to size d, and adds
# one extra set at a time. Each new set is found by simulated annealing over
# swaps, minimizing uncovered points plus pairs of sets that share no index.
# Every candidate is re-verified with lib.is_valid before it can be returned.
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


def _baseline_arc(q, s, m, point_lines, line_points, index, rng, deadline):
    """Largest arc-type set S found by the conic or greedy search, with loads <= s."""
    S = []
    if s >= 1:
        S = _greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)
    if s >= 2:
        cs = _conic_set(q, index, lib.GF(q))
        if _loads_ok(cs, s, m, point_lines, line_points) and len(cs) > len(S):
            S = cs
    return S


def _graph_from_family(m, edges, fam):
    """Old PG(2,q) incidence plus an A-vertex per set (on lines) and a B-vertex per set (on points)."""
    K = len(fam)
    E = list(edges)
    for t, N in enumerate(fam):
        a = 2 * m + t
        b = 2 * m + K + t
        for j in N:
            E.append((a, m + j))
            E.append((j, b))
    return 2 * m + 2 * K, E


def _random_extra(fam, m, s, d, rng):
    """A random set of size d using only indices whose load is still below s, or None."""
    use = [0] * m
    for N in fam:
        for j in N:
            use[j] += 1
    free = [j for j in range(m) if use[j] < s]
    if len(free) < d:
        return None
    return rng.sample(free, d)


def _family_search(fam, m, s, d, line_points, rng, deadline):
    """Simulated annealing over swaps inside the sets of fam until cover+meet+load hold.

    Returns the repaired family, or None if the deadline passes first.
    """
    fam = [list(N) for N in fam]
    K = len(fam)
    inset = [[False] * m for _ in range(K)]
    use = [0] * m
    cov = [[0] * m for _ in range(K)]
    for t, N in enumerate(fam):
        for j in N:
            inset[t][j] = True
            use[j] += 1
            for x in line_points[j]:
                cov[t][x] += 1
    if max(use) > s:
        return None
    inter = [[0] * K for _ in range(K)]
    for t in range(K):
        for u in range(t + 1, K):
            v = sum(1 for j in fam[t] if inset[u][j])
            inter[t][u] = v
            inter[u][t] = v
    cost = 0
    for t in range(K):
        cost += sum(1 for c in cov[t] if c == 0)
    cost += sum(1 for t in range(K) for u in range(t + 1, K) if inter[t][u] == 0)

    def move(t, i, a, b):
        """Replace index a by b in set t (fam[t][i] == a). Return the cost change."""
        ct = cov[t]
        dcost = 0
        for x in line_points[a]:
            ct[x] -= 1
            if ct[x] == 0:
                dcost += 1
        for x in line_points[b]:
            if ct[x] == 0:
                dcost -= 1
            ct[x] += 1
        it = inter[t]
        for u in range(K):
            if u == t:
                continue
            v = it[u]
            nv = v - inset[u][a] + inset[u][b]
            if (v == 0) != (nv == 0):
                dcost += 1 if nv == 0 else -1
            it[u] = nv
            inter[u][t] = nv
        inset[t][a] = False
        inset[t][b] = True
        use[a] -= 1
        use[b] += 1
        fam[t][i] = b
        return dcost

    T0, T1 = 1.5, 0.1
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    T = T0
    it_count = 0
    while cost > 0:
        it_count += 1
        if it_count % 256 == 0:
            now = time.monotonic()
            if now >= deadline:
                return None
            frac = (now - start) / span
            T = T0 * (T1 / T0) ** frac
        t = rng.randrange(K)
        i = rng.randrange(d)
        a = fam[t][i]
        b = rng.randrange(m)
        if inset[t][b] or use[b] >= s:
            continue
        delta = move(t, i, a, b)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost += delta
        else:
            move(t, i, b, a)
    return fam


def _pg_family_candidates(d, deadline, rng):
    """Return a list of (n, edges) graphs for diameter 3; the last one is the largest found."""
    plans = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, _pts = _pg_data(q)
        S = _baseline_arc(q, s, m, point_lines, line_points, index, rng, deadline)
        plans.append((2 * m + 2 * len(S), q, s, m, edges, point_lines, line_points, S))
    if not plans:
        return []
    plans.sort(key=lambda p: -p[0])
    _n, q, s, m, edges, point_lines, line_points, S = plans[0]

    fam = [list(point_lines[P]) for P in S]
    out = [_graph_from_family(m, edges, fam)]
    if s < 1:
        return out

    # Pad every baseline set to size d using indices whose load is still below s.
    use = [0] * m
    for N in fam:
        for j in N:
            use[j] += 1
    for N in fam:
        Nset = set(N)
        need = d - len(N)
        cand = [j for j in range(m) if use[j] < s and j not in Nset]
        if len(cand) < need:
            return out
        add = rng.sample(cand, need)
        for j in add:
            use[j] += 1
        N.extend(add)

    # Add one set at a time and search until the family is valid or time runs out.
    while time.monotonic() < deadline:
        extra = _random_extra(fam, m, s, d, rng)
        if extra is None:
            break
        trial = [list(N) for N in fam] + [extra]
        res = _family_search(trial, m, s, d, line_points, rng, deadline)
        if res is None:
            break
        fam = res
        out.append(_graph_from_family(m, edges, fam))
    return out


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
# Simulated annealing over bi-Cayley voltage lifts (unchanged from parent).
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
    deadline = start + 0.7 * time_limit
    # Diameter-3 family search gets nearly all the time for D = 3 targets.
    fam_deadline = start + (0.7 if D == 3 else 0.25) * time_limit
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

    # Diameter 3: projective-plane families with local search for extra sets.
    if D >= 3:
        for n_c, e_c in _pg_family_candidates(d, fam_deadline, rng):
            consider(n_c, e_c)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search for D >= 4: annealed group voltage lifts. Larger bases for D >= 5.
    if D >= 4:
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
