import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
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


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# NEW (bold change for D = 3): Haar graphs over NON-CYCLIC groups.
#
# Let G be a finite group of order m and S a k-subset of G. The Haar graph
# H(G, S) has parts A = {a_x} and B = {b_y}, with a_x ~ b_{x s} for s in S.
# It is k-regular on 2m vertices and left translation is an automorphism.
#
# Distances from a_1: a_1 reaches a_g in two steps iff g is in S S^{-1}.
# Distances from b_1: b_1 reaches b_g in two steps iff g is in S^{-1} S.
# If S S^{-1} = G and S^{-1} S = G, then A-A and B-B pairs are within 2, and
# A-B pairs are within 3. So H(G, S) has diameter 3 whenever both covers hold.
# Since |S S^{-1}| <= k(k-1)+1, m <= k(k-1)+1 again. Cyclic groups are only one
# option. Semidirect products Z_a x| Z_b often admit covers when cyclic ones
# do not, so the search tries many groups of each order.
# ----------------------------------------------------------------------------

def _groups_of_order(m):
    """Semidirect products Z_a x| Z_b with a*b = m, a >= 2, as (a, b, r). b = 1 gives cyclic Z_m."""
    out = []
    for b in range(1, m + 1):
        if m % b:
            continue
        a = m // b
        if a < 2:
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, b, a) == 1 % a:
                out.append((a, b, r))
    return out


def _group_tables(a, b, r):
    """Return (order, M, INV): full multiplication table and inverse list, identity = 0."""
    order, mul, inv = lib.semidirect_group(a, b, r)
    M = [[mul(x, y) for y in range(order)] for x in range(order)]
    INV = [inv(x) for x in range(order)]
    return order, M, INV


def _apply(S, i, y, M, INV, cA, cB, cost):
    """Replace S[i] by y, updating the coverage counts and the deficiency cost. Returns the new cost.

    cA[g] = #{(s,t) ordered, s != t, s t^-1 = g}; cB[g] = #{(s,t), s != t, s^-1 t = g}.
    cost = #{g != 0 : cA[g] = 0} + #{g != 0 : cB[g] = 0}.
    """
    k = len(S)
    old = S[i]
    for j in range(k):
        if j == i:
            continue
        t = S[j]
        g = M[old][INV[t]]
        cA[g] -= 1
        if cA[g] == 0:
            cost += 1
        g = M[t][INV[old]]
        cA[g] -= 1
        if cA[g] == 0:
            cost += 1
        g = M[INV[old]][t]
        cB[g] -= 1
        if cB[g] == 0:
            cost += 1
        g = M[INV[t]][old]
        cB[g] -= 1
        if cB[g] == 0:
            cost += 1
    S[i] = y
    for j in range(k):
        if j == i:
            continue
        t = S[j]
        g = M[y][INV[t]]
        if cA[g] == 0:
            cost -= 1
        cA[g] += 1
        g = M[t][INV[y]]
        if cA[g] == 0:
            cost -= 1
        cA[g] += 1
        g = M[INV[y]][t]
        if cB[g] == 0:
            cost -= 1
        cB[g] += 1
        g = M[INV[t]][y]
        if cB[g] == 0:
            cost -= 1
        cB[g] += 1
    return cost


def _sa_group(k, m, M, INV, deadline, rng):
    """Simulated annealing for S of size k in a group of order m with both covers. Returns sorted S or None."""
    if m < k or k * (k - 1) + 1 < m:
        return None
    while time.monotonic() < deadline:
        S = rng.sample(range(m), k)
        inS = [False] * m
        for s in S:
            inS[s] = True
        cA = [0] * m
        cB = [0] * m
        for i in range(k):
            for j in range(k):
                if i != j:
                    s, t = S[i], S[j]
                    cA[M[s][INV[t]]] += 1
                    cB[M[INV[s]][t]] += 1
        cost = sum(1 for g in range(1, m) if cA[g] == 0) + sum(1 for g in range(1, m) if cB[g] == 0)
        T = 0.6
        moves = 0
        while cost > 0 and moves < 200000:
            moves += 1
            if (moves & 1023) == 0 and time.monotonic() > deadline:
                return None
            i = rng.randrange(k)
            y = rng.randrange(m)
            if inS[y]:
                continue
            old = S[i]
            c2 = _apply(S, i, y, M, INV, cA, cB, cost)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
                inS[old] = False
                inS[y] = True
            else:
                _apply(S, i, old, M, INV, cA, cB, c2)
            T = max(0.15, T * 0.99995)
        if cost == 0:
            return sorted(S)
    return None


def _haar_group_graph(order, M, S):
    """Haar graph H(G, S): a_x (0..order-1) ~ b_{x s} (order + x*s) for s in S."""
    E = []
    for x in range(order):
        for s in S:
            E.append((x, order + M[x][s]))
    return 2 * order, E


def _try_order(k, m, deadline, rng):
    """Search groups of order m for a valid S; returns (order, S, M) or None."""
    if m < k or k * (k - 1) + 1 < m:
        return None
    groups = _groups_of_order(m)
    rng.shuffle(groups)
    groups = groups[:8]
    for idx, (a, b, r) in enumerate(groups):
        now = time.monotonic()
        if now >= deadline:
            break
        remaining = deadline - now
        sub_end = min(deadline, now + 1.5 * remaining / max(1, len(groups) - idx))
        try:
            order, M, INV = _group_tables(a, b, r)
        except ValueError:
            continue
        S = _sa_group(k, order, M, INV, sub_end, rng)
        if S is not None:
            return order, S, M
    return None


def _group_haar_search(d, deadline, rng):
    """Climb the order m of Haar graphs H(G, S) with |S| = d; return (n, edges) or None."""
    k = d
    cap = k * (k - 1) + 1
    if k < 2 or cap < 3:
        return None
    best = None
    target = max(k + 1, int(0.75 * cap))
    fails = 0
    while time.monotonic() < deadline and k + 1 <= target <= cap:
        now = time.monotonic()
        slice_end = min(deadline, now + max(2.0, 0.3 * (deadline - now)))
        res = _try_order(k, target, slice_end, rng)
        if res is not None:
            best = _haar_group_graph(res[0], res[2], res[1])
            fails = 0
            target += 1
        else:
            fails += 1
            if best is None:
                target = max(k + 1, target - 3)
            elif fails >= 2:
                break
    return best


# ----------------------------------------------------------------------------
# Greedy vertex insertion with ball-cover certificates ("_augment").
# ----------------------------------------------------------------------------

def _side_colors(n, adj):
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


def _ball_masks(n, adj, R):
    """Bitmask of all vertices within distance R of each vertex."""
    reach = [1 << v for v in range(n)]
    for _ in range(R):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return reach


def _augment(n, edges, d, D, rng, deadline, max_fails=60):
    """Greedily insert vertices whose neighbourhoods cover the graph within D. Returns (n, edges)."""
    if n == 0 or D < 2:
        return n, list(edges)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _side_colors(n, adj)
    R = D - 1
    fails = 0
    while time.monotonic() < deadline and fails < max_fails:
        balls = _ball_masks(n, adj, R)
        full = (1 << n) - 1
        added = False
        sides = [0, 1]
        rng.shuffle(sides)
        for side in sides:
            base_cand = [u for u in range(n) if color[u] == 1 - side and len(adj[u]) < d]
            if not base_cand:
                continue
            for _attempt in range(4):
                cand = base_cand[:]
                rng.shuffle(cand)
                covered = 0
                chosen = []
                pool = cand
                while covered != full and len(chosen) < d and pool:
                    best_gain, bu, bi = 0, None, -1
                    for i, u in enumerate(pool):
                        g = (balls[u] & ~covered).bit_count()
                        if g > best_gain:
                            best_gain, bu, bi = g, u, i
                    if bu is None:
                        break
                    chosen.append(bu)
                    covered |= balls[bu]
                    pool = pool[:bi] + pool[bi + 1:]
                if covered == full:
                    w = n
                    n += 1
                    adj.append(set())
                    color.append(side)
                    for u in chosen:
                        adj[u].add(w)
                        adj[w].add(u)
                    added = True
                    break
            if added:
                break
        if added:
            fails = 0
            continue
        fails += 1
        spare_a = [u for u in range(n) if len(adj[u]) < d and color[u] == 0]
        spare_b = [u for u in range(n) if len(adj[u]) < d and color[u] == 1]
        if spare_a and spare_b:
            for _ in range(20):
                u = rng.choice(spare_a)
                v = rng.choice(spare_b)
                if u != v and v not in adj[u]:
                    adj[u].add(v)
                    adj[v].add(u)
                    break
    out = [(u, v) for u in range(n) for v in adj[u] if u < v]
    return n, out


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
# Simulated annealing over bi-Cayley voltage lifts (used for D >= 4).
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


def _safe(fn, *args):
    """Run a construction stage; any failure just yields None so the fallback still applies."""
    try:
        return fn(*args)
    except Exception:
        return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
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
        # Cheap projective-plane candidates first (valid fallbacks).
        arcs = _safe(_arc_extensions, d, start + 0.08 * time_limit,
                     random.Random(seed * 7919 + d)) or []
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)
        # Main new construction: Haar graphs over (possibly non-cyclic) groups.
        hg = _safe(_group_haar_search, d, start + 0.85 * time_limit, rng)
        if hg is not None:
            consider(hg[0], hg[1])
    else:
        if D >= 3:
            arcs = _safe(_arc_extensions, d, start + 0.10 * time_limit,
                         random.Random(seed * 7919 + d)) or []
            arcs.sort(key=lambda t: -t[0])
            for n_c, e_c in arcs[:3]:
                consider(n_c, e_c)
            if arcs:
                n_a, e_a = arcs[0]
                r_aug = _safe(_augment, n_a, e_a, d, D, rng, start + 0.30 * time_limit)
                if r_aug is not None:
                    consider(r_aug[0], r_aug[1])

        if D >= 4 and time.monotonic() < start + 0.30 * time_limit:
            gq = _safe(_best_gq, d)
            if gq is not None:
                consider(gq[0], gq[1])

        search_end = start + 0.55 * time_limit
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < search_end:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _safe(_anneal, d, D, k, order, mul, rng, search_end, 400)
            if res is not None:
                consider(res[0], res[1])

        if D >= 2 and time.monotonic() < start + 0.85 * time_limit:
            r_f = _safe(_augment, best[0], best[1], d, D, rng, start + 0.85 * time_limit)
            if r_f is not None:
                consider(r_f[0], r_f[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
