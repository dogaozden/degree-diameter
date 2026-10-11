import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from PG(2, q) incidence (points 0..m-1, lines m..2m-1). Each old vertex
# has degree q+1, so spare s = d - q - 1. Choose SA (points) so that every line
# holds <= s points of SA, and SB (lines) so that every point lies on <= s lines
# of SB. Add one A-vertex per SA point (joined to its q+1 lines) and one B-vertex
# per SB line (joined to its q+1 points). Order 2(q^2+q+1) + |SA| + |SB|.
# ----------------------------------------------------------------------------

_LS_ITERS = 20000


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
    """True if every target is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements so every target is hit by <= s chosen elements."""
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


def _local_search(m, s, nbr, S, rng, deadline, iters):
    """Plateau/improvement local search for the same load-constrained set problem."""
    if s < 1:
        return list(S)
    inS = [False] * m
    hits = [set() for _ in range(m)]
    for x in S:
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
    size = len(S)
    best = list(S)
    best_size = size
    for it in range(iters):
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        x = rng.randrange(m)
        if inS[x]:
            continue
        rem = set()
        ok = True
        for t in nbr[x]:
            cur = [y for y in hits[t] if y not in rem]
            if len(cur) >= s:
                rem.add(rng.choice(cur))
                if len(rem) > 2:
                    ok = False
                    break
        if not ok:
            continue
        if len(rem) == 2 and rng.random() > 0.03:
            continue
        for y in rem:
            inS[y] = False
            for t in nbr[y]:
                hits[t].discard(y)
        inS[x] = True
        for t in nbr[x]:
            hits[t].add(x)
        size += 1 - len(rem)
        if size > best_size:
            best_size = size
            best = [i for i in range(m) if inS[i]]
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
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


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for the most promising prime powers q with q + 1 <= d."""
    qs = [q for q in range(2, min(d - 1, 23) + 1) if lib.is_prime_power(q)]

    def bound(q):
        s = d - q - 1
        mm = q * q + q + 1
        return 2 * mm + 2 * s * mm // (q + 1)

    qs.sort(key=lambda q: -bound(q))
    out = []
    for q in qs[:4]:
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        F = lib.GF(q)
        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, F)
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs
        SA = _local_search(m, s, point_lines, SA, rng, deadline, _LS_ITERS)
        SB = _local_search(m, s, line_points, SB, rng, deadline, _LS_ITERS)
        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


# ----------------------------------------------------------------------------
# Cyclic and non-abelian Haar graphs from group covers (diameter 3).
#
# For a group G of order N and a k-subset S, H = H(G, S) has a_g ~ b_{gs}.
# A-A distance <= 2 needs S S^-1 = G; B-B distance <= 2 needs S^-1 S = G;
# A-B distance 3 then follows. Order 2N, degree k.
# ----------------------------------------------------------------------------

def _tables(order, mul, inv):
    """Multiplication and inverse tables of a finite group with identity 0."""
    mt = [[mul(a, b) for b in range(order)] for a in range(order)]
    iv = [inv(a) for a in range(order)]
    return mt, iv


def _group_options(N, rng):
    """Cyclic group of order N plus a few random semidirect products Z_m x| Z_k2 of order N."""
    opts = [lib.cyclic_group(N)]
    cands = []
    for k2 in range(2, N + 1):
        if N % k2:
            continue
        m = N // k2
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                cands.append((m, k2, r))
    rng.shuffle(cands)
    for m, k2, r in cands[:8]:
        try:
            opts.append(lib.semidirect_group(m, k2, r))
        except ValueError:
            pass
    return opts


def _counts(S, N, mt, iv):
    """c1[x] = #ordered pairs (s,t), s != t, with s t^-1 = x; c2 with s^-1 t; z = uncovered count."""
    k = len(S)
    c1 = [0] * N
    c2 = [0] * N
    for i in range(k):
        a = S[i]
        for j in range(k):
            if i != j:
                b = S[j]
                c1[mt[a][iv[b]]] += 1
                c2[mt[iv[a]][b]] += 1
    z = sum(1 for x in range(1, N) if c1[x] == 0) + sum(1 for x in range(1, N) if c2[x] == 0)
    return c1, c2, z


def _swap(S, inS, c1, c2, i, y, mt, iv, k, z):
    """Replace S[i] by y (y not in S), update counts and uncovered count z; return new z."""
    old = S[i]
    for j in range(k):
        if j != i:
            t = S[j]
            x = mt[old][iv[t]]
            c1[x] -= 1
            if c1[x] == 0:
                z += 1
            x = mt[iv[old]][t]
            c2[x] -= 1
            if c2[x] == 0:
                z += 1
    inS[old] = False
    S[i] = y
    inS[y] = True
    for j in range(k):
        if j != i:
            t = S[j]
            x = mt[y][iv[t]]
            if c1[x] == 0:
                z -= 1
            c1[x] += 1
            x = mt[iv[y]][t]
            if c2[x] == 0:
                z -= 1
            c2[x] += 1
    return z


def _cover(N, k, mt, iv, deadline, rng):
    """Find a k-subset S with S S^-1 = G = S^-1 S, or return None on timeout."""
    S = rng.sample(range(N), k)
    inS = [False] * N
    for x in S:
        inS[x] = True
    c1, c2, z = _counts(S, N, mt, iv)
    stall = 0
    T = 0.35
    it = 0
    while z > 0:
        it += 1
        if (it & 127) == 0 and time.monotonic() > deadline:
            return None
        if stall > 50000:  # restart from a fresh random set
            S = rng.sample(range(N), k)
            inS = [False] * N
            for x in S:
                inS[x] = True
            c1, c2, z = _counts(S, N, mt, iv)
            stall = 0
            continue
        unc1 = [x for x in range(1, N) if c1[x] == 0]
        unc2 = [x for x in range(1, N) if c2[x] == 0]
        if not unc1 and not unc2:
            # Counter drift guard: resynchronise from scratch.
            c1, c2, z = _counts(S, N, mt, iv)
            if z == 0:
                break
            continue
        if unc2 and (not unc1 or rng.random() < 0.5):
            kind, x = 2, rng.choice(unc2)
        else:
            kind, x = 1, rng.choice(unc1)
        j = rng.randrange(k)
        t = S[j]
        # Focused move: the new element y creates a pair covering the chosen residue x.
        y = mt[x][t] if kind == 1 else mt[t][x]
        if inS[y]:
            stall += 1
            continue
        i = rng.randrange(k - 1)
        if i >= j:
            i += 1
        old = S[i]
        z2 = _swap(S, inS, c1, c2, i, y, mt, iv, k, z)
        delta = z2 - z
        if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / T)):
            if z2 < z:
                stall = 0
            else:
                stall += 1
            z = z2
        else:
            z = _swap(S, inS, c1, c2, i, old, mt, iv, k, z2)
            stall += 1
    # Final verification with a clean recount.
    _, _, zc = _counts(S, N, mt, iv)
    if zc != 0:
        return None
    return sorted(S)


def _haar_search(k, deadline, rng):
    """Largest group Haar graph with |S| = k found before the deadline, as (n, edges), or None."""
    cap = k * (k - 1) + 1
    if k < 2 or cap < 3:
        return None
    best = None
    N = max(k + 1, int(0.6 * cap))
    while N <= cap and time.monotonic() < deadline:
        found = None
        for _ in range(4):
            now = time.monotonic()
            if now >= deadline:
                break
            end = min(deadline, now + max(1.0, 0.35 * (deadline - now)))
            order, mul, inv = rng.choice(_group_options(N, rng))
            mt, iv = _tables(order, mul, inv)
            S = _cover(N, k, mt, iv, end, rng)
            if S is not None:
                found = (N, S, mt)
                break
        if found is None:
            break
        best = found
        N += 1
    if best is None:
        return None
    N, S, mt = best
    E = [(g, N + mt[g][s]) for s in S for g in range(N)]
    return 2 * N, E


# ----------------------------------------------------------------------------
# Greedy vertex insertion with ball-cover certificates.
# A new vertex w joined to N on the opposite side reaches x within D exactly when
# x lies within distance D-1 of some u in N.
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
            if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / T)):
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
            if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / T)):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
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
        try:
            ok = n > best_n and lib.is_valid(n, e, d, D)
        except Exception:
            ok = False
        if ok:
            best = (n, e)
            best_n = n

    arc_top = None
    if D >= 3:
        # Arc-extended projective planes: the strong baseline (394 for d = 16).
        arcs = _arc_extensions(d, start + 0.12 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)
        if arcs:
            arc_top = arcs[0]
        # Group-cover Haar graphs: main search for diameter 3.
        hg_end = start + (0.78 if D == 3 else 0.30) * time_limit
        try:
            hg = _haar_search(d, hg_end, rng)
        except Exception:
            hg = None
        if hg is not None:
            consider(hg[0], hg[1])

    if D >= 4:
        if time.monotonic() < start + 0.35 * time_limit:
            gq = _best_gq(d)
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
            res = _anneal(d, D, k, order, mul, rng, search_end, iters=400)
            if res is not None:
                consider(res[0], res[1])

    if D >= 3:
        # Vertex insertion into spare-degree graphs.
        if arc_top is not None:
            n_a, e_a = _augment(arc_top[0], arc_top[1], d, D, rng, start + 0.88 * time_limit)
            consider(n_a, e_a)
        if time.monotonic() < start + 0.90 * time_limit:
            n_f, e_f = _augment(best[0], best[1], d, D, rng, start + 0.92 * time_limit)
            consider(n_f, e_f)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
