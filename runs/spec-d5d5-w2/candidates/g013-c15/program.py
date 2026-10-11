import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Tunables.
# ----------------------------------------------------------------------------

MAX_GROUPS = 10        # groups tried per bi-Cayley order N
CLIMB_ITERS = 400      # annealing steps per (group, connection set) try
RESTARTS = 2           # random restarts of the connection set per group
ANNEAL_ITERS = 800     # annealing steps for multi-base lifts
SWEEP_WINDOW = 12      # bi-Cayley orders swept above the lower bound before resetting
SEARCH_SHARE = 0.6     # fraction of the budget spent on the lift search before repair
REPAIR_T_HI = 3.0      # repair annealing temperature (in bad-pair units), start
REPAIR_T_LO = 0.2      # repair annealing temperature, end
_BIG = 10 ** 9
_TABLE_CACHE = {}


# ----------------------------------------------------------------------------
# D = 3 and D = 4 baselines: projective planes, arc extensions, quadrangles.
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 5 for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


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


def _local_improve(m, s, point_lines, line_points, S, rng, deadline, iters):
    """Plateau-walking 1-swap local search growing a feasible load-bounded set S."""
    cl = [0] * m
    cp = [0] * m
    inS = [False] * m

    def add(P):
        inS[P] = True
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1

    def rem(P):
        inS[P] = False
        for L in point_lines[P]:
            cl[L] -= 1
        for Q in line_points[P]:
            cp[Q] -= 1

    def fits(P):
        return (all(cl[L] < s for L in point_lines[P])
                and all(cp[Q] < s for Q in line_points[P]))

    cur = list(S)
    for P in cur:
        add(P)
    best = list(cur)
    for it in range(iters):
        if (it & 63) == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        if fits(P):
            add(P)
            cur.append(P)
            if len(cur) > len(best):
                best = list(cur)
            continue
        if not cur:
            continue
        idx = rng.randrange(len(cur))
        R = cur[idx]
        rem(R)
        if fits(P):
            add(P)
            cur[idx] = P
        else:
            add(R)
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
    """Return a list of (n, edges) candidates, one per prime power q with q + 1 <= d."""
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
            g = _greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)
            g = _local_improve(m, s, point_lines, line_points, g, rng, deadline, 3000)
            cands.append(g)
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x|_r Z_k with a bounded annealed connection set.
#
# Vertices A_x and B_y (x, y in G). Edge A_x -- B_{x s} for s in S, |S| = d.
# Left multiplication is an automorphism, so eccentricities from A_0 and B_0
# decide the diameter. The identity is WLOG in S.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(m, k, r):
    """Cached (order, mul, T, invs) for Z_m x|_r Z_k, where T[x][g] = x*g and invs[g] = g^-1."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, mul, T, invs)
    if len(_TABLE_CACHE) >= 48:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Count vertex pairs (source, target) not within distance D, from A_0 and B_0."""
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _climb(N, T, invs, d, D, rng, iters, deadline):
    """Anneal a connection set S (identity fixed in S) to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        temp = 0.3 + 1.5 * (1.0 - it / iters)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _bicayley_search(N, d, D, rng, deadline):
    """Try groups of order N with restarts; return (T, S) on success, else None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        _, _, T, invs = _tables(m, k, r)
        for _ in range(RESTARTS):
            if time.monotonic() > deadline:
                break
            S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
            if S is not None:
                return T, S
    return None


# ----------------------------------------------------------------------------
# Multi-base voltage lifts over semidirect products, annealed.
# Each of the d layers is a perfect matching between k A-base and k B-base
# vertices, with one voltage per dart. Left multiplication is an automorphism,
# so one representative per base vertex suffices for the diameter check.
# ----------------------------------------------------------------------------

def _right_perm(mul, G, s):
    """Permutation g -> g*s of the group."""
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
    """Edge list of the lift, A-vertices first, B-vertices after."""
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
    temp = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(T_end, temp * decay)

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
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
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
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# NEW: subdivision growth + degree-preserving double-edge-swap repair.
#
# Given a valid-ish graph on n0 vertices, add one A-vertex and one B-vertex.
# Each new vertex is attached by "subdividing" d existing edges: an edge (a, b)
# (a in A, b in B) becomes (a, B_new) and (A_new, b), so every old degree is
# unchanged and each new vertex reaches degree d. The diameter is then repaired
# by annealing over double-edge swaps, which also preserve all degrees.
# The cost is the number of unordered pairs at distance > D, evaluated with
# bitmask balls (Python big ints), which is fast for a few hundred vertices.
# ----------------------------------------------------------------------------

def _two_color(n, edges):
    """Return a 0/1 bipartition colouring of the graph, or None if it is not bipartite."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
                elif col[v] == col[u]:
                    return None
    return col


def _bad_bits(n, nbr, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs included)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in nbr[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _grow_repair(n0, edges0, d, D, deadline, rng):
    """Add one A and one B vertex to a bipartite graph and repair the diameter.

    Returns a validated (n, edges) on n0 + 2 vertices, or None.
    """
    col = _two_color(n0, edges0)
    if col is None:
        return None
    n = n0 + 2
    a_new, b_new = n0, n0 + 1
    nbr = [set() for _ in range(n)]
    E = []
    for u, v in edges0:
        nbr[u].add(v)
        nbr[v].add(u)
        E.append((u, v) if col[u] == 0 else (v, u))

    # Attach the new vertices: each step subdivides one old edge (a, b).
    for _ in range(d):
        placed = False
        for _try in range(400):
            i = rng.randrange(len(E))
            a, b = E[i]
            if b in nbr[a_new] or a in nbr[b_new]:
                continue
            nbr[a].discard(b)
            nbr[b].discard(a)
            nbr[a].add(b_new)
            nbr[b_new].add(a)
            nbr[a_new].add(b)
            nbr[b].add(a_new)
            E[i] = (a, b_new)
            E.append((a_new, b))
            placed = True
            break
        if not placed:
            return None

    m_e = len(E)
    if m_e < 2:
        return None
    cur = _bad_bits(n, nbr, D)
    t_start = time.monotonic()
    span = max(1e-3, deadline - t_start)
    while cur > 0:
        now = time.monotonic()
        if now > deadline:
            return None
        frac = (now - t_start) / span
        T = REPAIR_T_HI * (REPAIR_T_LO / REPAIR_T_HI) ** frac

        i = rng.randrange(m_e)
        j = rng.randrange(m_e)
        if i == j:
            continue
        a, b = E[i]   # a in A, b in B
        c, e = E[j]   # c in A, e in B
        if a == c or b == e or e in nbr[a] or b in nbr[c]:
            continue
        # Double-edge swap: (a,b),(c,e) -> (a,e),(c,b). All degrees preserved.
        nbr[a].discard(b)
        nbr[b].discard(a)
        nbr[c].discard(e)
        nbr[e].discard(c)
        nbr[a].add(e)
        nbr[e].add(a)
        nbr[c].add(b)
        nbr[b].add(c)
        E[i] = (a, e)
        E[j] = (c, b)
        c2 = _bad_bits(n, nbr, D)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c2
        else:
            nbr[a].discard(e)
            nbr[e].discard(a)
            nbr[c].discard(b)
            nbr[b].discard(c)
            nbr[a].add(b)
            nbr[b].add(a)
            nbr[c].add(e)
            nbr[e].add(c)
            E[i] = (a, b)
            E[j] = (c, e)

    edges = [(min(u, v), max(u, v)) for u, v in E]
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    search_deadline = start + SEARCH_SHARE * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and meets the Moore bound 2d for D = 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Structured baselines.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if best[0] < moore:
            for n_c, e_c in _arc_extensions(d, start + 0.3 * budget,
                                            random.Random(seed * 7919 + d)):
                consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: aim strictly above the current best order.
    sweep = None
    while best[0] < moore and time.monotonic() < search_deadline:
        n_best = best[0]

        if d >= 2 and rng.random() < 0.6:
            lo = n_best // 2 + 1
            if lo > moore // 2:
                break
            if sweep is None or sweep < lo or sweep > lo + SWEEP_WINDOW:
                sweep = lo
            N = sweep
            sweep += 1
            found = _bicayley_search(N, d, D, rng, search_deadline)
            if found is not None:
                T, S = found
                consider(2 * N, [(x, N + T[x][g]) for x in range(N) for g in S])
        else:
            k = rng.choice((2, 3))
            lo = n_best // (2 * k) + 1
            if 2 * k * lo > moore:
                continue
            G = lo + rng.randrange(max(2, lo // 10))
            m, k2, r = rng.choice(_groups(G))
            order, mul, _ = lib.semidirect_group(m, k2, r)
            res = _anneal(d, D, k, order, mul, rng, search_deadline, ANNEAL_ITERS)
            if res is not None:
                consider(res[0], res[1])

    # Repair phase: grow the best graph by two vertices at a time while time remains.
    while best[0] < moore and time.monotonic() < deadline:
        grown = _grow_repair(best[0], best[1], d, D, deadline, rng)
        if grown is None or grown[0] <= best[0]:
            break
        best = grown

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
