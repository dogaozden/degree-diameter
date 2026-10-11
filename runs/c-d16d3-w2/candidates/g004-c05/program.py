import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Every old vertex has degree q+1,
# so with d >= q+1 it has spare capacity s = d - q - 1. Choose a point set S such
# that every line holds <= s points of S and every point lies on <= s lines
# indexed by S. Add a new A-vertex per P in S (joined to the lines through P)
# and a new B-vertex per j in S (joined to the points on line j).
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
# NEW for D = 3: non-abelian Haar graphs from two-sided difference bases.
#
# Let G be a finite group (here Z_m x| Z_k, which includes cyclic and direct
# products) and S a k-subset of G. Define the bipartite graph on G x {A, B}
# with a_g ~ b_{g s} for s in S. It is k-regular on 2|G| vertices.
#
#   a_1 reaches a_{s t^-1} in 2 steps   -> need S S^-1 = G
#   b_1 reaches b_{s^-1 t} in 2 steps   -> need S^-1 S = G
#   a_1 reaches b_x in 3 steps via S S^-1 S = G automatically.
#
# Left multiplication is an automorphism, so these checks cover all pairs.
# So diameter 3 holds whenever both covers hold. Since |G|-1 <= k(k-1), the
# order is at most 2(k^2-k+1). Unlike the cyclic search, non-abelian groups
# give extra freedom. The search is annealing on both difference families at once.
# ----------------------------------------------------------------------------

def _group_tables(m, k2, r):
    """Return (order, M, I): full multiplication and inverse tables; identity is index 0."""
    order, mul, inv = lib.semidirect_group(m, k2, r)
    M = [[mul(a, b) for b in range(order)] for a in range(order)]
    I = [inv(a) for a in range(order)]
    return order, M, I


def _group_options(G):
    """All (m, k2, r) with m * k2 = G giving a semidirect product Z_m x| Z_k2 (r = 1 gives a direct product)."""
    opts = []
    for k2 in range(1, G + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            opts.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                opts.append((m, k2, r))
    return opts


def _gcounts(S, M, I, G):
    """Counts c1 (for s t^-1) and c2 (for s^-1 t) over ordered pairs s != t, plus the number of uncovered non-identity elements."""
    c1 = [0] * G
    c2 = [0] * G
    for a in S:
        for b in S:
            if a != b:
                c1[M[a][I[b]]] += 1
                c2[M[I[a]][b]] += 1
    zeros = sum(1 for x in range(1, G) if c1[x] == 0) + sum(1 for x in range(1, G) if c2[x] == 0)
    return c1, c2, zeros


def _gmove(S, c1, c2, M, I, i, y, zeros):
    """Replace S[i] by y (y not in S), updating counts. Returns the new number of uncovered elements."""
    k = len(S)
    old = S[i]
    Io = I[old]
    for j in range(k):
        if j == i:
            continue
        t = S[j]
        x = M[old][I[t]]
        c1[x] -= 1
        if c1[x] == 0:
            zeros += 1
        x = M[t][Io]
        c1[x] -= 1
        if c1[x] == 0:
            zeros += 1
        x = M[Io][t]
        c2[x] -= 1
        if c2[x] == 0:
            zeros += 1
        x = M[I[t]][old]
        c2[x] -= 1
        if c2[x] == 0:
            zeros += 1
    S[i] = y
    Iy = I[y]
    for j in range(k):
        if j == i:
            continue
        t = S[j]
        x = M[y][I[t]]
        if c1[x] == 0:
            zeros -= 1
        c1[x] += 1
        x = M[t][Iy]
        if c1[x] == 0:
            zeros -= 1
        c1[x] += 1
        x = M[Iy][t]
        if c2[x] == 0:
            zeros -= 1
        c2[x] += 1
        x = M[I[t]][y]
        if c2[x] == 0:
            zeros -= 1
        c2[x] += 1
    return zeros


def _gcover(k, M, I, G, deadline, rng):
    """Annealing for a k-subset S of G with S S^-1 = G and S^-1 S = G. Returns sorted S or None."""
    if k * (k - 1) < G - 1:
        return None
    S = rng.sample(range(G), k)
    c1, c2, zeros = _gcounts(S, M, I, G)
    T = 0.3
    it = 0
    while zeros > 0:
        it += 1
        if it % 256 == 0 and time.monotonic() > deadline:
            return None
        if it % 100000 == 0:
            S[:] = rng.sample(range(G), k)
            c1, c2, zeros = _gcounts(S, M, I, G)
            continue
        i = rng.randrange(k)
        y = rng.randrange(G)
        if y in S:
            continue
        old = S[i]
        z = _gmove(S, c1, c2, M, I, i, y, zeros)
        delta = z - zeros
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            zeros = z
        else:
            _gmove(S, c1, c2, M, I, i, old, z)
    return sorted(S)


def _group_haar(G, S, M):
    """Bipartite graph with a_g ~ b_{g s} for s in S: returns (2G, edges)."""
    E = []
    for g in range(G):
        for s in S:
            E.append((g, G + M[g][s]))
    return 2 * G, E


def _group_search(k, deadline, rng):
    """Find the largest group order G (with a valid two-sided difference basis of size k) before the deadline. Returns (G, S, M) or None."""
    cap = k * (k - 1) + 1
    G = max(k + 1, int(0.7 * cap))
    best = None
    fails = 0
    while G <= cap and time.monotonic() < deadline:
        opts = _group_options(G)
        if not opts:
            G += 1
            continue
        rng.shuffle(opts)
        opts = opts[:6]
        now = time.monotonic()
        budget = max(0.5, 0.4 * (deadline - now))
        per = budget / len(opts)
        found = None
        for m, k2, r in opts:
            if time.monotonic() >= deadline:
                break
            order, M, I = _group_tables(m, k2, r)
            S = _gcover(k, M, I, order, min(deadline, time.monotonic() + per), rng)
            if S is not None:
                found = (order, S, M)
                break
        if found is None:
            fails += 1
            if fails >= 3:
                break
        else:
            best = found
            G += 1
            fails = 0
    return best


# ----------------------------------------------------------------------------
# Greedy vertex insertion with ball-cover certificates (for D >= 4).
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

    arcs = []
    if D >= 3:
        # Projective-plane arc extensions (the conic gives the record for d = q + 3).
        arcs = _arc_extensions(d, start + 0.10 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)
        # NEW: two-sided difference-basis Haar graphs over (possibly non-abelian) groups.
        group_end = start + (0.85 if D == 3 else 0.40) * time_limit
        res = _group_search(d, group_end, rng)
        if res is not None:
            G, S, M = res
            n_g, e_g = _group_haar(G, S, M)
            consider(n_g, e_g)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
        if arcs:
            n_a, e_a = arcs[0]
            n2, e2 = _augment(n_a, e_a, d, D, rng, start + 0.90 * time_limit)
            consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
