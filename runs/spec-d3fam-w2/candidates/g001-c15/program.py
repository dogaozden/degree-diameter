import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Fallbacks and base constructions.
# ----------------------------------------------------------------------------

def _fallback(d, D):
    """Safe graphs that are valid by construction."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:
        return lib.haar_graph(d, range(d))          # K_{d,d}, diameter 2
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


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
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Arc-extended projective plane graphs (diameter 3).
# ----------------------------------------------------------------------------

def _pg_data(q):
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
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
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
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
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
# Cover-based vertex extension and edge saturation.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bipartition(n, adj):
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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(200):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Matching-rewire growth for diameter 3.
# ----------------------------------------------------------------------------

def _random_matching(Eo, d, rng):
    pool = list(Eo)
    rng.shuffle(pool)
    used = set()
    R = []
    for u, v in pool:
        if u in used or v in used:
            continue
        R.append((u, v))
        used.add(u)
        used.add(v)
        if len(R) == d:
            return R
    return None


def _rewire_build(n, Eo_set, R):
    Rkeys = {(min(u, v), max(u, v)) for u, v in R}
    out = [e for e in Eo_set if (min(e[0], e[1]), max(e[0], e[1])) not in Rkeys]
    x, y = n, n + 1
    for u, v in R:
        out.append((x, v))
        out.append((u, y))
    return n + 2, out


def _pair_search(n, E, d, D, deadline, rng):
    adj = [[] for _ in range(n)]
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    col = _bipartition(n, adj)
    if any(col[u] == col[v] for u, v in E):
        return None
    Eo = [(u, v) if col[u] == 0 else (v, u) for u, v in E]
    if len(Eo) < d:
        return None
    R = _random_matching(Eo, d, rng)
    if R is None:
        return None

    def cost(RR):
        nn, ee = _rewire_build(n, Eo, RR)
        return lib.bad_pairs(nn, ee, D)

    c = cost(R)
    t_start = time.monotonic()
    span = max(1e-6, deadline - t_start)
    while time.monotonic() < deadline:
        if c == 0:
            return _rewire_build(n, Eo, R)
        frac = (time.monotonic() - t_start) / span
        T = 1.0 * (0.05 ** frac)
        i = rng.randrange(d)
        cand = Eo[rng.randrange(len(Eo))]
        used = set()
        for j, (a, b) in enumerate(R):
            if j != i:
                used.add(a)
                used.add(b)
        if cand[0] in used or cand[1] in used:
            continue
        newR = list(R)
        newR[i] = cand
        c2 = cost(newR)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            R, c = newR, c2
    if c == 0:
        return _rewire_build(n, Eo, R)
    return None


def _pair_grow(n, E, d, D, deadline, rng):
    cur_n, cur_e = n, list(E)
    while time.monotonic() < deadline:
        res = _pair_search(cur_n, cur_e, d, D, deadline, rng)
        if res is None:
            break
        cur_n, cur_e = res
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Cayley-type bipartite lifts: two base vertices, darts from a difference cover.
# a_x ~ b_{x s} for s in S. Diameter <= 3 when S S^{-1} = G.
# ----------------------------------------------------------------------------

def _group_list(N, rng):
    groups = [lib.cyclic_group(N)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:4]:
            try:
                groups.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return groups


def _ratio_table(N, mul, inv):
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


def _search(N, R, d, rng, steps, deadline):
    """Annealing search for d distinct elements S with S S^{-1} = G."""
    S = rng.sample(range(N), d)

    def uncovered(S):
        return N - len({R[a][b] for a in S for b in S})

    cost = uncovered(S)
    T = 0.6
    for _ in range(steps):
        if cost == 0:
            return S
        if time.monotonic() > deadline:
            return None
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        new = uncovered(S)
        if new <= cost or rng.random() < math.exp(-(new - cost) / T):
            cost = new
        else:
            S[i] = old
    return S if cost == 0 else None


def _cayley_phase(d, rng, deadline, consider, get_n):
    """Round-robin annealing over difference-cover groups of order N, largest N first."""
    hi = d * (d - 1) + 1
    jobs = []
    for N in range(hi, d - 1, -1):
        for _o, mul, inv in _group_list(N, rng):
            jobs.append([N, mul, inv, None])
    while time.monotonic() < deadline:
        jobs = [j for j in jobs if j[0] > get_n() // 2]
        if not jobs:
            break
        for job in list(jobs):
            if time.monotonic() >= deadline:
                break
            N, mul, inv, R = job
            if N <= get_n() // 2:
                continue
            if R is None:
                R = _ratio_table(N, mul, inv)
                job[3] = R
            S = _search(N, R, d, rng, 1500, deadline)
            if S is None:
                continue
            n, e = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
            consider(n, e)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    rng = random.Random(seed)

    def at(f):
        return start + f * total

    if d <= 0 or D <= 0:
        return 1, []

    base = _fallback(d, D)
    if not lib.is_valid(base[0], base[1], d, D):
        return 1, []

    state = {"n": base[0], "e": base[1]}

    def consider(n, e):
        if n > state["n"] and lib.is_valid(n, e, d, D):
            state["n"], state["e"] = n, e
            return True
        return False

    def get_n():
        return state["n"]

    if D <= 2 or d < 3:
        return state["n"], state["e"]

    if D == 3:
        # Moore-extremal case is already optimal.
        if lib.is_prime_power(d - 1):
            return state["n"], state["e"]

        # Araujo-Pardo & Lopez record construction for d = q + 2.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

        # Plain projective plane, grown by cover extension and saturation.
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            n2, e2 = _grow(pg[0], pg[1], d, D, at(0.15), rng)
            consider(n2, e2)

        # Arc-extended projective plane graphs.
        for n_c, e_c in _arc_extensions(d, at(0.25), random.Random(seed * 7919 + d)):
            consider(n_c, e_c)

        # Cayley difference-cover lifts.
        _cayley_phase(d, random.Random(seed + 17), at(0.6), consider, get_n)

        # Matching-rewire growth from the best graph found so far.
        n3, e3 = _pair_grow(state["n"], state["e"], d, D, at(1.0),
                            random.Random(seed + 101))
        consider(n3, e3)

    elif D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            n2, e2 = _grow(gq[0], gq[1], d, D, at(0.8), rng)
            consider(n2, e2)

    if not lib.is_valid(state["n"], state["e"], d, D):
        return base[0], base[1]
    return state["n"], state["e"]
