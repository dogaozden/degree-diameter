import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Tunables.
# ----------------------------------------------------------------------------

MAX_GROUPS = 10          # semidirect groups tried per bi-Cayley order N
CLIMB_ITERS = 400        # annealing steps per semidirect (group, S) try
RESTARTS = 2             # restarts of the connection set per semidirect group
ANNEAL_ITERS = 800       # annealing steps for multi-base lifts
SWEEP_WINDOW = 12        # semidirect bi-Cayley orders swept above the bound
CAT_ITERS = 700          # annealing steps per catalog (non-metabelian) try
CAT_RESTARTS = 2         # restarts per catalog group
CAT_CACHE_MAX = 12       # cached group tables
_BIG = 10 ** 9
_TABLE_CACHE = {}
_CAT_CACHE = {}
_CAT_ATTEMPTS = {}

# Non-metabelian base groups, given as projective / special linear groups over GF(p).
# (spec, order). Products with cyclic groups are generated from these.
_BASE_GROUPS = [
    (('mat', 3, 'PSL'), 12),     # A4
    (('mat', 3, 'SL'), 24),      # SL(2,3)
    (('mat', 3, 'PGL'), 24),     # S4
    (('mat', 5, 'PSL'), 60),     # A5
    (('mat', 5, 'SL'), 120),     # SL(2,5)
    (('mat', 5, 'PGL'), 120),    # S5
    (('mat', 7, 'PSL'), 168),    # PSL(2,7)
    (('mat', 7, 'SL'), 336),     # SL(2,7)
    (('mat', 7, 'PGL'), 336),    # PGL(2,7)
]


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
# Group tables. Every group is given as (T, invs) with T[x][y] = x*y, identity 0.
# ----------------------------------------------------------------------------

def _normalize(T):
    """Relabel so the identity is index 0; return (T, invs)."""
    N = len(T)
    e = next(x for x in range(N) if T[x][x] == x)  # only the identity is idempotent
    if e != 0:
        perm = list(range(N))
        perm[0], perm[e] = e, 0
        T2 = [[0] * N for _ in range(N)]
        for x in range(N):
            row = T[x]
            new_row = T2[perm[x]]
            for y in range(N):
                new_row[perm[y]] = perm[row[y]]
        T = T2
    invs = [row.index(0) for row in T]
    return T, invs


def _mat_elements(p, kind):
    """Elements of SL, PSL or PGL over GF(p) (p prime), as canonical 2x2 tuples, and the canonicaliser."""
    inv = [0] + [pow(x, p - 2, p) for x in range(1, p)]

    def canon(M):
        if kind == 'PSL':
            neg = tuple((-x) % p for x in M)
            return min(M, neg)
        if kind == 'PGL':
            for x in M:
                if x:
                    c = inv[x]
                    return tuple(y * c % p for y in M)
        return M

    elems = set()
    for M in itertools.product(range(p), repeat=4):
        det = (M[0] * M[3] - M[1] * M[2]) % p
        if kind == 'PGL':
            if det == 0:
                continue
        elif det != 1:
            continue
        elems.add(canon(M))
    return sorted(elems), canon


def _mat_table(p, kind):
    """Multiplication table of SL, PSL or PGL over GF(p)."""
    els, canon = _mat_elements(p, kind)
    idx = {M: i for i, M in enumerate(els)}
    T = []
    for A in els:
        a, b, c, dd = A
        row = []
        for B in els:
            e, f, g, h = B
            M = ((a * e + b * g) % p, (a * f + b * h) % p,
                 (c * e + dd * g) % p, (c * f + dd * h) % p)
            row.append(idx[canon(M)])
        T.append(row)
    return T


def _prod_table(TA, TB):
    """Direct product table of two group tables; element (a, b) is coded as a*|B| + b."""
    NA, NB = len(TA), len(TB)
    N = NA * NB
    T = [[0] * N for _ in range(N)]
    for a in range(NA):
        for b in range(NB):
            row = T[a * NB + b]
            RA = TA[a]
            RB = TB[b]
            for a2 in range(NA):
                base = RA[a2] * NB
                for b2 in range(NB):
                    row[a2 * NB + b2] = base + RB[b2]
    return T


def _build_spec(spec):
    """Return (T, invs) for a catalog spec: ('mat', p, kind) or ('prod', spec, c)."""
    hit = _CAT_CACHE.get(spec)
    if hit is not None:
        return hit
    if spec[0] == 'mat':
        T = _mat_table(spec[1], spec[2])
    else:
        TH, _ = _build_spec(spec[1])
        c = spec[2]
        TC = [[(x + y) % c for y in range(c)] for x in range(c)]
        T = _prod_table(TH, TC)
    val = _normalize(T)
    if len(_CAT_CACHE) >= CAT_CACHE_MAX:
        _CAT_CACHE.clear()
    _CAT_CACHE[spec] = val
    return val


def _cat_entries(lo, hi):
    """Catalog specs (order, spec) with lo <= order <= hi: base groups and products with Z_c."""
    out = []
    for spec, h in _BASE_GROUPS:
        if h > hi:
            continue
        for c in range(1, hi // h + 1):
            order = h * c
            if order < lo:
                continue
            s = spec if c == 1 else ('prod', spec, c)
            out.append((order, s))
    return out


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over a group G with a bounded annealed connection set.
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


def _catalog_attempt(lo, hi, d, D, rng, deadline):
    """Try the least-tried catalog group with order in [lo, hi]; return (n, edges) or None."""
    ents = _cat_entries(lo, hi)
    if not ents:
        return None
    order, spec = min(ents, key=lambda e: (_CAT_ATTEMPTS.get(e[1], 0), e[0]))
    _CAT_ATTEMPTS[spec] = _CAT_ATTEMPTS.get(spec, 0) + 1
    T, invs = _build_spec(spec)
    N = len(T)
    found = None
    for _ in range(CAT_RESTARTS):
        if time.monotonic() > deadline:
            break
        found = _climb(N, T, invs, d, D, rng, CAT_ITERS, deadline)
        if found is not None:
            break
    if found is None:
        return None
    return 2 * N, [(x, N + T[x][g]) for x in range(N) for g in found]


def _bicayley_search(N, d, D, rng, deadline):
    """Try semidirect groups of order N with restarts; return (T, S) on success, else None."""
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
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
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
    half_moore = moore // 2
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        lo = n_best // 2 + 1
        if lo > half_moore:
            break
        try:
            r = rng.random()
            if r < 0.55:
                # Non-metabelian and product groups: SL/PSL/PGL over GF(p), times cyclic groups.
                res = _catalog_attempt(lo, half_moore, d, D, rng, deadline)
                if res is not None:
                    consider(res[0], res[1])
            elif r < 0.85:
                # Semidirect bi-Cayley lifts (metabelian groups).
                if sweep is None or sweep < lo or sweep > lo + SWEEP_WINDOW:
                    sweep = lo
                N = sweep
                sweep += 1
                found = _bicayley_search(N, d, D, rng, deadline)
                if found is not None:
                    T, S = found
                    consider(2 * N, [(x, N + T[x][g]) for x in range(N) for g in S])
            else:
                # Multi-base voltage lifts over semidirect products.
                k = rng.choice((2, 3))
                lo_k = n_best // (2 * k) + 1
                if 2 * k * lo_k <= moore:
                    G = lo_k + rng.randrange(max(2, lo_k // 10))
                    m, k2, r_ = rng.choice(_groups(G))
                    order, mul, _ = lib.semidirect_group(m, k2, r_)
                    res = _anneal(d, D, k, order, mul, rng, deadline, ANNEAL_ITERS)
                    if res is not None:
                        consider(res[0], res[1])
        except MemoryError:
            break
        except Exception:
            # Any unexpected failure in one attempt must not lose the valid best graph.
            continue

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
