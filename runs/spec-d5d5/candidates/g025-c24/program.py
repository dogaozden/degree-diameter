import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Constructions for D = 3 and D = 4: projective planes, arc extensions,
# generalized quadrangles, and diameter-preserving growth.
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 7 for speed."""
    for q in range(min(d - 1, 7), 1, -1):
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


def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
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
    """Two-colouring of a bipartite graph given by adjacency lists."""
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
    """Greedy set cover of `full` by at most d candidate vertices; None if it fails."""
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
    """Greedily add vertices whose neighbourhoods cover all vertices within D-1 of the graph."""
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
    """Greedily join deficient opposite-side vertices in random order."""
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
    """Extend by cover vertices first, then saturate edges with the leftover spare degree."""
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
# Shared bi-Cayley machinery: reachability test on a group given by its
# multiplication table T and inverse table invs.
# Bi-Cayley graph: A_x ~ B_{x s} for s in S (identity WLOG in S).
# ----------------------------------------------------------------------------

MAX_GROUPS = 8        # groups tried per order N before moving on
CLIMB_ITERS = 300     # hill-climb steps per group
ANNEAL_ITERS = 600    # annealing steps for multi-base lifts
BAND_EXTRA = 12       # sweep window above the lower bound for bi-Cayley orders
SLICE = 2.5           # seconds per exotic group per round
_BIG = 10 ** 9
_TABLE_CACHE = {}


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
    """Count vertex pairs (source, target) not within distance D, from A_0 and B_0.

    Left translation is an automorphism, so eccentricities of A_0 and B_0 suffice.
    """
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
    """Hill-climb a connection set S (identity fixed as one dart, WLOG) to zero unreached pairs.

    Sideways moves are accepted, which lets the walk drift across plateaus.
    """
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur:
            S, cur = S2, v
    return S if cur == 0 else None


# ----------------------------------------------------------------------------
# BOLD CHANGE for D = 5: bi-Cayley lifts over exotic, non-metacyclic groups
# (A5, S5, PSL/PGL/SL(2,p), ASL(2,3), S4, A4, GL(2,3), and direct products
# with cyclic groups). Groups are built from permutation or matrix generators
# by closure, then multiplication tables are formed.
# ----------------------------------------------------------------------------

def _closure(gens, mul, ident, cap):
    """Elements of the group generated by gens (identity first), or None if more than cap."""
    elems = [ident]
    index = {ident: 0}
    frontier = [ident]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = mul(g, x)
                if y not in index:
                    if len(elems) >= cap:
                        return None
                    index[y] = len(elems)
                    elems.append(y)
                    nxt.append(y)
        frontier = nxt
    return elems, index


def _group_table(elems, index, mul):
    """Return (N, T, invs) with T[a][b] = index of elems[a]*elems[b]; identity is index 0."""
    N = len(elems)
    T = [[index[mul(elems[a], elems[b])] for b in range(N)] for a in range(N)]
    invs = [row.index(0) for row in T]
    return N, T, invs


def _perm_mul(g, x):
    """Composition g o x of permutations given as tuples."""
    return tuple(g[i] for i in x)


def _perm_base(gens):
    """Permutation group generated by gens, as (N, T, invs), or None if too large."""
    n = len(gens[0])
    cl = _closure(gens, _perm_mul, tuple(range(n)), 400)
    if cl is None:
        return None
    return _group_table(cl[0], cl[1], _perm_mul)


def _mat_mul_factory(dim, p):
    """Matrix product mod p for flat row-major tuples of size dim*dim."""
    def mul(A, B):
        out = []
        for i in range(dim):
            for j in range(dim):
                s = 0
                for k in range(dim):
                    s += A[i * dim + k] * B[k * dim + j]
                out.append(s % p)
        return tuple(out)
    return mul


def _mat_base(gens, dim, p):
    """Matrix group over GF(p) generated by gens, as (N, T, invs), or None if too large."""
    ident = tuple(1 if i == j else 0 for i in range(dim) for j in range(dim))
    mul = _mat_mul_factory(dim, p)
    cl = _closure(gens, mul, ident, 400)
    if cl is None:
        return None
    return _group_table(cl[0], cl[1], mul)


def _mobius_perm(p, a, b, c, d):
    """Permutation of the projective line PG(1, p) (points 0..p-1, infinity = p) by t -> (at+b)/(ct+d)."""
    out = []
    for t in range(p + 1):
        if t == p:
            img = p if c % p == 0 else (a * pow(c, p - 2, p)) % p
        else:
            num = (a * t + b) % p
            den = (c * t + d) % p
            img = p if den == 0 else (num * pow(den, p - 2, p)) % p
        out.append(img)
    return tuple(out)


def _mob_gens(p, proj):
    """Generators of PSL(2,p), or PGL(2,p) when proj is True, acting on PG(1,p)."""
    gens = [_mobius_perm(p, 1, 1, 0, 1), _mobius_perm(p, 0, p - 1, 1, 0)]
    if proj:
        g = next(x for x in range(2, p) if pow(x, (p - 1) // 2, p) == p - 1)
        gens.append(_mobius_perm(p, g, 0, 0, 1))
    return gens


def _sl2_gens(p):
    """Generators of SL(2,p) as flat 2x2 matrices."""
    return [(1, 1, 0, 1), (0, p - 1, 1, 0)]


_BASE_BUILDERS = {
    'A5': lambda: _perm_base([(1, 2, 0, 3, 4), (1, 2, 3, 4, 0)]),
    'S5': lambda: _perm_base([(1, 0, 2, 3, 4), (1, 2, 3, 4, 0)]),
    'A4': lambda: _perm_base([(1, 2, 0, 3), (1, 0, 3, 2)]),
    'S4': lambda: _perm_base([(1, 0, 2, 3), (1, 2, 3, 0)]),
    'PSL25': lambda: _perm_base(_mob_gens(5, False)),
    'PGL25': lambda: _perm_base(_mob_gens(5, True)),
    'PSL27': lambda: _perm_base(_mob_gens(7, False)),
    'PGL27': lambda: _perm_base(_mob_gens(7, True)),
    'SL25': lambda: _mat_base(_sl2_gens(5), 2, 5),
    'SL27': lambda: _mat_base(_sl2_gens(7), 2, 7),
    'SL23': lambda: _mat_base(_sl2_gens(3), 2, 3),
    'GL23': lambda: _mat_base(_sl2_gens(3) + [(1, 0, 0, 2)], 2, 3),
    'ASL23': lambda: _mat_base([
        (1, 0, 1, 0, 1, 0, 0, 0, 1),
        (1, 0, 0, 0, 1, 1, 0, 0, 1),
        (1, 1, 0, 0, 1, 0, 0, 0, 1),
        (0, 2, 0, 1, 0, 0, 0, 0, 1),
    ], 3, 3),
}

_ORDER = {'A5': 60, 'S5': 120, 'A4': 12, 'S4': 24, 'PSL25': 60, 'PGL25': 120,
          'SL25': 120, 'PSL27': 168, 'PGL27': 336, 'SL27': 336, 'SL23': 24,
          'GL23': 48, 'ASL23': 216}

# Each spec is a direct product of named factors ('C<k>' = cyclic of order k).
EXOTIC_SPECS = [
    ('PSL27',), ('A5', 'C3'), ('A4', 'C15'), ('A5', 'C4'), ('A5', 'C2', 'C2'),
    ('S5', 'C2'), ('SL25', 'C2'), ('PGL25', 'C2'), ('PSL27', 'C2'), ('ASL23',),
    ('S4', 'C8'), ('S4', 'C10'), ('S4', 'C12'), ('S4', 'C14'), ('A4', 'C20'),
    ('A4', 'C25'), ('SL23', 'C8'), ('SL23', 'C10'), ('SL23', 'C12'), ('SL23', 'C14'),
    ('GL23', 'C4'), ('GL23', 'C5'), ('GL23', 'C6'), ('GL23', 'C7'), ('PGL27',), ('SL27',),
]

_BASE_CACHE = {}


def _spec_order(spec):
    """Order of the direct product described by spec."""
    n = 1
    for name in spec:
        n *= int(name[1:]) if name.startswith('C') else _ORDER[name]
    return n


def _base_table(name):
    """(N, T, invs) for a named factor, cached; None if unavailable."""
    if name.startswith('C'):
        c = int(name[1:])
        T = [[(a + b) % c for b in range(c)] for a in range(c)]
        return c, T, [(-a) % c for a in range(c)]
    if name not in _BASE_CACHE:
        _BASE_CACHE[name] = _BASE_BUILDERS[name]()
    return _BASE_CACHE[name]


def _product(A, B):
    """Direct product of two group tables; element (i, j) has index i*N2 + j."""
    N1, T1, _ = A
    N2, T2, _ = B
    N = N1 * N2
    T = [[0] * N for _ in range(N)]
    for i1 in range(N1):
        R1 = T1[i1]
        for j1 in range(N2):
            row = T[i1 * N2 + j1]
            R2 = T2[j1]
            for i2 in range(N1):
                base = R1[i2] * N2
                for j2 in range(N2):
                    row[i2 * N2 + j2] = base + R2[j2]
    invs = [row.index(0) for row in T]
    return N, T, invs


def _build_spec(spec):
    """Group table (N, T, invs) for a product spec, or None if a factor is unavailable."""
    tab = None
    for name in spec:
        f = _base_table(name)
        if f is None:
            return None
        tab = f if tab is None else _product(tab, f)
    return tab


def _search_group(N, T, invs, d, D, rng, deadline, restart_iters=400):
    """Hill-climb with restarts over connection sets S (identity in S) until found or deadline."""
    while time.monotonic() < deadline:
        S = [0] + rng.sample(range(1, N), d - 1)
        cur = _unreached(N, T, invs, S, D)
        for _ in range(restart_iters):
            if cur == 0 or time.monotonic() > deadline:
                break
            i = rng.randrange(1, d)
            c = rng.randrange(1, N)
            if c in S:
                continue
            S2 = S[:]
            S2[i] = c
            v = _unreached(N, T, invs, S2, D)
            if v <= cur:
                S, cur = S2, v
        if cur == 0:
            return S
    return None


def _exotic_search(d, D, cur_n, moore, deadline, rng):
    """Round-robin bi-Cayley searches over exotic groups; returns the best valid (n, edges) found or None."""
    specs = []
    for spec in EXOTIC_SPECS:
        N = _spec_order(spec)
        if cur_n < 2 * N <= moore:
            specs.append((N, spec))
    specs.sort()
    found = None
    while specs and time.monotonic() < deadline:
        for item in list(specs):
            if time.monotonic() >= deadline:
                break
            N, spec = item
            if 2 * N <= cur_n:
                specs.remove(item)
                continue
            tab = _build_spec(spec)
            if tab is None:
                specs.remove(item)
                continue
            _, T, invs = tab
            end = min(deadline, time.monotonic() + SLICE)
            S = _search_group(N, T, invs, d, D, rng, end)
            if S is not None:
                edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                if lib.is_valid(2 * N, edges, d, D):
                    found = (2 * N, edges)
                    cur_n = 2 * N
                    specs.remove(item)
    return found


# ----------------------------------------------------------------------------
# General multi-base voltage lifts over semidirect products, annealed.
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
    T = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)

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

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best  # K_{d,d} meets the Moore bound 2d for D = 2

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
                n2, e2 = _grow(pg[0], pg[1], d, D, start + 0.15 * budget, rng)
                consider(n2, e2)
        if best[0] < moore:
            for n_c, e_c in _arc_extensions(d, start + 0.3 * budget,
                                            random.Random(seed * 7919 + d)):
                consider(n_c, e_c)

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if best[0] < moore:
                n2, e2 = _grow(gq[0], gq[1], d, D, start + 0.2 * budget, rng)
                consider(n2, e2)

    # Target-focused search for D = 5: exotic-group bi-Cayley lifts get most of the budget.
    if D == 5 and d >= 3 and best[0] < moore:
        res = _exotic_search(d, D, best[0], moore, start + 0.75 * budget, rng)
        if res is not None:
            consider(res[0], res[1])

    # Main search: aim above the current best order.
    ks = (2, 3)
    sweep_next = None   # next bi-Cayley order to try; sweeps upward from the lower bound
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]

        if rng.random() < 0.6:
            # Bi-Cayley lift on a semidirect group of order N; the lift has 2N vertices.
            lo = n_best // 2 + 1
            if lo > moore // 2:
                break
            if sweep_next is None or sweep_next < lo or sweep_next > lo + BAND_EXTRA:
                sweep_next = lo
            N = sweep_next
            sweep_next += 1
            groups = _groups(N)
            rng.shuffle(groups)
            found = None
            for m, k2, r in groups[:MAX_GROUPS]:
                if time.monotonic() > deadline:
                    break
                _, _, T, invs = _tables(m, k2, r)
                S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
                if S is not None:
                    found = (T, S)
                    break
            if found is not None:
                T, S = found
                edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                consider(2 * N, edges)
        else:
            # Multi-base lift with k base vertices per side over a group of order G.
            k = rng.choice(ks)
            lo = n_best // (2 * k) + 1
            if 2 * k * lo > moore:
                continue
            G = lo + rng.randrange(max(2, lo // 10))
            if G < 2:
                continue
            m, k2, r = rng.choice(_groups(G))
            order, mul, _ = lib.semidirect_group(m, k2, r)
            res = _anneal(d, D, k, order, mul, rng, deadline, ANNEAL_ITERS)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
