import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy (bold change for the weakest target, d=16 D=3):
#
# 1. Base: arc-extended incidence graph of PG(2,q). Points 0..m-1, lines m..2m-1.
#    For a point set S with at most s = d-q-1 points on any line, add an A-vertex
#    per P in S (joined to the q+1 lines through P) and a B-vertex per j in S
#    (joined to the q+1 points on line j). Diameter 3, order 2(q^2+q+1)+2|S|.
#    For d=16 this is q=13, S = conic: 394 vertices.
#
# 2. Growth with repair (experimental): add one new A-vertex and one new B-vertex
#    to the base, saturate spare degree randomly, then run simulated annealing
#    over degree-preserving 2-switches (sides kept fixed, so bipartiteness is kept)
#    minimising the number of pairs at distance > D. If the cost reaches zero and
#    the graph passes lib.is_valid, keep it and grow again.
#
# 3. Safe fallback: K_{d,d} (diameter 2) is returned whenever nothing better
#    validates, so every case still returns a valid graph.
# ----------------------------------------------------------------------------


def _pg(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q); points 0..m-1, lines are indexed 0..m-1."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return m, edges, pl, lp


def _loads_ok(S, s, m, pl, lp):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy(m, s, pl, lp, rng, trials, deadline):
    """Randomized greedy point set S with all loads <= s; returns the largest found."""
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
            if all(cl[L] < s for L in pl[P]) and all(cp[Q] < s for Q in lp[P]):
                S.append(P)
                for L in pl[P]:
                    cl[L] += 1
                for Q in lp[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic(q):
    """Conic (plus nucleus for even q): an arc with no three collinear, as point indices."""
    F = lib.GF(q)
    index = {p: i for i, p in enumerate(lib.projective_points(q))}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_base(m, edges, pl, lp, S):
    """Extended incidence graph. Side 0 = points and A-vertices, side 1 = lines and B-vertices."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        E.extend((x, m + L) for L in pl[P])
    for t, j in enumerate(S):
        b = 2 * m + k + t
        E.extend((Q, b) for Q in lp[j])
    side = [0] * m + [1] * m + [0] * k + [1] * k
    return n, E, side


def _base(d, deadline, rng):
    """Best arc-extended PG(2,q) base over prime powers q with q+1 <= d; returns (n, edges, side) or None."""
    best = None
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 0:
            continue
        m, edges, pl, lp = _pg(q)
        cands = [[]]
        if s >= 2:
            cs = _conic(q)
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        if s >= 1:
            cands.append(_greedy(m, s, pl, lp, rng, 25, deadline))
        for S in cands:
            if not _loads_ok(S, s, m, pl, lp):
                continue
            n = 2 * m + 2 * len(S)
            if best is None or n > best[0]:
                best = _arc_base(m, edges, pl, lp, S)
    return best


# ----------------------------------------------------------------------------
# Growth with repair.
# ----------------------------------------------------------------------------

def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs included)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _attach(x, n, side, adj, d, rng):
    """Connect vertex x to up to d - deg(x) random opposite-side vertices with spare capacity."""
    opp = [v for v in range(n)
           if side[v] != side[x] and v != x and len(adj[v]) < d and v not in adj[x]]
    rng.shuffle(opp)
    for v in opp[:d - len(adj[x])]:
        adj[x].add(v)
        adj[v].add(x)


def _fill(n, side, adj, d, rng):
    """Greedily add random edges between spare-capacity vertices of opposite sides."""
    order = list(range(n))
    rng.shuffle(order)
    for x in order:
        if len(adj[x]) < d:
            _attach(x, n, side, adj, d, rng)


def _rm(adj, a, b):
    adj[a].discard(b)
    adj[b].discard(a)


def _add(adj, a, b):
    adj[a].add(b)
    adj[b].add(a)


def _anneal(n, side, adj, D, deadline, rng):
    """Degree-preserving 2-switch annealing until no pair is at distance > D. Returns True on success."""
    E = [(v, u) for v in range(n) if side[v] == 0 for u in adj[v]]
    if len(E) < 2:
        return False
    cost = _bad(n, adj, D)
    T = 1.0
    while cost > 0:
        if time.monotonic() > deadline:
            return False
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
        a, b = E[i]   # a side 0, b side 1
        c, e = E[j]   # c side 0, e side 1
        if e in adj[a] or b in adj[c]:
            continue
        _rm(adj, a, b)
        _rm(adj, c, e)
        _add(adj, a, e)
        _add(adj, c, b)
        new = _bad(n, adj, D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            _rm(adj, a, e)
            _rm(adj, c, b)
            _add(adj, a, b)
            _add(adj, c, e)
        T = max(0.3, T * 0.9995)
    return True


def _edges_from(n, adj):
    return [(v, u) for v in range(n) for u in adj[v] if v < u]


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + max(1.0, min(0.8 * time_limit, time_limit - 5.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    if D == 2 or d < 3:
        return fallback

    base = _base(d, deadline, rng)
    if base is None:
        return fallback
    n, E, side = base
    if not lib.is_valid(n, E, d, D):
        return fallback

    adj = [set() for _ in range(n)]
    for u, v in E:
        _add(adj, u, v)
    best = (n, E)

    # Grow by two vertices (one per side) and repair with annealing.
    while time.monotonic() < deadline:
        n2 = n + 2
        adj2 = [set(s) for s in adj] + [set(), set()]
        side2 = list(side) + [0, 1]
        _attach(n, n2, side2, adj2, d, rng)
        _attach(n + 1, n2, side2, adj2, d, rng)
        if not adj2[n] or not adj2[n + 1]:
            break
        _fill(n2, side2, adj2, d, rng)
        if not _anneal(n2, side2, adj2, D, deadline, rng):
            break
        E2 = _edges_from(n2, adj2)
        if not lib.is_valid(n2, E2, d, D):
            break
        n, side, adj = n2, side2, adj2
        best = (n, E2)

    bn, bE = best
    if lib.is_valid(bn, bE, d, D) and bn >= fallback[0]:
        return bn, bE
    return fallback
