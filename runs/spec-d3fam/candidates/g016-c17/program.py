import math
import random
import time

import lib

TIME_FRAC = 0.85      # fraction of time_limit used before returning
MARGIN = 2.0          # seconds kept in reserve
ITER = 600            # annealing steps per growth attempt
MAX_FAILS = 6         # failed growth attempts before resetting to the best base


# ---------------------------------------------------------------- graph helpers

def _two_colour(n, adj):
    """Proper 2-colouring of a bipartite graph given as adjacency sets/lists."""
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


def _balls_adj(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    reach = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        if new == reach:
            break
        reach = new
    return reach


def _bad_pairs(n, adj, D):
    """Number of unordered pairs at distance > D (unreachable pairs count)."""
    reach = _balls_adj(n, adj, D)
    return sum(n - r.bit_count() for r in reach) // 2


def _edges(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


# ---------------------------------------------------------------- arc extension (D = 3)

def _pg_lists(q):
    """Incidence graph of PG(2,q) plus point->line and line->point lists."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return m, edges, pl, lp


def _loads_ok(S, s, m, pl, lp):
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _conic(q):
    """Conic (plus nucleus for even q) as a point-index set, an arc with no three collinear."""
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_search(m, s, pl, lp, rng, deadline):
    """Find a point set S with every line holding <= s points of S and every point on <= s lines of S."""

    def fits(P, cl, cp):
        return (all(cl[L] < s for L in pl[P])
                and all(cp[Q] < s for Q in lp[P]))

    def add(P, cl, cp):
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1

    def rem(P, cl, cp):
        for L in pl[P]:
            cl[L] -= 1
        for Q in lp[P]:
            cp[Q] -= 1

    best = []
    order = list(range(m))
    for _ in range(20):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if fits(P, cl, cp):
                add(P, cl, cp)
                S.append(P)
        if len(S) > len(best):
            best = S

    # Plateau-walking 1-swap local search from the best greedy set.
    cl = [0] * m
    cp = [0] * m
    inS = [False] * m
    cur = list(best)
    for P in cur:
        add(P, cl, cp)
        inS[P] = True
    bestset = list(cur)
    for it in range(3000):
        if (it & 63) == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        if fits(P, cl, cp):
            add(P, cl, cp)
            inS[P] = True
            cur.append(P)
            if len(cur) > len(bestset):
                bestset = list(cur)
            continue
        if not cur:
            continue
        idx = rng.randrange(len(cur))
        R = cur[idx]
        rem(R, cl, cp)
        inS[R] = False
        if fits(P, cl, cp):
            add(P, cl, cp)
            inS[P] = True
            cur[idx] = P
        else:
            add(R, cl, cp)
            inS[R] = True
    return bestset


def _arc_graph(m, edges, pl, lp, S):
    """PG incidence plus one new A-vertex per point of S and one new B-vertex per line of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in pl[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in lp[j]:
            E.append((Q, b))
    return n, E


# ---------------------------------------------------------------- growth by annealed repair

def _pick_neighbours(n, adj, color, c, d, D, rng):
    """Choose d vertices of colour 1-c, greedily covering radius-(D-1) balls."""
    other = [v for v in range(n) if color[v] == 1 - c]
    if len(other) < d:
        return None
    balls = _balls_adj(n, adj, D - 1)
    full = (1 << n) - 1
    covered, chosen = 0, []
    cand = other[:]
    rng.shuffle(cand)
    while covered != full and len(chosen) < d and cand:
        best_u, best_g = -1, 0
        for u in cand:
            g = (balls[u] & ~covered).bit_count()
            if g > best_g:
                best_u, best_g = u, g
        if best_u < 0:
            break
        chosen.append(best_u)
        covered |= balls[best_u]
        cand.remove(best_u)
    chosen_set = set(chosen)
    rest = [v for v in other if v not in chosen_set]
    rng.shuffle(rest)
    chosen += rest[:d - len(chosen)]
    return chosen


def _swap(adj, side0, rng):
    """Degree-preserving double-edge swap that keeps bipartiteness. Returns undo info or None."""
    a1 = rng.choice(side0)
    if not adj[a1]:
        return None
    b1 = rng.choice(tuple(adj[a1]))
    a2 = rng.choice(side0)
    if a2 == a1 or not adj[a2]:
        return None
    b2 = rng.choice(tuple(adj[a2]))
    if b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
        return None
    adj[a1].remove(b1); adj[b1].remove(a1)
    adj[a2].remove(b2); adj[b2].remove(a2)
    adj[a1].add(b2); adj[b2].add(a1)
    adj[a2].add(b1); adj[b1].add(a2)
    return (a1, b1, a2, b2)


def _unswap(adj, mv):
    a1, b1, a2, b2 = mv
    adj[a1].remove(b2); adj[b2].remove(a1)
    adj[a2].remove(b1); adj[b1].remove(a2)
    adj[a1].add(b1); adj[b1].add(a1)
    adj[a2].add(b2); adj[b2].add(a2)


def _augment(n, adj, color, d, rng):
    """Add edges between deficient opposite-colour vertices. Never increases any distance."""
    d0 = [u for u in range(n) if color[u] == 0 and len(adj[u]) < d]
    d1 = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    if not d0 or not d1:
        return
    rng.shuffle(d0)
    for u in d0:
        if len(adj[u]) >= d:
            continue
        for v in d1:
            if len(adj[v]) < d and v not in adj[u]:
                adj[u].add(v)
                adj[v].add(u)
                if len(adj[u]) >= d:
                    break


def _attempt(n, adj, color, d, D, rng, deadline):
    """Add one vertex, then anneal swaps until the diameter bound holds. Returns (n, adj, color) or None."""
    adj = [set(s) for s in adj]
    color = list(color)
    c = rng.randrange(2)
    nb = _pick_neighbours(n, adj, color, c, d, D, rng)
    if nb is None:
        return None
    for u in nb:
        if len(adj[u]) >= d:
            w = rng.choice(tuple(adj[u]))
            adj[u].discard(w)
            adj[w].discard(u)
    x = n
    adj.append(set())
    color.append(c)
    n += 1
    for u in nb:
        adj[x].add(u)
        adj[u].add(x)

    side0 = [v for v in range(n) if color[v] == 0]
    cost = _bad_pairs(n, adj, D)
    for it in range(ITER):
        if cost == 0:
            break
        if time.monotonic() > deadline:
            return None
        mv = _swap(adj, side0, rng)
        if mv is None:
            continue
        new = _bad_pairs(n, adj, D)
        delta = new - cost
        temp = 1.5 * (1.0 - it / ITER) + 0.05
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cost = new
        else:
            _unswap(adj, mv)
    if cost != 0:
        return None
    _augment(n, adj, color, d, rng)
    return n, adj, color


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, TIME_FRAC * time_limit - MARGIN)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:                                  # cycle of length 2D: bipartite, diameter D
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:                                  # K_{d,d} is Moore-extremal for D = 2
        return lib.haar_graph(d, range(d))
    if D == 3 and lib.is_prime_power(d - 1):    # Moore-extremal projective plane
        return lib.projective_plane_incidence(d - 1)

    # Fallback: K_{d,d}, valid for any D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Starting candidates for D = 3.
    if D == 3:
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n2, e2 = lib.araujo_lopez_graph(d - 2)   # record construction, degree d
                consider(n2, e2)
            except Exception:
                pass

        q = d - 1
        while q >= 2 and not lib.is_prime_power(q):
            q -= 1
        if q >= 2:
            n2, e2 = lib.projective_plane_incidence(q)
            consider(n2, e2)

        # Arc-extended projective planes: spare degree s = d - q - 1 pays for extra A/B vertices.
        arc_deadline = start + 0.3 * (deadline - start)
        for q in range(2, min(d - 2, 23) + 1):
            if not lib.is_prime_power(q):
                continue
            if time.monotonic() > arc_deadline:
                break
            s = d - q - 1
            if s < 1:
                continue
            m, edges, pl, lp = _pg_lists(q)
            S = _arc_search(m, s, pl, lp, rng, arc_deadline)
            if s >= 2:
                cs = _conic(q)
                if _loads_ok(cs, s, m, pl, lp) and len(cs) > len(S):
                    S = cs
            if not S or not _loads_ok(S, s, m, pl, lp):
                continue
            consider(*_arc_graph(m, edges, pl, lp, S))

    # Growth: add vertices with annealed repair, starting from the best graph found so far.
    n0, e0 = best
    adj0 = [set() for _ in range(n0)]
    for u, v in e0:
        adj0[u].add(v)
        adj0[v].add(u)
    base = (n0, adj0, _two_colour(n0, adj0))
    cur = base
    fails = 0
    while time.monotonic() < deadline:
        res = _attempt(cur[0], cur[1], cur[2], d, D, rng, deadline)
        if res is None:
            fails += 1
            if fails >= MAX_FAILS:
                cur = base
                fails = 0
            continue
        fails = 0
        cur = res
        if cur[0] > best_n:
            consider(cur[0], _edges(cur[0], cur[1]))
            if best_n == cur[0]:
                base = cur

    if lib.is_valid(best[0], best[1], d, D):
        return best
    return lib.haar_graph(d, range(d))
