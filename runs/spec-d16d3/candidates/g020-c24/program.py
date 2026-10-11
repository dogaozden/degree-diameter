import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generic helpers on adjacency lists.
# ----------------------------------------------------------------------------

def _to_adj(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _rm(adj, u, v):
    adj[u].remove(v)
    adj[v].remove(u)


def _add(adj, u, v):
    adj[u].append(v)
    adj[v].append(u)


def _count_bad(n, adj, D):
    """Unordered vertex pairs at distance > D (unreachable pairs included), via bitmask balls."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return sum(n - b.bit_count() for b in ball) // 2


def _accept(delta, T, rng):
    return delta <= 0 or rng.random() < math.exp(-delta / T)


# ----------------------------------------------------------------------------
# New base family: independent "load-capped" point and line sets on PG(2, q).
#
# Point-side star vertices A_P (for P in S) join the q+1 lines through P, and
# line-side vertices B_j (for j in T) join the q+1 points on j. Line L gains
# |S cap L| spare load and point Q gains #{j in T : Q on j}. With spare
# s = d - q - 1 the only requirement is that every line meets S in <= s points
# and every point lies on <= s lines of T. S and T are chosen independently,
# so the best choice is the best arc-like set per side (conic for odd prime q).
# Every A-B pair is at distance 3 and A-A, B-B pairs are at distance 2, so the
# diameter stays 3.
# ----------------------------------------------------------------------------

def _arc_base(q, d, deadline, rng):
    """(n, edges, color) for the load-capped PG(2,q) graph with spare s = d - q - 1, or None."""
    s = d - q - 1
    if s < 0:
        return None
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]   # lines through point P (indices)
    lp = [[] for _ in range(m)]   # points on line L (indices)
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)

    def loads_ok(S):
        cl = [0] * m
        cp = [0] * m
        for P in S:
            for L in pl[P]:
                cl[L] += 1
            for Q in lp[P]:
                cp[Q] += 1
        return max(cl) <= s and max(cp) <= s

    def greedy(trials):
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

    cands = [[]]
    if lib._prime_power(q)[1] == 1 and q > 2:
        index = {p: i for i, p in enumerate(pts)}
        conic = [index[(1, t, t * t % q)] for t in range(q)] + [index[(0, 0, 1)]]
        if loads_ok(conic):
            cands.append(conic)
    cands.append(greedy(30))
    S = max(cands, key=len)
    if not loads_ok(S):
        return None

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
    color = [0] * m + [1] * m + [0] * k + [1] * k
    return n, [(int(u), int(v)) for u, v in E], color


# ----------------------------------------------------------------------------
# New search: repair-grow by simulated annealing.
#
# To add one vertex X of colour c, attach it to d opposite-colour vertices
# with spare degree, then anneal over two move types until the whole graph has
# no pair at distance > D. Moves:
#   - swap one neighbour of X for another vertex with spare degree;
#   - rewire an edge (a, b) to (a, b2), which moves a unit of load between
#     vertices without touching a's degree.
# The cost is the number of bad pairs, so a rejected move is undone exactly.
# ----------------------------------------------------------------------------

def _try_add(n, adj, color, c, d, D, deadline, rng, iters):
    X = n
    N = n + 1
    cur = [list(a) for a in adj]
    cur.append([])
    col = list(color) + [c]
    cands = [v for v in range(n) if col[v] == 1 - c and len(cur[v]) < d]
    if not cands:
        return None
    rng.shuffle(cands)
    for y in cands[:d]:
        _add(cur, X, y)
    cost = _count_bad(N, cur, D)

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 1.5 * (0.02 ** (it / iters))
        if rng.random() < 0.5 and cur[X]:
            x = rng.choice(cur[X])
            pool = [v for v in range(n) if col[v] == 1 - c and len(cur[v]) < d and v not in cur[X]]
            if not pool:
                continue
            y = rng.choice(pool)
            _rm(cur, X, x)
            _add(cur, X, y)
            new = _count_bad(N, cur, D)
            if _accept(new - cost, T, rng):
                cost = new
            else:
                _rm(cur, X, y)
                _add(cur, X, x)
        else:
            a = rng.randrange(N)
            if not cur[a]:
                continue
            b = rng.choice(cur[a])
            pool = [v for v in range(N)
                    if col[v] != col[a] and v != b and len(cur[v]) < d and v not in cur[a]]
            if not pool:
                continue
            b2 = rng.choice(pool)
            _rm(cur, a, b)
            _add(cur, a, b2)
            new = _count_bad(N, cur, D)
            if _accept(new - cost, T, rng):
                cost = new
            else:
                _rm(cur, a, b2)
                _add(cur, a, b)

    if cost == 0:
        return N, cur, col
    return None


def _grow(n, adj, color, d, D, moore, deadline, rng):
    fails = 0
    while n < moore and fails < 4 and time.monotonic() < deadline:
        c = rng.randrange(2)
        res = _try_add(n, adj, color, c, d, D, deadline, rng, 400)
        if res is None:
            fails += 1
            continue
        n, adj, color = res
        fails = 0
    return n, adj, color


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D < 3:
        return best_n, best_e

    # Diameter-3 bases: PG(2,q) with spare-load arc extension, for every prime power q.
    base = None
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q) or time.monotonic() > start + 0.3 * time_limit:
            continue
        g = _arc_base(q, d, start + 0.3 * time_limit, rng)
        if g is None:
            continue
        if base is None or g[0] > base[0]:
            base = g

    if base is None:
        return best_n, best_e

    n, edges, color = base
    if not lib.is_valid(n, edges, d, D):
        return best_n, best_e
    if n > best_n:
        best_n, best_e = n, edges

    # Repair-grow: add vertices by annealing until the Moore bound or the deadline.
    moore = lib._moore_bound(d, D)
    adj = _to_adj(n, edges)
    n2, adj2, _ = _grow(n, adj, color, d, D, moore, start + 0.8 * time_limit, rng)
    if n2 > best_n:
        e2 = [(u, v) for u in range(n2) for v in adj2[u] if u < v]
        if lib.is_valid(n2, e2, d, D):
            return n2, e2
    return best_n, best_e
