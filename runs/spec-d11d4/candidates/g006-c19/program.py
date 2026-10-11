import itertools
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bases.
# ----------------------------------------------------------------------------

def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq(q):
    """Point-line incidence graph of the symplectic generalized quadrangle W(q).

    Points are 0..P-1, lines are P..P+L-1. Every point lies on q+1 lines, every
    line has q+1 points, and the incidence graph has diameter 4.
    """
    F = lib.GF(q)
    A = F.add_table.tolist()
    M = F.mul_table.tolist()
    NEG = [F.neg(a) for a in range(q)]
    INV = [0] + [F.inv(a) for a in range(1, q)]
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    P = len(pts)
    index = {v: i for i, v in enumerate(pts)}

    def norm(v):
        c = next(x for x in v if x)
        ic = INV[c]
        return tuple(M[ic][x] for x in v)

    covered = [bytearray(P) for _ in range(P)]
    lines = []
    for i in range(P):
        x = pts[i]
        ci = covered[i]
        for j in range(i + 1, P):
            if ci[j]:
                continue
            y = pts[j]
            # Symplectic form x0*y1 - x1*y0 + x2*y3 - x3*y2.
            t = A[M[x[0]][y[1]]][NEG[M[x[1]][y[0]]]]
            s = A[M[x[2]][y[3]]][NEG[M[x[3]][y[2]]]]
            if A[t][s] != 0:
                continue
            L = set()
            for a in range(q):
                ax = [M[a][x[k]] for k in range(4)]
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(A[ax[k]][M[b][y[k]]] for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                cp = covered[p]
                for r in L:
                    cp[r] = 1
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return P + len(lines), edges


# ----------------------------------------------------------------------------
# Twin blow-up with a distance-2-free vertex set, searched side by side.
#
# If every vertex of a base graph G has degree d-1, blow up some vertices v into
# two twin copies with the same neighbourhood. A copy of u then has degree
# sum_{v in N(u)} m_v, so u may have at most one blown-up neighbour. Blown-up
# vertices on the same side must therefore have no common neighbour. The two
# sides of a bipartite base are independent of each other, so the search can be
# done separately per side (for W(q): a partial ovoid on points and a partial
# spread on lines), with the time split between the sides.
# ----------------------------------------------------------------------------

def _independent_set(N, nb, rng, nprng, deadline):
    """Iterated local search for a large set of vertices with no conflicting pair."""
    if N == 0:
        return []
    nbn = [np.asarray(x, dtype=np.int64) for x in nb]
    cnt = np.zeros(N, dtype=np.int64)     # number of chosen conflict-neighbours
    inS = np.zeros(N, dtype=bool)
    tabu = np.zeros(N, dtype=np.int64)
    S = []
    conf = 0
    best = []
    best_size = 0
    it = 0
    last_best_it = 0

    def add(v):
        nonlocal conf
        conf += int(cnt[v])
        cnt[nbn[v]] += 1
        inS[v] = True
        S.append(v)

    def remove(u):
        nonlocal conf
        conf -= int(cnt[u])
        cnt[nbn[u]] -= 1
        inS[u] = False
        S.remove(u)

    def pick():
        score = cnt + nprng.random(N)     # random tie-breaking
        score[inS] = np.inf
        score[tabu > it] = np.inf
        return int(np.argmin(score))

    while True:
        it += 1
        if (it & 63) == 0 and time.monotonic() >= deadline:
            break
        if conf == 0:
            if len(S) > best_size:
                best = list(S)
                best_size = len(S)
                last_best_it = it
            add(pick())
        else:
            conflicting = [u for u in S if cnt[u] > 0]
            u = conflicting[rng.randrange(len(conflicting))]
            remove(u)
            tabu[u] = it + 5 + rng.randrange(8)
            add(pick())
        if S and it - last_best_it > 15000:
            u = S[rng.randrange(len(S))]
            remove(u)
            tabu[u] = it + 5
            last_best_it = it
    if conf == 0 and len(S) > best_size:
        best = list(S)
    return best


def _side_search(V, cs, rng, nprng, deadline):
    """Large conflict-free subset of one side V, using local conflict lists cs."""
    idx = {v: i for i, v in enumerate(V)}
    nb_local = [[idx[w] for w in cs[v] if w in idx] for v in V]
    res = _independent_set(len(V), nb_local, rng, nprng, deadline)
    return [V[i] for i in res]


def _two_colour(n, edges):
    """Return a 0/1 colouring of a bipartite graph (vertices in each component start at 0)."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if color[y] == -1:
                    color[y] = 1 - color[x]
                    stack.append(y)
    return color


def _blow(n0, edges0, S):
    """Blow up each vertex of S into two twin copies (same neighbourhood)."""
    extra = {}
    for v in S:
        extra[v] = n0 + len(extra)
    copies = [[v] + ([extra[v]] if v in extra else []) for v in range(n0)]
    edges = []
    for u, v in edges0:
        for a in copies[u]:
            for b in copies[v]:
                edges.append((a, b))
    return n0 + len(extra), edges


def _blowup(n0, edges0, d, deadline, rng, nprng):
    """Twin blow-up of a base graph of degree d-1, searching each side separately."""
    adj = [[] for _ in range(n0)]
    for u, v in edges0:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != d - 1 for a in adj):
        return None
    cs = [set() for _ in range(n0)]
    for w in range(n0):
        a = adj[w]
        for i in range(len(a)):
            for j in range(i + 1, len(a)):
                x, y = a[i], a[j]
                cs[x].add(y)
                cs[y].add(x)
    if n0 <= 60:
        deadline = min(deadline, time.monotonic() + 2.0)
    color = _two_colour(n0, edges0)
    sides = [[v for v in range(n0) if color[v] == c] for c in (0, 1)]

    now = time.monotonic()
    total = max(0.0, deadline - now)
    S = []
    # Side 0 gets half of the remaining time, side 1 gets the rest.
    S += _side_search(sides[0], cs, rng, nprng, now + 0.5 * total)
    S += _side_search(sides[1], cs, rng, nprng, deadline)
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------
# Augmentation: attach new vertices to spare degree.
#
# Adding a vertex x adjacent to a set T can never increase any distance between
# old vertices. The distance from x to an old vertex v is 1 + min_t dist(t, v),
# so x satisfies the diameter bound iff every old vertex lies within distance
# D-1 of T. Each new vertex is checked exactly this way, so the graph stays
# valid at every step.
# ----------------------------------------------------------------------------

def _balls_adj(n, adj, R):
    """Bitmask of all vertices within distance R of each vertex (bit w = w reachable)."""
    reach = [1 << v for v in range(n)]
    for _ in range(R):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _greedy_cover(balls, cands, d, full, rng):
    """Randomised greedy set cover: pick <= d candidates whose balls cover `full`."""
    covered = 0
    chosen = []
    pool = list(cands)
    while len(chosen) < d and covered != full and pool:
        scored = []
        for t in pool:
            g = (balls[t] & ~covered).bit_count()
            if g > 0:
                scored.append((g, t))
        if not scored:
            break
        mx = max(g for g, _ in scored)
        if rng.random() < 0.6:
            thr = mx
        else:
            thr = mx - max(1, mx // 10)
        opts = [t for g, t in scored if g >= thr]
        t = rng.choice(opts)
        chosen.append(t)
        covered |= balls[t]
        pool.remove(t)
    if covered == full:
        return chosen
    return None


def _extend(n0, edges0, d, R, deadline, rng):
    """Greedily attach new vertices to vertices of spare degree while keeping diameter."""
    adj = [[] for _ in range(n0)]
    for u, v in edges0:
        adj[u].append(v)
        adj[v].append(u)
    color = list(_two_colour(n0, edges0))
    edges = list(edges0)
    fails = 0
    while time.monotonic() < deadline and fails < 40:
        N = len(adj)
        full = (1 << N) - 1
        balls = _balls_adj(N, adj, R)
        sides = [0, 1]
        rng.shuffle(sides)
        success = False
        for s in sides:
            cands = [t for t in range(N) if color[t] != s and len(adj[t]) < d]
            if not cands:
                continue
            chosen = None
            for _ in range(6):
                chosen = _greedy_cover(balls, cands, d, full, rng)
                if chosen is not None:
                    break
            if chosen is None:
                continue
            x = N
            adj.append([])
            color.append(s)
            for t in chosen:
                adj[t].append(x)
                adj[x].append(t)
                edges.append((t, x))
            success = True
            break
        if success:
            fails = 0
        else:
            fails += 1
    return len(adj), edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    parent_deadline = start + max(0.5, 0.7 * time_limit - 3.0)
    final_deadline = start + max(0.8, 0.8 * time_limit - 4.0)
    rng = random.Random(seed)
    nprng = np.random.default_rng(abs(int(seed)) % (2 ** 32))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    try:
        pg = _pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

        # Blow-up route: base of degree exactly d-1 with q = d-2 a prime power.
        q = d - 2
        if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < parent_deadline - 2.0:
            if D >= 4:
                n0, e0 = _gq(q)
            elif D == 3:
                n0, e0 = lib.projective_plane_incidence(q)
            else:
                n0, e0 = 0, []
            if n0 > 0:
                consider(n0, e0)
                res = _blowup(n0, e0, d, parent_deadline, rng, nprng)
                if res is not None:
                    consider(res[0], res[1])
    except Exception:
        pass

    # Augmentation route: attach extra vertices to whatever spare degree remains.
    try:
        if d >= 2 and time.monotonic() < final_deadline:
            n2, e2 = _extend(best_n, best[1], d, D - 1, final_deadline, rng)
            consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
