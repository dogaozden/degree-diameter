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
# Twin blow-up with a distance-2-free vertex set.
#
# If every vertex of a base graph G has degree d-1, replace some vertices v by
# two copies (v, v') that share the same neighbourhood. Each copy of u then has
# degree sum_{v in N(u)} m_v = (d-1) + |N(u) ∩ S| where S = {v : m_v = 2}. So S
# must have no two vertices with a common neighbour, i.e. the neighbourhoods of
# the chosen vertices must be pairwise disjoint. Blow-ups keep bipartiteness and
# diameter, so every such S gives a valid graph with n0 + |S| vertices.
#
# The two colour classes are independent subproblems (conflicts only join
# vertices on the same side). For W(q):
#   - a conflict-free subset of points is a partial ovoid;
#   - a conflict-free subset of lines is a partial spread.
# A full spread (q^2+1 lines, partitioning the points) always exists for W(q),
# while a local search on the line side tends to stall well below it.
#
# NEW in this version: for each side we first try an exact-cover search. A set
# whose neighbourhoods partition the other side is a perfect packing (a spread
# for lines, an ovoid for points), and it is the largest possible packing. The
# search is randomised DFS with minimum-remaining-values branching and restarts.
# If it fails within its small budget, we fall back to the iterated local search.
# ----------------------------------------------------------------------------

class _Abort(Exception):
    pass


def _exact_cover(side, adj, rng, deadline):
    """Randomised exact-cover search: chosen side vertices with neighbourhoods partitioning the other side.

    Returns the list of chosen vertices, or None if no perfect packing was found in time.
    """
    rows = {v: list(adj[v]) for v in side}
    cols0 = {}
    for v in side:
        for w in adj[v]:
            cols0.setdefault(w, set()).add(v)
    if not cols0:
        return []

    def dfs(colrows, chosen, budget):
        budget[0] += 1
        if budget[0] > budget[1] or time.monotonic() >= deadline:
            raise _Abort()
        if not colrows:
            return list(chosen)
        best_len = min(len(rs) for rs in colrows.values())
        if best_len == 0:
            return None
        mins = [c for c, rs in colrows.items() if len(rs) == best_len]
        c = mins[rng.randrange(len(mins))]
        cands = list(colrows[c])
        rng.shuffle(cands)
        for v in cands:
            removed = set()
            for w in rows[v]:
                removed |= colrows[w]
            new = {x: set(rs) for x, rs in colrows.items()}
            for u in removed:
                for x in rows[u]:
                    s = new.get(x)
                    if s is not None:
                        s.discard(u)
            for w in rows[v]:
                new.pop(w, None)
            res = dfs(new, chosen + [v], budget)
            if res is not None:
                return res
        return None

    while time.monotonic() < deadline:
        budget = [0, 4000]
        try:
            res = dfs(cols0, [], budget)
        except _Abort:
            continue
        if res is not None:
            return res
    return None


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
        if len(nbn[v]):
            cnt[nbn[v]] += 1
        inS[v] = True
        S.append(v)

    def remove(u):
        nonlocal conf
        conf -= int(cnt[u])
        if len(nbn[u]):
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


def _sides(n0, adj):
    """Two-colour the base graph (it is bipartite); return the two colour classes."""
    color = [-1] * n0
    for s in range(n0):
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
    classes = [[], []]
    for v in range(n0):
        classes[max(color[v], 0)].append(v)
    return classes


def _solve_side(side, nb, adj, rng, nprng, deadline):
    """Conflict-free subset of one colour class: exact cover first, then local search."""
    now = time.monotonic()
    exact_deadline = min(deadline, now + min(0.3 * max(0.0, deadline - now), 6.0))
    cover = _exact_cover(side, adj, rng, exact_deadline)
    if cover is not None:
        return cover
    loc = {v: i for i, v in enumerate(side)}
    lnb = [[loc[w] for w in nb[v] if w in loc] for v in side]
    sol = _independent_set(len(side), lnb, rng, nprng, deadline)
    return [side[i] for i in sol]


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
    """Twin blow-up of a base graph of degree d-1 by a large distance-2-free set."""
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
    nb = [sorted(s) for s in cs]
    if n0 <= 60:
        deadline = min(deadline, time.monotonic() + 2.0)

    sides = _sides(n0, adj)
    S = []
    now = time.monotonic()
    span = max(0.0, deadline - now)
    k = len(sides)
    for idx, side in enumerate(sides):
        if not side:
            continue
        sub_deadline = now + span * (idx + 1) / k
        S.extend(_solve_side(side, nb, adj, rng, nprng, sub_deadline))
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    # Use more of the budget than before; the final is_valid checks are cheap.
    deadline = start + max(0.5, 0.85 * time_limit - 4.0)
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

    if D == 2:
        return best

    pg = _pg(d)
    if pg is not None:
        consider(pg[0], pg[1])

    # Blow-up route: base of degree exactly d-1 with q = d-2 a prime power.
    q = d - 2
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < deadline - 2.0:
        if D >= 4:
            n0, e0 = _gq(q)
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
        else:
            n0, e0 = 0, []
        if n0 > 0:
            consider(n0, e0)
            res = _blowup(n0, e0, d, deadline, rng, nprng)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
