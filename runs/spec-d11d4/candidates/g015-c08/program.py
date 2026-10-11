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
# NEW IDEA: two-sided twin blow-up.
#
# Blowing up a vertex set S (each v in S replaced by two twins with the same
# neighbourhood) keeps bipartiteness and diameter, and a base vertex u of degree
# d-1 stays within degree d iff at most one of its neighbours lies in S.
#
# Conflicts only join vertices on the SAME side of the bipartition. So S splits
# into an independent set on side 0 and one on side 1, and the two can be
# optimised separately:
#   * side 1 (lines of W(q)): a set of pairwise disjoint lines covering every
#     point exactly once is an exact cover. A depth-first exact-cover search
#     with a most-constrained-target rule finds a full spread of W(q), size q^2+1.
#   * side 0 (points of W(q)): a partial ovoid (pairwise non-collinear points),
#     found with iterated local search. For odd q no ovoid exists, so this
#     side is the bottleneck.
# The combined S is then blown up and checked with lib.is_valid.
# ----------------------------------------------------------------------------

class _Stop(Exception):
    pass


def _exact_cover(T, cov_of, covers, rng, budget, deadline):
    """Find candidates whose covers partition range(T); return candidate indices or None.

    covers[j]: targets covered by candidate j. cov_of[t]: candidates covering target t.
    """
    covered = [False] * T
    blk = [0] * len(covers)   # number of already covered targets inside covers[j]
    chosen = []
    nodes = [0]

    def setj(j, val):
        delta = 1 if val else -1
        for t in covers[j]:
            covered[t] = val
            for k in cov_of[t]:
                blk[k] += delta

    def dfs():
        nodes[0] += 1
        if nodes[0] > budget or time.monotonic() > deadline:
            raise _Stop()
        best = None
        for t in range(T):
            if covered[t]:
                continue
            o = [j for j in cov_of[t] if blk[j] == 0]
            if not o:
                return False
            if best is None or len(o) < len(best):
                best = o
                if len(o) == 1:
                    break
        if best is None:
            return True
        rng.shuffle(best)
        for j in best:
            setj(j, True)
            chosen.append(j)
            if dfs():
                return True
            chosen.pop()
            setj(j, False)
        return False

    try:
        ok = dfs()
    except _Stop:
        return None
    return list(chosen) if ok else None


def _independent_set(N, nb, rng, nprng, deadline):
    """Iterated local search for a large set of vertices with no conflicting pair."""
    if N == 0:
        return []
    nbn = [np.asarray(x, dtype=np.int64) for x in nb]
    cnt = np.zeros(N, dtype=np.int64)
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
        score = cnt + nprng.random(N)
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


def _two_colour(n0, adj):
    """Return the bipartition colour list, or None if the graph is not bipartite."""
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
                elif color[v] == color[u]:
                    return None
    return color


def _side_mis(n0, adj, color, side, rng, nprng, deadline):
    """Large set of vertices on `side` with no two sharing a neighbour."""
    members = [v for v in range(n0) if color[v] == side]
    idx = {v: i for i, v in enumerate(members)}
    conf = [set() for _ in members]
    for w in range(n0):
        if color[w] == side:
            continue
        a = adj[w]
        for i in range(len(a)):
            x = idx[a[i]]
            for j in range(i + 1, len(a)):
                y = idx[a[j]]
                conf[x].add(y)
                conf[y].add(x)
    loc = _independent_set(len(members), [sorted(s) for s in conf], rng, nprng, deadline)
    return [members[i] for i in loc]


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


def _blowup_two_sided(n0, edges0, d, try_cover, deadline, rng, nprng):
    """Twin blow-up of a (d-1)-regular bipartite base using an independent set on each side."""
    adj = [[] for _ in range(n0)]
    for u, v in edges0:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != d - 1 for a in adj):
        return None
    color = _two_colour(n0, adj)
    if color is None:
        return None

    now = time.monotonic()
    avail = deadline - now
    if avail <= 0:
        return None

    S = []
    spread = None
    targets = [v for v in range(n0) if color[v] == 0]
    covering = [v for v in range(n0) if color[v] == 1]
    if try_cover and len(targets) == len(covering):
        tidx = {v: i for i, v in enumerate(targets)}
        cidx = {v: j for j, v in enumerate(covering)}
        covers = [[tidx[w] for w in adj[c]] for c in covering]
        cov_of = [[cidx[w] for w in adj[t]] for t in targets]
        spread_deadline = time.monotonic() + 0.45 * avail
        while time.monotonic() < spread_deadline:
            res = _exact_cover(len(targets), cov_of, covers, rng, 1200, spread_deadline)
            if res is not None:
                spread = [covering[j] for j in res]
                break

    if spread is not None:
        S.extend(spread)
        S.extend(_side_mis(n0, adj, color, 0, rng, nprng, deadline))
    else:
        mid = time.monotonic() + 0.5 * (deadline - time.monotonic())
        S.extend(_side_mis(n0, adj, color, 1, rng, nprng, mid))
        S.extend(_side_mis(n0, adj, color, 0, rng, nprng, deadline))

    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 4.0)
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

    q = d - 2
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < deadline - 2.0:
        if D >= 4:
            n0, e0 = _gq(q)
            try_cover = True
        else:
            n0, e0 = lib.projective_plane_incidence(q)
            try_cover = False
        consider(n0, e0)
        res = _blowup_two_sided(n0, e0, d, try_cover, deadline, rng, nprng)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
