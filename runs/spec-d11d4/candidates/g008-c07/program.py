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
    Returns (n, edges, P).
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
    return P + len(lines), edges, P


# ----------------------------------------------------------------------------
# Twin blow-up with a distance-2-free vertex set.
#
# If every vertex of a base graph G has degree d-1, replace some vertices v by
# two copies (v, v') that share the same neighbourhood. Each copy of u then has
# degree sum_{v in N(u)} m_v with m_v in {1, 2}; since |N(u)| = d-1 the degree
# stays <= d iff u has at most one neighbour in S = {v : m_v = 2}. So S must
# have no two vertices at distance 2. Blow-ups keep bipartiteness and diameter.
#
# Distance-2 conflicts only join vertices of the same side, so the conflict
# graph splits into a point part and a line part. Their independent sets can be
# chosen independently and unioned, so we search each side separately.
# ----------------------------------------------------------------------------

def _independent_set(N, nb, allowed, rng, nprng, deadline):
    """Iterated local search for a large conflict-free set among `allowed` vertices."""
    nbn = [np.asarray(x, dtype=np.int64) for x in nb]
    cnt = np.zeros(N, dtype=np.int64)     # number of chosen conflict-neighbours
    inS = np.zeros(N, dtype=bool)
    tabu = np.zeros(N, dtype=np.int64)
    blocked = ~allowed
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
        score[blocked] = np.inf
        score[tabu > it] = np.inf
        v = int(np.argmin(score))
        return v if np.isfinite(score[v]) else -1

    while True:
        it += 1
        if (it & 63) == 0 and time.monotonic() >= deadline:
            break
        if conf == 0:
            if len(S) > best_size:
                best = list(S)
                best_size = len(S)
                last_best_it = it
            v = pick()
            if v < 0:
                if (tabu > it).any():
                    tabu[:] = 0
                    continue
                break
            add(v)
        else:
            conflicting = [u for u in S if cnt[u] > 0]
            u = conflicting[rng.randrange(len(conflicting))]
            remove(u)
            tabu[u] = it + 5 + rng.randrange(8)
            v = pick()
            if v >= 0:
                add(v)
        if S and it - last_best_it > 15000:
            u = S[rng.randrange(len(S))]
            remove(u)
            tabu[u] = it + 5
            last_best_it = it
    if conf == 0 and len(S) > best_size:
        best = list(S)
    return best


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


def _blowup(n0, edges0, d, split, deadline, rng, nprng):
    """Twin blow-up of a base graph of degree d-1.

    Vertices 0..split-1 form one side and split..n0-1 the other; conflicts only
    occur within a side, so each side is searched separately with half of the
    remaining time each.
    """
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

    side_a = np.zeros(n0, dtype=bool)
    side_a[:split] = True
    side_b = ~side_a

    now = time.monotonic()
    mid = now + (deadline - now) / 2.0
    S_a = _independent_set(n0, nb, side_a, rng, nprng, mid)
    S_b = _independent_set(n0, nb, side_b, rng, nprng, deadline)
    return _blow(n0, edges0, S_a + S_b)


# ----------------------------------------------------------------------------
# New: slack-cover augmentation.
#
# Adding a vertex w never lengthens any existing path, so a new vertex only
# needs its own eccentricity <= D. It reaches every vertex x iff some neighbour
# c of w satisfies dist(c, x) <= D-1. So w is admissible exactly when the
# radius-(D-1) balls of its neighbours cover the whole graph. We pick w's
# neighbours greedily by coverage gain among vertices of the opposite side that
# still have spare degree, with randomised tie-breaking, and keep the vertex
# only if lib.is_valid confirms the result. Each accepted vertex uses up spare
# degree, so we repeat until the greedy cover fails a few times in a row.
# ----------------------------------------------------------------------------

def _two_colour(n, adj):
    """Return a proper 2-colouring of a bipartite adjacency structure, or None."""
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
                elif color[v] == color[u]:
                    return None
    return color


def _ball_masks(n, adj, R):
    """Bitmask of all vertices within distance R of each vertex."""
    reach = [1 << v for v in range(n)]
    for _ in range(R):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return reach


def _augment(n, edges, d, D, deadline, rng):
    """Greedily attach new vertices to spare-degree vertices while validity holds."""
    edges = list(edges)
    if D < 2 or n < 2:
        return n, edges
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _two_colour(n, adj)
    if color is None:
        return n, edges

    fails = 0
    while time.monotonic() < deadline and fails < 3:
        masks = _ball_masks(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        sides = [0, 1]
        rng.shuffle(sides)
        for s in sides:
            avail = set(v for v in range(n) if color[v] != s and len(adj[v]) < d)
            if not avail:
                continue
            cov = 0
            chosen = []
            for _ in range(d):
                best_c = -1
                best_key = -1.0
                for c in avail:
                    g = (masks[c] & ~cov).bit_count()
                    if g == 0:
                        continue
                    key = g + rng.random() * 0.5
                    if key > best_key:
                        best_key = key
                        best_c = c
                if best_c < 0:
                    break
                chosen.append(best_c)
                avail.discard(best_c)
                cov |= masks[best_c]
                if cov == full:
                    break
            if cov == full and chosen:
                new = n
                trial = edges + [(c, new) for c in chosen]
                if lib.is_valid(n + 1, trial, d, D):
                    edges = trial
                    for c in chosen:
                        adj[c].append(new)
                    adj.append(list(chosen))
                    color.append(s)
                    n += 1
                    added = True
                    break
        if added:
            fails = 0
        else:
            fails += 1
    return n, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.85 * time_limit - 2.0)
    # Leave roughly 30% of the search budget for the augmentation pass.
    t_blow = start + 0.7 * (deadline - start)
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
            n0, e0, split = _gq(q)
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
            split = n0 // 2
        else:
            n0, e0, split = 0, [], 0
        if n0 > 0:
            consider(n0, e0)
            res = _blowup(n0, e0, d, split, t_blow, rng, nprng)
            if res is not None:
                consider(res[0], res[1])

    # Augment the best valid graph found using spare degree.
    if lib.is_valid(best[0], best[1], d, D):
        try:
            aug_n, aug_e = _augment(best[0], best[1], d, D, deadline, rng)
            consider(aug_n, aug_e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
