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
# Twin blow-up with a distance-2-free vertex set (parent idea, kept).
# ----------------------------------------------------------------------------

def _independent_set(N, nb, rng, nprng, deadline):
    """Iterated local search for a large set of vertices with no conflicting pair."""
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


def _colour(n, adj):
    """Proper 2-colouring of a bipartite adjacency list (0/1 per vertex)."""
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _blow(n0, edges0, S, side0):
    """Blow up each vertex of S into two twin copies; return (n, edges, side)."""
    extra = {}
    for v in S:
        extra[v] = n0 + len(extra)
    side = list(side0) + [side0[v] for v in S]
    copies = [[v] + ([extra[v]] if v in extra else []) for v in range(n0)]
    edges = []
    for u, v in edges0:
        for a in copies[u]:
            for b in copies[v]:
                edges.append((a, b))
    return n0 + len(extra), edges, side


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
    S = _independent_set(n0, nb, rng, nprng, deadline)
    side0 = _colour(n0, adj)
    return _blow(n0, edges0, S, side0)


# ----------------------------------------------------------------------------
# NEW IDEA: distance-ball set-cover pendant extension.
#
# A new vertex x is attached to a set T of existing vertices, all on the
# opposite side, each with spare degree (< d). Then dist(x, w) <= D for every
# w iff the union of the radius-(D-1) balls of the members of T covers every
# vertex. Adding x never lengthens any old shortest path, so the diameter of
# the old graph is preserved, and bipartiteness is kept by side labels. So the
# only check needed is this cover test, which is a bitmask set-cover problem.
# Newly added vertices keep spare degree and become candidates themselves.
# We grow greedily, choosing the side whose cover is smallest.
# ----------------------------------------------------------------------------

def _masks(adj, n, r):
    """Bitmask of all vertices within distance r of each vertex."""
    reach = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            m = reach[v]
            for u in adj[v]:
                m |= reach[u]
            new.append(m)
        reach = new
    return reach


def _cover(masks, cands, full, d, rng):
    """Greedy set cover of all vertices by ball masks of candidates; None if it fails."""
    order = list(cands)
    rng.shuffle(order)
    cur = 0
    chosen = []
    while cur != full:
        if len(chosen) >= d:
            return None
        bestg = 0
        best = None
        for c in order:
            g = (masks[c] & ~cur).bit_count()
            if g > bestg:
                bestg = g
                best = c
        if best is None:
            return None
        chosen.append(best)
        cur |= masks[best]
    return chosen


def _extend(n, edges, side, d, D, deadline, rng):
    """Greedily add pendant vertices via ball set-covers; return (n, edges)."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    side = list(side)
    r = D - 1
    while time.monotonic() < deadline:
        masks = _masks(adj, n, r)
        full = (1 << n) - 1
        best_plan = None
        for s in (0, 1):
            # New vertex has side s, so its neighbours have side 1-s.
            cands = [v for v in range(n) if side[v] == 1 - s and len(adj[v]) < d]
            plan = _cover(masks, cands, full, d, rng)
            if plan is not None and (best_plan is None or len(plan) < len(best_plan[1])):
                best_plan = (s, plan)
        if best_plan is None:
            break
        s, T = best_plan
        x = n
        n += 1
        adj.append(set(T))
        side.append(s)
        for t in T:
            adj[t].add(x)
    out = [(u, v) for u in range(n) for v in adj[u] if u < v]
    return n, out


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    ils_deadline = start + max(0.5, 0.55 * time_limit)
    ext_deadline = start + max(1.0, 0.8 * time_limit - 4.0)
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
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < ils_deadline - 2.0:
        if D >= 4:
            n0, e0 = _gq(q)
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
        else:
            n0, e0 = 0, []
        if n0 > 0:
            consider(n0, e0)
            res = _blowup(n0, e0, d, ils_deadline, rng, nprng)
            if res is not None:
                nb_, eb_, sideb = res
                consider(nb_, eb_)
                ne, ee = _extend(nb_, eb_, sideb, d, D, ext_deadline, rng)
                consider(ne, ee)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
