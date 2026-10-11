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
# Twin blow-up with a distance-2-free vertex set (parent idea).
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
    S = _independent_set(n0, nb, rng, nprng, deadline)
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------
# NEW IDEA: greedy 2-hop domination insertion ("slack extension").
#
# A graph with a spare-degree budget can often take extra vertices. Adding a
# new vertex x on side s, joined to a set T of side-o vertices with spare degree,
# keeps the graph valid iff x is within distance D of everything. Adding x only
# creates new paths, so the old pairs stay within D, and only x's eccentricity
# needs checking.
#
# For D >= 3, the side-o vertices are at distance <= 3 from x exactly when they
# are in T or share a side-s neighbour with some t in T. So we need T, |T| <= d,
# covering all side-o vertices in this 2-hop sense. This is a set-cover problem.
# Coverage sets are Python int bitmasks, and the greedy cover uses random
# tie-breaking, so repeated attempts explore different insertions.
# ----------------------------------------------------------------------------

def _ecc_ok(adj, x, D, N):
    """True if every vertex of the N-vertex graph is within distance D of x."""
    seen = {x}
    frontier = [x]
    for _ in range(D):
        nxt = []
        for u in frontier:
            for v in adj[u]:
                if v not in seen:
                    seen.add(v)
                    nxt.append(v)
        frontier = nxt
        if len(seen) == N:
            return True
    return len(seen) == N


def _extend(n, edges, d, D, deadline, rng):
    """Greedily insert new vertices into spare degree; return (n, edges)."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    if any(len(a) > d for a in adj):
        return n, list(edges)
    side = [-1] * n
    for s0 in range(n):
        if side[s0] != -1:
            continue
        side[s0] = 0
        stack = [s0]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if side[v] == -1:
                    side[v] = 1 - side[u]
                    stack.append(v)
                elif side[v] == side[u]:
                    return n, list(edges)  # not bipartite: do nothing

    new_edges = []
    fails = 0
    while time.monotonic() < deadline and fails < 2000:
        s = rng.randrange(2)
        o = 1 - s
        side_o = [v for v in range(n) if side[v] == o]
        if not side_o:
            break
        pos = {v: i for i, v in enumerate(side_o)}
        elig = [t for t in side_o if len(adj[t]) < d]
        if not elig:
            fails += 1
            continue
        # mz[z]: bitmask of side-o neighbours of side-s vertex z.
        mz = {}
        for z in range(n):
            if side[z] == s and adj[z]:
                m = 0
                for y in adj[z]:
                    m |= 1 << pos[y]
                mz[z] = m
        cov = {}
        for t in elig:
            c = 1 << pos[t]
            for z in adj[t]:
                c |= mz[z]
            cov[t] = c
        uncovered = (1 << len(side_o)) - 1
        chosen = []
        cand = list(elig)
        while uncovered and len(chosen) < d and cand:
            bi = -1
            bkey = None
            for i, t in enumerate(cand):
                g = (cov[t] & uncovered).bit_count()
                if g == 0:
                    continue
                key = (g, rng.random())
                if bkey is None or key > bkey:
                    bkey = key
                    bi = i
            if bi < 0:
                break
            t = cand.pop(bi)
            chosen.append(t)
            uncovered &= ~cov[t]
        if uncovered or not chosen:
            fails += 1
            continue
        x = n
        adj.append(set(chosen))
        for t in chosen:
            adj[t].add(x)
        n += 1
        side.append(s)
        if _ecc_ok(adj, x, D, n):
            new_edges.extend((x, t) for t in chosen)
            fails = 0
        else:
            for t in chosen:
                adj[t].discard(x)
            adj.pop()
            n -= 1
            side.pop()
            fails += 1
    return n, list(edges) + new_edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    blow_deadline = start + max(0.3, 0.4 * T - 1.0)
    ext_deadline = start + max(0.5, 0.8 * T - 2.0)
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
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < blow_deadline - 2.0:
        if D >= 4:
            n0, e0 = _gq(q)
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
        else:
            n0, e0 = 0, []
        if n0 > 0:
            consider(n0, e0)
            res = _blowup(n0, e0, d, blow_deadline, rng, nprng)
            if res is not None:
                consider(res[0], res[1])

    # New step: spend the remaining budget inserting vertices into spare degree.
    if time.monotonic() < ext_deadline:
        n2, e2 = _extend(best_n, list(best[1]), d, D, ext_deadline, rng)
        if n2 > best_n:
            consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
