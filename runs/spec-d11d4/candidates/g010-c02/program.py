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

    Points are 0..P-1, lines are P..P+L-1. Returns (n, edges, P, lines) where
    lines[j] is the sorted point list of line j (vertex P + j).
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
    return P + len(lines), edges, P, lines


def _conflicts(n0, edges0):
    """Adjacency lists and, per vertex, the sorted list of vertices sharing a neighbour with it."""
    adj = [[] for _ in range(n0)]
    for u, v in edges0:
        adj[u].append(v)
        adj[v].append(u)
    cs = [set() for _ in range(n0)]
    for w in range(n0):
        a = adj[w]
        for i in range(len(a)):
            for j in range(i + 1, len(a)):
                x, y = a[i], a[j]
                cs[x].add(y)
                cs[y].add(x)
    return adj, [sorted(s) for s in cs]


# ----------------------------------------------------------------------------
# Exact-cover search for a spread of W(q) (pairwise disjoint lines).
# A spread is exactly a set of lines with no two sharing a point, so the
# line twins of a blow-up can be attached to all points with no conflicts.
# ----------------------------------------------------------------------------

def _spread(P, lines, deadline, rng):
    """Return indices of pairwise disjoint lines found by randomized MRV backtracking."""
    L = len(lines)
    lmask = [0] * L
    pl = [[] for _ in range(P)]
    for j, Ls in enumerate(lines):
        m = 0
        for p in Ls:
            m |= 1 << p
            pl[p].append(j)
        lmask[j] = m
    full = (1 << P) - 1
    best = []
    nodes = [0]
    limit = [0]

    def dfs(covered, chosen):
        nonlocal best
        if len(chosen) > len(best):
            best = list(chosen)
        if covered == full:
            return True
        nodes[0] += 1
        if nodes[0] > limit[0] or time.monotonic() > deadline:
            return False
        bc = None
        for p in range(P):
            if (covered >> p) & 1:
                continue
            cand = [j for j in pl[p] if not (lmask[j] & covered)]
            if bc is None or len(cand) < len(bc):
                bc = cand
                if len(cand) <= 1:
                    break
        if not bc:
            return False
        rng.shuffle(bc)
        for j in bc:
            chosen.append(j)
            if dfs(covered | lmask[j], chosen):
                return True
            chosen.pop()
        return False

    while time.monotonic() < deadline:
        nodes[0] = 0
        limit[0] = 400
        if dfs(0, []):
            break
    return best


# ----------------------------------------------------------------------------
# Maximum conflict-free set by iterated local search (numpy-vectorized).
# ----------------------------------------------------------------------------

def _independent_set(N, nb, allowed, rng, nprng, deadline):
    """Iterated local search for a large conflict-free set among `allowed` vertices."""
    nbn = [np.asarray(x, dtype=np.int64) for x in nb]
    cnt = np.zeros(N, dtype=np.int64)
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
        score = cnt + nprng.random(N)
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


# ----------------------------------------------------------------------------
# Twin blow-up: each vertex in S gets a twin with the same neighbourhood.
# Valid when the base is regular of degree d-1 and S has at most one
# neighbour per vertex on the opposite side (no conflicts within a side).
# ----------------------------------------------------------------------------

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


def _gq_route(q, deadline, rng, nprng):
    """Choose twin sets on W(q): a spread of lines (line side) and a partial ovoid (point side)."""
    n0, e0, P, lines = _gq(q)
    _, nb = _conflicts(n0, e0)
    side_p = np.zeros(n0, dtype=bool)
    side_p[:P] = True
    side_l = ~side_p
    t0 = time.monotonic()
    total = max(0.5, deadline - t0)

    J_idx = _spread(P, lines, t0 + 0.35 * total, rng)
    J = [P + j for j in J_idx]
    if len(J) < q * q + 1:
        Jl = _independent_set(n0, nb, side_l, rng, nprng, t0 + 0.5 * total)
        if len(Jl) > len(J):
            J = Jl
    I = _independent_set(n0, nb, side_p, rng, nprng, t0 + 0.8 * total)
    return n0, e0, list(I) + list(J)


def _pg_blowup(q, deadline, rng, nprng):
    """Twin blow-up of PG(2, q) (degree q+1), searched by local search on each side."""
    n0, e0 = lib.projective_plane_incidence(q)
    split = n0 // 2
    _, nb = _conflicts(n0, e0)
    side_a = np.zeros(n0, dtype=bool)
    side_a[:split] = True
    side_b = ~side_a
    now = time.monotonic()
    mid = now + (deadline - now) / 2.0
    S_a = _independent_set(n0, nb, side_a, rng, nprng, mid)
    S_b = _independent_set(n0, nb, side_b, rng, nprng, deadline)
    return _blow(n0, e0, S_a + S_b)


# ----------------------------------------------------------------------------
# Greedy set-cover vertex extension for diameter 4.
#
# A new vertex x on side X joined to a set S on the opposite side keeps
# diameter <= 4 exactly when the union of R3(s) over s in S covers all
# vertices. Adding x only shortens distances, so nothing else can break.
# ----------------------------------------------------------------------------

def _ball3(n, adj):
    """Return per-vertex bitmasks of all vertices within distance 3."""
    reach = [1 << v for v in range(n)]
    for _ in range(3):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _extend(n, edges, d, deadline, rng):
    """Greedily add vertices while keeping max degree d and diameter 4; return (n, edges)."""
    edges = list(edges)
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
            u = stack.pop()
            for w in adj[u]:
                if color[w] == -1:
                    color[w] = 1 - color[u]
                    stack.append(w)

    fails = 0
    while time.monotonic() < deadline and fails < 3000:
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        grown = False
        while time.monotonic() < deadline and fails < 3000:
            spare = [v for v in range(n) if len(adj[v]) < d]
            if not spare:
                return n, edges
            s0 = rng.choice(spare)
            pool = [v for v in spare if color[v] == color[s0] and v != s0]
            S = [s0]
            unc = full & ~reach[s0]
            while unc and len(S) < d and pool:
                best, bv = 0, -1
                for v in pool:
                    g = (reach[v] & unc).bit_count()
                    if g > best:
                        best, bv = g, v
                if bv < 0:
                    break
                S.append(bv)
                unc &= ~reach[bv]
                pool.remove(bv)
            if unc:
                fails += 1
                continue
            x = n
            n += 1
            for s in S:
                edges.append((s, x))
                adj[s].append(x)
            adj.append(list(S))
            color.append(1 - color[s0])
            fails = 0
            grown = True
            break
        if not grown:
            break
    return n, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.85 * time_limit - 2.0)
    rng = random.Random(seed)
    nprng = np.random.default_rng(abs(int(seed)) % (2 ** 32))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # Projective plane incidence (diameter 3).
    if D >= 3:
        pg = _pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    q = d - 2

    # D = 3: twin blow-up of PG(2, d-2).
    if D == 3 and 2 <= q <= 9 and lib.is_prime_power(q) and time.monotonic() < deadline - 2.0:
        try:
            n1, e1 = _pg_blowup(q, deadline, rng, nprng)
            consider(n1, e1)
        except Exception:
            pass

    if D >= 4:
        # W(d-1) incidence: degree d, diameter 4.
        if 2 <= d - 1 <= 9 and lib.is_prime_power(d - 1):
            try:
                consider(*_gq(d - 1)[:2])
            except Exception:
                pass

        # W(d-2): spread on the line side plus partial ovoid on the point side,
        # blown up to degree d, then greedy extension.
        if 2 <= q <= 9 and lib.is_prime_power(q) and time.monotonic() < deadline - 3.0:
            try:
                n0, e0, S = _gq_route(q, deadline, rng, nprng)
                consider(n0, e0)
                n1, e1 = _blow(n0, e0, S)
                consider(n1, e1)
                n2, e2 = _extend(n1, e1, d, deadline, rng)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
