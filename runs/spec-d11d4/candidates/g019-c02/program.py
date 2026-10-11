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
# Twin blow-up.
#
# If every vertex of a base graph G has degree d-1, replace a set S of base
# vertices by twin pairs (v, v') with the same neighbourhood. A neighbour u of
# v gains one degree per twin, so degree <= d iff |N(u) ∩ S| <= 1 for all u.
# Equivalently S has no two vertices at distance 2. Blow-ups keep bipartiteness
# and diameter, so every such S gives a valid graph with n0 + |S| vertices.
#
# NEW ROUTINE: side-split k-fixed tabu search.
# The distance-2 conflict graph of W(q) splits into a point part (collinearity)
# and a line part (concurrency), with no edges between them. Each part is
# searched separately by a k-fixed tabu search: keep exactly k vertices, minimise
# the number of conflicting pairs by swapping one chosen vertex for one unchosen
# vertex per step, and grow k whenever the conflict count reaches zero. This
# targets a partial spread of lines (up to q^2+1) and a partial ovoid of points
# (up to about q^2-q+1), which the union-level local search tends to miss.
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


def _kfixed_tabu(A, deadline, rng, nprng):
    """k-fixed tabu search for a large independent set of the graph with bool adjacency A.

    Returns the largest conflict-free set found (local indices).
    """
    N = A.shape[0]
    if N == 0:
        return []
    Ai = A.astype(np.int32)
    inS = np.zeros(N, dtype=bool)
    cnt = np.zeros(N, dtype=np.int32)
    tab_in = np.zeros(N, dtype=np.int64)
    tab_out = np.zeros(N, dtype=np.int64)
    chosen = []
    best = []
    # Initial greedy independent set, then pad to k0 = 1 by minimum conflicts.
    for v in nprng.permutation(N):
        if cnt[v] == 0:
            inS[v] = True
            cnt += Ai[v]
            chosen.append(int(v))
    it = 0
    while True:
        it += 1
        if (it & 15) == 0 and time.monotonic() >= deadline:
            break
        conf = int(cnt[inS].sum()) // 2
        if conf == 0:
            if len(chosen) > len(best):
                best = list(chosen)
            # Grow k: add the unchosen vertex with fewest conflicts.
            score = cnt.astype(np.float64) + nprng.random(N) * 0.5
            score[inS] = np.inf
            v = int(np.argmin(score))
            if not np.isfinite(score[v]):
                break
            inS[v] = True
            cnt += Ai[v]
            chosen.append(v)
            continue
        ch = np.array(chosen, dtype=np.int64)
        cu = cnt[ch].astype(np.float64) + nprng.random(len(ch)) * 0.5
        cu = np.where(tab_out[ch] > it, -np.inf, cu)
        u = int(ch[int(np.argmax(cu))])
        score = (cnt - Ai[u]).astype(np.float64) + nprng.random(N) * 0.5
        score[inS] = np.inf
        score[tab_in > it] = np.inf
        v = int(np.argmin(score))
        if not np.isfinite(score[v]):
            continue
        # Swap u out, v in.
        inS[u] = False
        cnt -= Ai[u]
        chosen.remove(u)
        inS[v] = True
        cnt += Ai[v]
        chosen.append(v)
        tab_in[u] = it + 7 + rng.randrange(10)
        tab_out[v] = it + 3 + rng.randrange(5)
    return best


def _two_color(n, adj):
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        st = [s]
        while st:
            u = st.pop()
            for w in adj[u]:
                if col[w] == -1:
                    col[w] = 1 - col[u]
                    st.append(w)
    return col


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
    """Return candidate distance-2-free sets S for the twin blow-up of a degree-(d-1) base."""
    adj = [[] for _ in range(n0)]
    for u, v in edges0:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != d - 1 for a in adj):
        return []
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

    candidates = []
    now = time.monotonic()
    total = max(0.5, deadline - now)

    # Baseline: union-level iterated local search on a short budget.
    S0 = _independent_set(n0, nb, rng, nprng, now + 0.1 * total)
    candidates.append(S0)

    # Side-split k-fixed tabu search on the two independent conflict classes.
    color = _two_color(n0, adj)
    now = time.monotonic()
    remaining = max(0.2, deadline - now)
    parts = []
    for side in (0, 1):
        verts = [v for v in range(n0) if color[v] == side]
        m = len(verts)
        if m == 0:
            continue
        loc = {v: i for i, v in enumerate(verts)}
        A = np.zeros((m, m), dtype=bool)
        for v in verts:
            for w in nb[v]:
                A[loc[v], loc[w]] = True
        share = 0.5 if side == 0 else 1.0
        sub_deadline = time.monotonic() + remaining * share
        res = _kfixed_tabu(A, sub_deadline, rng, nprng)
        parts.extend(verts[i] for i in res)
        remaining = max(0.2, deadline - time.monotonic())
    candidates.append(parts)

    return candidates


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.8 * time_limit - 3.0)
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
            for S in _blowup(n0, e0, d, deadline, rng, nprng):
                consider(*_blow(n0, e0, S))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
