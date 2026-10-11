import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Symplectic generalized quadrangle W(q), built from the trace form on GF(q^2)^2.
#
# Points: K-points of K^4 = GF(q^2)^2 (K = GF(q)), i.e. nonzero (x1, x2) modulo K*.
# Lines: totally isotropic 2-spaces of B((x1,x2),(y1,y2)) = Tr(x1*y2 - x2*y1).
# The Desarguesian spread {(x, a*x)} (a in GF(q^2)) plus {(0, x)} partitions the
# points into q^2+1 pairwise-disjoint lines, which are t.i. for this form.
# ----------------------------------------------------------------------------

def _gq_model(q):
    """Return (P, lines, spread, colL): points 0..P-1, GQ lines as point lists, a line spread, collinearity matrix."""
    Q = q * q
    F = lib.GF(Q)
    mul = F.mul_table
    add = F.add_table
    neg = np.argmax(add == 0, axis=1).astype(np.int64)
    powq = np.array([F.pow(x, q) for x in range(Q)], dtype=np.int64)
    Kset = [x for x in range(Q) if int(powq[x]) == x]
    if len(Kset) != q:
        raise ValueError("subfield size mismatch")
    Kstar = [x for x in Kset if x != 0]
    mulL = mul.tolist()
    addL = add.tolist()

    # Canonical point index for every nonzero vector (x1, x2), coded as x1*Q + x2.
    idx_of = [-1] * (Q * Q)
    reps = []
    for code in range(1, Q * Q):
        if idx_of[code] != -1:
            continue
        x1, x2 = divmod(code, Q)
        k = len(reps)
        reps.append((x1, x2))
        for lam in Kstar:
            idx_of[mulL[lam][x1] * Q + mulL[lam][x2]] = k
    P = len(reps)

    # Collinearity: B(p, p') = 0 iff Tr(x1*y2 - x2*y1) = 0.
    X1 = np.array([r[0] for r in reps], dtype=np.int64)
    X2 = np.array([r[1] for r in reps], dtype=np.int64)
    A = mul[X1[:, None], X2[None, :]]
    Bm = mul[X2[:, None], X1[None, :]]
    om = add[A, neg[Bm]]
    tr = add[om, powq[om]]
    col = (tr == 0)
    np.fill_diagonal(col, False)
    colL = col.tolist()

    # All totally isotropic lines, each found from one collinear pair.
    lines = []
    covered = [[False] * P for _ in range(P)]
    for i in range(P):
        a1, a2 = reps[i]
        for j in range(i + 1, P):
            if not colL[i][j] or covered[i][j]:
                continue
            b1, b2 = reps[j]
            S = set()
            for al in Kset:
                ma1 = mulL[al][a1]
                ma2 = mulL[al][a2]
                for be in Kset:
                    if al == 0 and be == 0:
                        continue
                    v1 = addL[ma1][mulL[be][b1]]
                    v2 = addL[ma2][mulL[be][b2]]
                    S.add(idx_of[v1 * Q + v2])
            L = sorted(S)
            if len(L) != q + 1:
                raise ValueError("unexpected line size")
            lines.append(L)
            for p in L:
                row = covered[p]
                for r in L:
                    row[r] = True

    # Desarguesian line spread: {(x, a x)} for a in GF(q^2), and {(0, x)}.
    spread = []
    for a in range(Q):
        spread.append(sorted({idx_of[x * Q + mulL[a][x]] for x in range(1, Q)}))
    spread.append(sorted({idx_of[x] for x in range(1, Q)}))

    # Verify the spread: sizes, disjointness, full cover, pairwise collinearity inside each set.
    seen = set()
    for S in spread:
        if len(S) != q + 1 or seen.intersection(S):
            raise ValueError("bad spread")
        seen.update(S)
        for x in S:
            for y in S:
                if x != y and not colL[x][y]:
                    raise ValueError("spread line not isotropic")
    if len(seen) != P or len(spread) != q * q + 1:
        raise ValueError("spread does not cover")
    return P, lines, spread, colL


def _gq_incidence(q):
    """Incidence graph of W(q): (n, edges); degree q+1, diameter 4."""
    P, lines, _, _ = _gq_model(q)
    return P + len(lines), [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]


# ----------------------------------------------------------------------------
# Maximum independent set by k-fixed tabu search (pure Python).
# ----------------------------------------------------------------------------

def _mis(n, adj, deadline, rng):
    """Return a large independent set of the graph (n vertices, adj neighbour lists) found before deadline."""
    inS = [False] * n
    c = [0] * n
    S = []

    def add(v):
        inS[v] = True
        S.append(v)
        for w in adj[v]:
            c[w] += 1

    def remove(u):
        inS[u] = False
        S.remove(u)
        for w in adj[u]:
            c[w] -= 1

    order = list(range(n))
    rng.shuffle(order)
    for v in order:
        if c[v] == 0:
            add(v)
    best = list(S)
    tab_add = [0] * n
    tab_rem = [0] * n
    it = 0
    stuck = 0
    while time.monotonic() < deadline:
        it += 1
        cost = sum(c[v] for v in S)
        if cost == 0:
            if len(S) > len(best):
                best = list(S)
                stuck = 0
            cands = [v for v in range(n) if not inS[v] and tab_add[v] <= it] \
                or [v for v in range(n) if not inS[v]]
            if not cands:
                break
            mn = min(c[v] for v in cands)
            add(rng.choice([v for v in cands if c[v] == mn]))
            continue
        stuck += 1
        if stuck > 3000:
            for v in list(S):
                remove(v)
            for v in best:
                add(v)
            stuck = 0
            continue
        ok = [u for u in S if tab_rem[u] <= it] or list(S)
        mx = max(c[u] for u in ok)
        u = rng.choice([x for x in ok if c[x] == mx])
        remove(u)
        tab_add[u] = it + rng.randint(5, 15)
        cands = [v for v in range(n) if not inS[v] and tab_add[v] <= it] \
            or [v for v in range(n) if not inS[v]]
        mn = min(c[v] for v in cands)
        v = rng.choice([x for x in cands if c[x] == mn])
        add(v)
        tab_rem[v] = it + rng.randint(5, 15)
    return best


# ----------------------------------------------------------------------------
# NEW CONSTRUCTION: spread + partial ovoid augmentation of W(q), degree q+2.
#
# Each point has q+1 lines, so one spare slot. Each line has q+1 points, one spare slot.
#  - A-vertices: one per point p of an independent set I (pairwise non-collinear),
#    adjacent to the q+1 lines through p. Lines get at most one A-neighbour.
#  - B-vertices: one per line of a spread, adjacent to its q+1 points. Each point
#    gets exactly one B-neighbour.
# Distances: non-collinear points share q+1 common neighbours, so A-vertices are
# at distance 4 from each other; B-vertices at distance 4 from each other; mixed
# pairs and pairs with old vertices are within 4 by the GQ axioms. lib.is_valid
# still verifies every output.
# ----------------------------------------------------------------------------

def _spread_twin(q, deadline, rng):
    P, lines, spread, colL = _gq_model(q)
    Lc = len(lines)
    pl = [[] for _ in range(P)]
    for j, Ls in enumerate(lines):
        for p in Ls:
            pl[p].append(j)
    padj = [[r for r in range(P) if r != p and colL[p][r]] for p in range(P)]
    I = _mis(P, padj, deadline, rng)

    edges = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
    n = P + Lc
    for p in I:
        for j in pl[p]:
            edges.append((n, P + j))
        n += 1
    for S in spread:
        for r in S:
            edges.append((r, n))
        n += 1
    return n, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.75 * time_limit, time_limit - 12.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    # Projective plane incidence graph: degree d, diameter 3.
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    # Generalized quadrangle W(d-1): degree d, diameter 4.
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    # Spread + partial ovoid augmentation of W(d-2): degree d, diameter 4.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            consider(*_spread_twin(d - 2, deadline, rng))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
