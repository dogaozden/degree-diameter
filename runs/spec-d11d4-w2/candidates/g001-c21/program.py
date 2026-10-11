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


def _gq_w(q):
    """Points and totally isotropic lines of the symplectic generalized quadrangle W(q).

    Returns (P, lines): points are 0..P-1, lines[j] is the sorted point list of line j.
    """
    F = lib.GF(q)
    mul = F.mul_table.tolist()
    add = F.add_table.tolist()
    neg = [next(b for b in range(q) if add[a][b] == 0) for a in range(q)]
    inv = [0] * q
    for a in range(1, q):
        inv[a] = next(b for b in range(1, q) if mul[a][b] == 1)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        ic = inv[c]
        return tuple(mul[ic][x] for x in v)

    def form(x, y):
        t = add[mul[x[0]][y[1]]][neg[mul[x[1]][y[0]]]]
        u = add[mul[x[2]][y[3]]][neg[mul[x[3]][y[2]]]]
        return add[t][u]

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i * P + j) in covered:
                continue
            y = pts[j]
            if form(x, y):
                continue
            Lset = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(add[mul[a][x[k]]][mul[b][y[k]]] for k in range(4))
                    if any(v):
                        Lset.add(index[norm(v)])
            Ls = sorted(Lset)
            lines.append(Ls)
            for p in Ls:
                for r in Ls:
                    if p < r:
                        covered.add(p * P + r)
    return P, lines


def _gq_incidence(q):
    """Incidence graph of W(q): (n, edges), points 0..P-1, lines P..P+L-1."""
    P, lines = _gq_w(q)
    L = len(lines)
    return P + L, [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]


# ----------------------------------------------------------------------------
# Independent-set searches.
# ----------------------------------------------------------------------------

def _spread_search(A_nb, B_to_A, nB, k, rng, deadline):
    """Largest family of A-vertices with pairwise disjoint neighbourhoods (k each).

    Randomized depth-first exact-cover style search, branching on the uncovered
    B-vertex with the fewest options, restarting on node caps.
    """
    nA = len(A_nb)
    blocked = [0] * nA
    covered = [False] * nB
    chosen = []
    best = []
    stop = [False]
    steps = [0]
    cap = [0]
    order = list(range(nB))

    def rec(U):
        if stop[0]:
            return
        steps[0] += 1
        if steps[0] > cap[0] or ((steps[0] & 15) == 0 and time.monotonic() >= deadline):
            stop[0] = True
            return
        if len(chosen) > len(best):
            best[:] = chosen
        if U == 0 or len(chosen) + U // k <= len(best):
            return
        pick = None
        for b in order:
            if covered[b]:
                continue
            o = [a for a in B_to_A[b] if blocked[a] == 0]
            if not o:
                return
            if pick is None or len(o) < len(pick):
                pick = o
        rng.shuffle(pick)
        for a in pick:
            chosen.append(a)
            for x in A_nb[a]:
                covered[x] = True
                for a2 in B_to_A[x]:
                    blocked[a2] += 1
            rec(U - k)
            for x in A_nb[a]:
                covered[x] = False
                for a2 in B_to_A[x]:
                    blocked[a2] -= 1
            chosen.pop()
            if stop[0]:
                return

    while time.monotonic() < deadline and len(best) * k < nB:
        rng.shuffle(order)
        stop[0] = False
        cap[0] = steps[0] + 600
        rec(nB)
    return list(best)


def _kfix(Ai, k, init, deadline, rng, nprng):
    """Tabu search for an independent set of size k in graph with int adjacency Ai.

    Returns (True, S) if conflict-free, else (False, best S found, possibly with conflicts).
    """
    n = Ai.shape[0]
    inS = np.zeros(n, dtype=bool)
    S = []
    for v in init:
        v = int(v)
        if not inS[v] and len(S) < k:
            inS[v] = True
            S.append(v)
    while len(S) < k:
        v = int(nprng.integers(n))
        if not inS[v]:
            inS[v] = True
            S.append(v)
    c = Ai[S].sum(axis=0).astype(np.int64)      # c[v] = number of S-neighbours of v
    conf = int(c[np.array(S)].sum()) // 2
    best_conf = conf
    best_S = list(S)
    tin = np.zeros(n, dtype=np.int64)
    tout = np.zeros(n, dtype=np.int64)
    it = 0
    while conf > 0:
        if (it & 31) == 0 and time.monotonic() >= deadline:
            break
        it += 1
        noise = nprng.random(n) * 0.9
        cand_out = inS & (tout <= it)
        if not cand_out.any():
            cand_out = inS
        u = int(np.argmax(np.where(cand_out, c + noise, -1e9)))
        cand_in = (~inS) & (tin <= it)
        if not cand_in.any():
            cand_in = ~inS
        v = int(np.argmin(np.where(cand_in, c - noise, 1e9)))
        conf += int(c[v]) - int(c[u]) - int(Ai[u, v])
        inS[u] = False
        c -= Ai[u]
        inS[v] = True
        c += Ai[v]
        tt = 7 + rng.randrange(10)
        tin[u] = it + tt
        tout[v] = it + tt
        if conf < best_conf:
            best_conf = conf
            best_S = np.flatnonzero(inS).tolist()
    if conf == 0:
        return True, np.flatnonzero(inS).tolist()
    return False, best_S


def _max_indep(A, deadline, rng, nprng):
    """Grow an independent set of a boolean adjacency matrix A until the deadline."""
    Ai = A.astype(np.int32)
    best = []
    k = 1
    while time.monotonic() < deadline and k <= A.shape[0]:
        ok, S = _kfix(Ai, k, best, deadline, rng, nprng)
        if not ok:
            break
        best = S
        k += 1
    return best


def _independent_part(A, S):
    """Greedy conflict-free subset of S under boolean adjacency A."""
    n = A.shape[0]
    blocked = np.zeros(n, dtype=bool)
    keep = []
    for v in S:
        v = int(v)
        if not blocked[v]:
            keep.append(v)
            blocked |= A[v]
    return keep


# ----------------------------------------------------------------------------
# Twin blow-up of W(q).
#
# Blowing up a set S into twins keeps all distances and raises each vertex's
# degree by the number of its S-neighbours. Base degree is q+1 = d-1, so we need
# |N(v) & S| <= 1 for all v. Point-side S must be a partial ovoid (no two
# collinear), line-side S must be a partial spread (no two concurrent). These
# two sides are independent (a point and a line never share a neighbour).
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


def _blow_w(q, deadline, rng, nprng):
    """Twin blow-up of W(q) (degree q+1), giving degree q+2 = d and diameter 4."""
    P, lines = _gq_w(q)
    L = len(lines)
    n0 = P + L
    edges0 = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]

    M = np.zeros((P, L), dtype=np.float32)
    for j, Ls in enumerate(lines):
        M[Ls, j] = 1.0
    A_pt = (M @ M.T) > 0.5      # collinear points
    A_ln = (M.T @ M) > 0.5      # concurrent lines
    np.fill_diagonal(A_pt, False)
    np.fill_diagonal(A_ln, False)
    pl = [[] for _ in range(P)]
    for j, Ls in enumerate(lines):
        for p in Ls:
            pl[p].append(j)

    target = q * q + 1          # spread size
    now = time.monotonic()
    total = max(0.0, deadline - now)

    # Line side: partial spread. Randomized exact-cover DFS first.
    spread = _spread_search(lines, pl, P, q + 1, rng, now + 0.3 * total)
    if len(spread) < target:
        ok, S = _kfix(A_ln.astype(np.int32), target, spread,
                      now + 0.4 * total, rng, nprng)
        cand = _independent_part(A_ln, S)
        if len(cand) > len(spread):
            spread = cand

    # Point side: partial ovoid, using the remaining time.
    ov = _max_indep(A_pt, deadline, rng, nprng)

    S_all = [P + j for j in spread] + [int(p) for p in ov]
    return _blow(n0, edges0, S_all)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + max(1.0, 0.8 * time_limit - 4.0)
    rng = random.Random(seed)
    nprng = np.random.default_rng(abs(int(seed)) % (2 ** 32))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    if D == 2:
        return best

    if D >= 3:
        pg = _pg(d)
        if pg is not None:
            consider(*pg)

    if D >= 4:
        # W(d-1) directly: degree d, diameter 4.
        if 2 <= d - 1 <= 11 and lib.is_prime_power(d - 1):
            try:
                consider(*_gq_incidence(d - 1))
            except Exception:
                pass

        # Twin blow-up of W(d-2): degree d-1 base, spare slot used by twins.
        q = d - 2
        if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < deadline - 2.0:
            try:
                consider(*_blow_w(q, deadline, rng, nprng))
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
