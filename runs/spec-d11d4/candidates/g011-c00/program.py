import itertools
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (symplectic), as points and totally isotropic lines.
# ----------------------------------------------------------------------------

def _gq(q):
    """Return (P, lines): points 0..P-1 of W(q) and each totally isotropic line as a sorted point list."""
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
            Ls = set()
            for a in range(q):
                ax = [M[a][x[k]] for k in range(4)]
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(A[ax[k]][M[b][y[k]]] for k in range(4))
                    if any(v):
                        Ls.add(index[norm(v)])
            Ls = sorted(Ls)
            lines.append(Ls)
            for p in Ls:
                cp = covered[p]
                for r in Ls:
                    cp[r] = 1
    return P, lines


# ----------------------------------------------------------------------------
# Tabu search for a large independent set in a conflict graph.
# Keeps a set S, repeatedly swaps a conflicting member out for the best
# non-tabu outsider, and grows S whenever it becomes conflict-free.
# ----------------------------------------------------------------------------

def _tabu_mis(N, nbr, deadline, rng, nprng, target):
    """Return a large conflict-free subset of 0..N-1; nbr[v] are numpy arrays of conflicting vertices."""
    if N == 0:
        return []
    cnt = np.zeros(N, dtype=np.int64)
    inS = np.zeros(N, dtype=bool)
    tabu = np.zeros(N, dtype=np.int64)
    S = []

    def add(v):
        inS[v] = True
        S.append(v)
        cnt[nbr[v]] += 1

    def rem(u):
        inS[u] = False
        S.remove(u)
        cnt[nbr[u]] -= 1

    def free_score(it):
        score = cnt + nprng.random(N)
        score[inS] = np.inf
        score[tabu > it] = np.inf
        return score

    # Greedy start.
    while len(S) < N:
        score = cnt + nprng.random(N)
        score[inS] = np.inf
        v = int(np.argmin(score))
        if cnt[v] > 0:
            break
        add(v)

    best = list(S)
    it = 0
    last_imp = 0
    while time.monotonic() < deadline:
        it += 1
        Sarr = np.array(S, dtype=np.int64)
        cs = cnt[Sarr]
        if not cs.any():
            if len(S) > len(best):
                best = list(S)
                last_imp = it
            if len(best) >= target:
                break
            score = free_score(it)
            v = int(np.argmin(score))
            if np.isinf(score[v]):
                break
            add(v)
            continue
        ci = np.nonzero(cs)[0]
        u = int(Sarr[ci[rng.randrange(len(ci))]])
        rem(u)
        tabu[u] = it + 7 + rng.randrange(10)
        score = free_score(it)
        v = int(np.argmin(score))
        if np.isinf(score[v]):
            add(u)
            continue
        add(v)
        if it - last_imp > 30000:
            for _ in range(3):
                if S:
                    rem(S[rng.randrange(len(S))])
            last_imp = it
    return best


# ----------------------------------------------------------------------------
# Twin construction on W(q), degree q+2 (d = q+2, D = 4).
#   * a point twin v_p (p in I) adjacent to all lines through p; I pairwise
#     non-collinear, so each line gets at most one new neighbour;
#   * a line twin w_L (L in J) adjacent to all points of L; J pairwise disjoint,
#     so each point gets at most one new neighbour.
# I is a partial ovoid, J a partial spread; the spread target is q^2+1.
# ----------------------------------------------------------------------------

def _twin_graph(P, lines, pl, I, J):
    L = len(lines)
    edges = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
    n = P + L
    for p in I:
        for j in pl[p]:
            edges.append((n, P + j))
        n += 1
    for j in J:
        for p in lines[j]:
            edges.append((p, n))
        n += 1
    return n, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(2.0, min(0.7 * time_limit, time_limit - 12.0))
    deadline = t0 + budget
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

    # Projective plane incidence graph: degree d, diameter 3.
    if lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    # Generalized quadrangle W(d-1): degree d, diameter 4.
    q_full = d - 1
    if D >= 4 and lib.is_prime_power(q_full) and 2 <= q_full <= 11:
        try:
            P, lines = _gq(q_full)
            n = P + len(lines)
            edges = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
            consider(n, edges)
        except Exception:
            pass

    # Twin construction on W(q), q = d-2: degree d, diameter 4.
    q = d - 2
    if D >= 4 and 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < deadline - 3.0:
        try:
            P, lines = _gq(q)
            Lc = len(lines)
            pl = [[] for _ in range(P)]
            for j, Ls in enumerate(lines):
                for p in Ls:
                    pl[p].append(j)
            padj = [set() for _ in range(P)]
            for Ls in lines:
                for p in Ls:
                    for r in Ls:
                        if p != r:
                            padj[p].add(r)
            ladj = [set() for _ in range(Lc)]
            for p in range(P):
                for a in pl[p]:
                    for b in pl[p]:
                        if a != b:
                            ladj[a].add(b)
            pnbr = [np.array(sorted(s), dtype=np.int64) for s in padj]
            lnbr = [np.array(sorted(s), dtype=np.int64) for s in ladj]

            now = time.monotonic()
            remaining = max(0.0, deadline - now)
            # Spread on lines first (perfect value is q^2+1), then partial ovoid on points.
            J = _tabu_mis(Lc, lnbr, now + 0.4 * remaining, rng, nprng, q * q + 1)
            I = _tabu_mis(P, pnbr, deadline, rng, nprng, P)
            n, edges = _twin_graph(P, lines, pl, I, J)
            consider(n, edges)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
