import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Baseline constructions.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


# ----------------------------------------------------------------------------
# New construction: bi-Cayley (voltage) lifts over finite groups.
#
# Base: k A-vertices and k B-vertices, with a d-regular bipartite multigraph
# given by sets S[i][j] of group elements (|S[i][j]| = c_ij, row and column sums d).
# Lift: vertices A(i,x) and B(j,y), x,y in G; A(i,x) ~ B(j, x*g) for g in S[i][j].
# The lift is bipartite, d-regular, and G acts by left multiplication, so the
# diameter is at most D iff BFS from A(i,e) and B(j,e) reaches everything in D steps.
# Search: simulated annealing on the total number of unreached vertices.
# ----------------------------------------------------------------------------

def _groups(o, rng, limit):
    """Semidirect products Z_m x| Z_kk (m*kk = o), as (m, kk, r) triples; shuffled, capped."""
    cands = []
    for kk in range(1, o + 1):
        if o % kk:
            continue
        m = o // kk
        for r in range(m):
            if math.gcd(r, m) != 1:
                continue
            if pow(r, kk, m) != 1 % m:
                continue
            cands.append((m, kk, r))
    rng.shuffle(cands)
    return cands[:limit]


def _tables(m, kk, r):
    """Multiplication table (numpy) and inverse indices for the group (identity = 0)."""
    order, mul, _ = lib.semidirect_group(m, kk, r)
    M = np.array([[mul(x, y) for y in range(order)] for x in range(order)], dtype=np.int64)
    INV = [int(np.flatnonzero(M[g] == 0)[0]) for g in range(order)]
    return M, INV


def _adj(k, o, Mnp, INV, S, d):
    """Regular adjacency array (N, d) of the lift."""
    N = 2 * k * o
    A = np.empty((N, d), dtype=np.int64)
    for i in range(k):
        c = 0
        for j in range(k):
            for g in S[i][j]:
                A[i * o:(i + 1) * o, c] = (k + j) * o + Mnp[:, g]
                c += 1
    for j in range(k):
        c = 0
        for i in range(k):
            for g in S[i][j]:
                A[(k + j) * o:(k + j + 1) * o, c] = i * o + Mnp[:, INV[g]]
                c += 1
    return A


def _score(A, k, o, D):
    """Total number of vertices not within distance D of the orbit representatives."""
    N = A.shape[0]
    total = 0
    sources = [i * o for i in range(k)] + [(k + j) * o for j in range(k)]
    for s in sources:
        seen = np.zeros(N, dtype=bool)
        seen[s] = True
        fr = np.array([s], dtype=np.int64)
        for _ in range(D):
            nb = A[fr].ravel()
            nb = nb[~seen[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            seen[nb] = True
            fr = nb
        total += N - int(seen.sum())
    return total


def _search(k, o, Mnp, INV, d, D, deadline, rng):
    """Anneal the voltage sets until the lift has diameter <= D; return S or None."""
    while time.monotonic() < deadline:
        cnt = [[0] * k for _ in range(k)]
        for _ in range(d):
            p = list(range(k))
            rng.shuffle(p)
            for i in range(k):
                cnt[i][p[i]] += 1
        pl = [(i, j) for i in range(k) for j in range(k) if cnt[i][j]]
        S = [[rng.sample(range(o), cnt[i][j]) for j in range(k)] for i in range(k)]
        cur = _score(_adj(k, o, Mnp, INV, S, d), k, o, D)
        best_sc = cur
        stale = 0
        while cur > 0 and stale < 2000:
            if time.monotonic() >= deadline:
                return None
            i, j = rng.choice(pl)
            lst = S[i][j]
            t = rng.randrange(len(lst))
            old = lst[t]
            new = rng.randrange(o)
            while new in lst:
                new = rng.randrange(o)
            lst[t] = new
            sc = _score(_adj(k, o, Mnp, INV, S, d), k, o, D)
            if sc <= cur or rng.random() < math.exp(-(sc - cur) / 0.7):
                cur = sc
            else:
                lst[t] = old
            if cur < best_sc:
                best_sc = cur
                stale = 0
            else:
                stale += 1
        if cur == 0:
            return S
    return None


def _lift_edges(k, o, Mnp, S):
    edges = []
    for i in range(k):
        for j in range(k):
            for g in S[i][j]:
                src = i * o + np.arange(o, dtype=np.int64)
                dst = (k + j) * o + Mnp[:, g]
                edges.extend(zip(src.tolist(), dst.tolist()))
    return edges


def _lift_stage(best, d, D, moore, deadline, rng):
    """Try successively larger orders N with lifts of 2k*o vertices; keep every valid success."""
    lo = best[0] + 1
    hi = min(moore, lo + 80)
    for N in range(lo, hi + 1):
        if time.monotonic() >= deadline:
            break
        if N % 2:
            continue
        attempts = []
        for k in range(1, 7):
            if N % (2 * k):
                continue
            o = N // (2 * k)
            if d < o <= 400:
                attempts.append((k, o))
        rng.shuffle(attempts)
        for k, o in attempts[:4]:
            now = time.monotonic()
            if now >= deadline:
                break
            gs = _groups(o, rng, 3)
            if not gs:
                continue
            m, kk, r = rng.choice(gs)
            Mnp, INV = _tables(m, kk, r)
            end = min(deadline, now + 3.0)
            S = _search(k, o, Mnp, INV, d, D, end, rng)
            if S is None:
                continue
            edges = _lift_edges(k, o, Mnp, S)
            if lib.is_valid(N, edges, d, D):
                best = (N, edges)
                break
    return best


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5 * time_limit, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        cyc = [(i, (i + 1) % n) for i in range(n)]
        if lib.is_valid(n, cyc, d, D):
            return n, cyc
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = 2 * sum((d - 1) ** i for i in range(D))

    if D == 3:
        q = next(q for q in range(d - 1, 1, -1) if lib.is_prime_power(q))
        cand = lib.projective_plane_incidence(q)
        if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand
    elif D == 4:
        for q in range(min(d - 1, 9), 1, -1):
            if lib.is_prime_power(q):
                cand = _gq_w(q)
                if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
                    best = cand
                break

    if best[0] >= moore:
        return best

    best = _lift_stage(best, d, D, moore, deadline, rng)
    return best
