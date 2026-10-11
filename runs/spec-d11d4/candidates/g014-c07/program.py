import itertools
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Projective plane (D = 3).
# ----------------------------------------------------------------------------

def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Symplectic generalized quadrangle W(q): points 0..P-1, lines as point lists.
# ----------------------------------------------------------------------------

def _gq_struct(q):
    """Return (P, lines): points of W(q) indexed 0..P-1 and each totally isotropic line as a sorted point list."""
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
            Lset = set()
            for a in range(q):
                ax = [M[a][x[k]] for k in range(4)]
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(A[ax[k]][M[b][y[k]]] for k in range(4))
                    if any(v):
                        Lset.add(index[norm(v)])
            Ls = sorted(Lset)
            lines.append(Ls)
            for p in Ls:
                cp = covered[p]
                for r in Ls:
                    cp[r] = 1
    return P, lines


def _gq_incidence(q):
    """Incidence graph of W(q): degree q+1, diameter 4."""
    P, lines = _gq_struct(q)
    return P + len(lines), [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]


def _incidence(P, lines):
    pl = [[] for _ in range(P)]
    for j, Ls in enumerate(lines):
        for p in Ls:
            pl[p].append(j)
    return pl


# ----------------------------------------------------------------------------
# Exact cover of the points by pairwise disjoint lines (a spread), DFS with MRV.
# ----------------------------------------------------------------------------

class _Timeout(Exception):
    pass


def _spread_exact(P, lines, pl, target, deadline, rng):
    """Return `target` pairwise disjoint lines covering all points, or None if not found in time."""
    L = len(lines)
    covered = [False] * P
    avail = [True] * L
    cnt = [len(pl[p]) for p in range(P)]   # available lines through each point
    chosen = []
    nodes = [0]

    def take(j):
        for p in lines[j]:
            covered[p] = True
        log = []
        for p in lines[j]:
            for m in pl[p]:
                if avail[m]:
                    avail[m] = False
                    log.append(m)
                    for r in lines[m]:
                        cnt[r] -= 1
        return log

    def undo(j, log):
        for m in reversed(log):
            avail[m] = True
            for r in lines[m]:
                cnt[r] += 1
        for p in lines[j]:
            covered[p] = False

    def dfs():
        if len(chosen) == target:
            return True
        nodes[0] += 1
        if (nodes[0] & 255) == 0 and time.monotonic() > deadline:
            raise _Timeout()
        bp, bc = -1, None
        for p in range(P):
            if not covered[p]:
                c = cnt[p]
                if c == 0:
                    return False
                if bc is None or c < bc:
                    bp, bc = p, c
                    if c == 1:
                        break
        cands = [m for m in pl[bp] if avail[m]]
        rng.shuffle(cands)
        for m in cands:
            log = take(m)
            chosen.append(m)
            if dfs():
                return True
            chosen.pop()
            undo(m, log)
        return False

    try:
        if dfs():
            return list(chosen)
    except _Timeout:
        pass
    return None


# ----------------------------------------------------------------------------
# Maximum independent set by tabu-guided local search (numpy).
# ----------------------------------------------------------------------------

def _mis(N, nb, rng, nprng, deadline):
    """Large set of vertices with no conflicting pair; nb[v] = conflict neighbours of v."""
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
    last_imp = 0

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
                last_imp = it
            v = pick()
            if v >= 0:
                add(v)
        else:
            conflicting = [u for u in S if cnt[u] > 0]
            u = conflicting[rng.randrange(len(conflicting))]
            remove(u)
            tabu[u] = it + 5 + rng.randrange(8)
            v = pick()
            if v >= 0:
                add(v)
        if S and it - last_imp > 15000:
            u = S[rng.randrange(len(S))]
            remove(u)
            tabu[u] = it + 5
            last_imp = it
    if conf == 0 and len(S) > best_size:
        best = list(S)
    return best


# ----------------------------------------------------------------------------
# Twin family on W(q), degree q+2, diameter 4 (for d = q+2, D = 4).
#
# Each vertex of W(q) has one spare degree slot. Adding a twin x' (same
# neighbourhood as x) keeps diameter. Twin points I must be pairwise
# non-collinear (partial ovoid); twin lines J must be pairwise disjoint
# (partial spread). J can be a full spread (q^2+1 lines, one per point).
# Then the graph has (q+1)(q^2+1)*2 + |J| + |I| vertices.
# ----------------------------------------------------------------------------

def _twin_family(q, deadline, rng, nprng):
    P, lines = _gq_struct(q)
    L = len(lines)
    pl = _incidence(P, lines)
    target = P // (q + 1)

    # Lines: try an exact spread first, otherwise a large partial spread.
    J = _spread_exact(P, lines, pl, target, min(deadline, time.monotonic() + 6.0), rng)
    if J is None:
        lconf = [set() for _ in range(L)]
        for p in range(P):
            for a in pl[p]:
                lconf[a].update(pl[p])
        for a in range(L):
            lconf[a].discard(a)
        now = time.monotonic()
        J = _mis(L, [sorted(s) for s in lconf], rng, nprng,
                 now + 0.3 * max(0.0, deadline - now))

    # Points: partial ovoid (pairwise non-collinear), the rest of the time.
    pconf = [set() for _ in range(P)]
    for Ls in lines:
        for p in Ls:
            pconf[p].update(Ls)
    for p in range(P):
        pconf[p].discard(p)
    I = _mis(P, [sorted(s) for s in pconf], rng, nprng, deadline)

    n = P + L
    edges = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
    for j in J:
        for p in lines[j]:
            edges.append((p, n))
        n += 1
    for p in I:
        for j in pl[p]:
            edges.append((n, P + j))
        n += 1
    return n, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = random.Random(seed)
    nprng = np.random.default_rng(abs(int(seed)) % (2 ** 32))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(res):
        nonlocal best, best_n
        if res is None:
            return
        n, e = res
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    try:
        consider(_pg(d))
    except Exception:
        pass
    if D == 3:
        return best

    # D >= 4: generalized quadrangle W(d-1) incidence, degree d.
    q = d - 1
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < deadline:
        try:
            consider(_gq_incidence(q))
        except Exception:
            pass

    # Twin family on W(d-2), degree d.
    q = d - 2
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < deadline - 2.0:
        try:
            consider(_twin_family(q, deadline, rng, nprng))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
