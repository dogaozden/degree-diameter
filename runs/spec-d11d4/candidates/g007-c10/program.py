import itertools
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q): point-line incidence graph (points 0..P-1,
# lines P..P+L-1). Degree q+1, diameter 4.
# ----------------------------------------------------------------------------

def _gq(q):
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
            L = sorted(Lset)
            lines.append(L)
            for p in L:
                cp = covered[p]
                for r in L:
                    cp[r] = 1
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return P + len(lines), edges


# ----------------------------------------------------------------------------
# Conflict structure of a base graph: x and y conflict if they share a neighbour.
# ----------------------------------------------------------------------------

def _conflict_lists(n0, edges0):
    adj = [[] for _ in range(n0)]
    for u, v in edges0:
        adj[u].append(v)
        adj[v].append(u)
    cs = [set() for _ in range(n0)]
    for w in range(n0):
        a = adj[w]
        for i in range(len(a)):
            for j in range(i + 1, len(a)):
                cs[a[i]].add(a[j])
                cs[a[j]].add(a[i])
    return adj, [sorted(s) for s in cs]


# ----------------------------------------------------------------------------
# Iterated tabu local search for a large conflict-free set S.
# ----------------------------------------------------------------------------

def _mis(N, nb, rng, nprng, deadline):
    nbn = [np.asarray(x, dtype=np.int64) for x in nb]
    cnt = np.zeros(N, dtype=np.int64)     # number of chosen conflict-neighbours
    inS = np.zeros(N, dtype=bool)
    tabu = np.zeros(N, dtype=np.int64)
    S = []
    conf = 0
    best = []
    it = 0
    last = 0

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

    def pick(now):
        score = cnt + 0.5 * nprng.random(N)   # random tie-breaking
        score[inS] = np.inf
        score[tabu > now] = np.inf
        v = int(np.argmin(score))
        return None if score[v] == np.inf else v

    while True:
        it += 1
        if (it & 31) == 0 and time.monotonic() >= deadline:
            break
        if conf == 0:
            if len(S) > len(best):
                best = list(S)
                last = it
            v = pick(it)
            if v is not None:
                add(v)
        else:
            cf = [u for u in S if cnt[u] > 0]
            u = cf[rng.randrange(len(cf))]
            remove(u)
            tabu[u] = it + 7 + rng.randrange(10)
            v = pick(it)
            if v is not None:
                add(v)
        if it - last > 4000:
            # Perturbation: return to the best set and kick a little.
            for u in list(S):
                remove(u)
            for v in best:
                add(v)
            for _ in range(2):
                if S:
                    u = S[rng.randrange(len(S))]
                    remove(u)
                    tabu[u] = it + 10
            last = it
    if conf == 0 and len(S) > len(best):
        best = list(S)
    return best


# ----------------------------------------------------------------------------
# Twin blow-up. If every base vertex has degree d-1, copying a set S of vertices
# with no two sharing a neighbour keeps every degree <= d, bipartiteness and
# the diameter. For W(q), this adds points (partial ovoid) and lines (partial
# spread) together, since they never conflict across types.
# ----------------------------------------------------------------------------

def _blowup(n0, edges0, d, deadline, rng, nprng):
    adj, nb = _conflict_lists(n0, edges0)
    if any(len(a) != d - 1 for a in adj):
        return None
    if n0 <= 60:
        deadline = min(deadline, time.monotonic() + 2.0)
    S = _mis(n0, nb, rng, nprng, deadline)
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


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + max(1.0, 0.8 * time_limit - 5.0)
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

    # Projective plane (degree d, diameter 3) and GQ(d-1) (degree d, diameter 4).
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_gq(d - 1))
        except Exception:
            pass

    # Blow-up route: base of degree d-1 with q = d-2 a prime power.
    q = d - 2
    if 2 <= q <= 11 and lib.is_prime_power(q):
        base = None
        try:
            if D >= 4:
                base = _gq(q)
            elif D == 3:
                base = lib.projective_plane_incidence(q)
        except Exception:
            base = None
        if base is not None:
            consider(*base)
            try:
                res = _blowup(base[0], base[1], d, deadline, rng, nprng)
                if res is not None:
                    consider(*res)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
