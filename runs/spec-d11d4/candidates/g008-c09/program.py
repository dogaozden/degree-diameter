import itertools
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bases (unchanged safe pipeline).
# ----------------------------------------------------------------------------

def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq(q):
    """Point-line incidence graph of the symplectic generalized quadrangle W(q)."""
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
    return P + len(lines), edges


# ----------------------------------------------------------------------------
# Twin blow-up of a degree-(d-1) base along a distance-2-free vertex set.
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
# NEW ROUTE: voltage lifts over Z_m of a small bipartite base with k vertices
# per side. Base multiplicities c[a][b] form a circulant with row/column sums d.
# A lift is bipartite and has degree d by construction. Voltages inside each
# (a, b) block are kept distinct so the lift is a simple graph. A hill climb on
# the number of pairs at distance > D searches for a diameter-D lift; m is
# increased while lifts remain valid.
# ----------------------------------------------------------------------------

def _lift_edges(k, volts, m):
    """Edges of the Z_m lift of the bipartite base: A-side a -> a*m+g, B-side b -> (k+b)*m+h."""
    edges = []
    for a in range(k):
        for b in range(k):
            for v in volts[a][b]:
                base_b = (k + b) * m
                for g in range(m):
                    edges.append((a * m + g, base_b + (g + v) % m))
    return 2 * k * m, edges


def _climb(k, cmat, m, D, deadline, rng):
    """Hill-climb voltages so that the lift has no pair at distance > D. Returns volts or None."""
    volts = [[rng.sample(range(m), cmat[a][b]) for b in range(k)] for a in range(k)]
    n, e = _lift_edges(k, volts, m)
    cur = lib.bad_pairs(n, e, D)
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        a = rng.randrange(k)
        b = rng.randrange(k)
        if cmat[a][b] == 0:
            continue
        i = rng.randrange(cmat[a][b])
        new = rng.randrange(m)
        if new in volts[a][b]:
            continue
        old = volts[a][b][i]
        volts[a][b][i] = new
        n2, e2 = _lift_edges(k, volts, m)
        bp = lib.bad_pairs(n2, e2, D)
        if bp <= cur or rng.random() < 0.02:
            cur = bp
        else:
            volts[a][b][i] = old
    return volts


def _lift_search(d, D, best_n, deadline, rng):
    """Search Z_m lifts of circulant bipartite bases with more than best_n vertices."""
    found = None
    cfgs = [3, 2]
    for idx, k in enumerate(cfgs):
        now = time.monotonic()
        if now >= deadline:
            break
        slot = deadline if idx == len(cfgs) - 1 else now + (deadline - now) / (len(cfgs) - idx)
        p = [d // k + (1 if i < d % k else 0) for i in range(k)]
        cmat = [[p[(b - a) % k] for b in range(k)] for a in range(k)]
        base_n = max(best_n, found[0] if found else 0)
        m = base_n // (2 * k) + 1
        while time.monotonic() < slot:
            volts = _climb(k, cmat, m, D, slot, rng)
            if volts is None:
                break
            n, e = _lift_edges(k, volts, m)
            if not lib.is_valid(n, e, d, D):
                break
            found = (n, e)
            m += 1
    return found


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    span = max(0.5, 0.75 * time_limit - 3.0)
    deadline = start + span
    blow_deadline = start + 0.4 * span
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

    # Bold route: voltage lifts of small bipartite bases, searched for the target.
    if D == 4 and d >= 8 and time.monotonic() < deadline - 1.0:
        res = _lift_search(d, D, best_n, deadline, rng)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
