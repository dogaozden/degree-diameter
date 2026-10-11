import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact algebraic families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# NEW: affine groups AGL(1, q) (x -> a x + b), optionally times Z_c.
#
# AGL(1, q) = F_q x| F_q^* is non-abelian and its translation subgroup is
# (Z_p)^k, which is generally NOT cyclic, so it is not covered by the
# Z_m x| Z_k semidirect products used elsewhere. Orders q(q-1)*c give
# many sizes that the cyclic/semidirect families miss.
# Element (a, b) with a != 0 is indexed (a-1)*q + b; identity is index 0.
# ----------------------------------------------------------------------------

def _affine_table(q, c=1):
    """Right-multiplication table MT (MT[g, s] = g*s) of AGL(1,q) x Z_c, order q(q-1)c."""
    F = lib.GF(q)
    G = q * (q - 1)
    idx = np.arange(G, dtype=np.int64)
    A = idx // q + 1
    B = idx % q
    # (a,b)*(c',d) = (a*c', a*d + b)
    MT = (F.mul_table[A[:, None], A[None, :]] - 1) * q + \
        F.add_table[F.mul_table[A[:, None], B[None, :]], B[:, None]]
    MT = MT.astype(np.int64)
    if c == 1:
        return MT
    M = G * c
    xs = np.arange(M, dtype=np.int64) // c
    zs = np.arange(M, dtype=np.int64) % c
    MT2 = MT[xs[:, None], xs[None, :]] * c + (zs[:, None] + zs[None, :]) % c
    return MT2


def _affine_candidates(lo):
    """Lift parameters (q, c, k, N) with lo < N <= 1.3*lo + 200, sorted by N."""
    out = []
    for q in range(3, 40):
        if not lib.is_prime_power(q):
            continue
        for c in (1, 2, 3):
            G0 = q * (q - 1) * c
            if G0 > 1400:
                continue
            for k in (1, 2, 3, 4):
                N = 2 * k * G0
                if lo < N <= 1.3 * lo + 200:
                    out.append((N, q, c, k))
    out.sort()
    return [(q, c, k, N) for N, q, c, k in out]


# ----------------------------------------------------------------------------
# Random d-regular bipartite graphs repaired by edge-switch annealing.
# Left vertices 0..n-1, right vertices n..2n-1.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP8 = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)


def _rr_base(N, W):
    base = np.zeros((N, W), dtype=np.uint64)
    v = np.arange(N, dtype=np.int64)
    base[v, v // 64] = np.uint64(1) << (v % 64).astype(np.uint64)
    return base


def _rr_cost(n, d, EB, D, N, base):
    E2 = EB.reshape(n, d)
    order = np.argsort(EB, kind="stable")
    nb = np.empty((N, d), dtype=np.int64)
    nb[:n] = n + E2
    nb[n:] = (order // d).reshape(n, d)
    R = base
    for _ in range(D):
        R = R | np.bitwise_or.reduce(R[nb], axis=1)
    reached = int(_POP8[R.view(np.uint8)].sum())
    srt = np.sort(E2, axis=1)
    dup = int(np.count_nonzero(srt[:, 1:] == srt[:, :-1]))
    return N * N - reached + _PENALTY * dup


def _rr_search(n, d, D, rng, deadline):
    N = 2 * n
    W = (N + 63) // 64
    base = _rr_base(N, W)
    perms = [rng.sample(range(n), n) for _ in range(d)]
    EB = np.array(perms, dtype=np.int64).T.copy().ravel()
    M = n * d
    cur = _rr_cost(n, d, EB, D, N, base)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cur != 0:
        now = time.monotonic()
        if now > deadline:
            break
        frac = (now - t0) / span
        temp = 8.0 * (0.03 ** frac) + 0.05
        e1 = rng.randrange(M)
        e2 = rng.randrange(M)
        if EB[e1] == EB[e2]:
            continue
        EB[e1], EB[e2] = EB[e2], EB[e1]
        c2 = _rr_cost(n, d, EB, D, N, base)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            cur = c2
        else:
            EB[e1], EB[e2] = EB[e2], EB[e1]
    if cur != 0:
        return None
    E2 = EB.reshape(n, d).tolist()
    edges = set()
    for i in range(n):
        for j in E2[i]:
            edges.add((i, n + j))
    return N, sorted(edges)


def _rr_arm(d, D, rng, deadline):
    moore = 2 * sum((d - 1) ** i for i in range(D))
    cap = 1500
    side = max(d + 1, min(cap, int(0.3 * moore / 2)))
    lo = None
    hi = None
    best = None
    while time.monotonic() < deadline - 0.5:
        now = time.monotonic()
        remaining = deadline - now
        slice_end = min(deadline, now + max(3.0, 0.3 * remaining))
        res = _rr_search(side, d, D, rng, slice_end)
        if res is not None:
            if best is None or res[0] > best[0]:
                best = res
            lo = side
            if side >= cap:
                break
            if hi is None:
                side = int(side * 1.06) + 1
            else:
                if hi - lo <= 1:
                    break
                side = (lo + hi) // 2
        else:
            hi = side
            if lo is None:
                side = int(side * 0.94)
            else:
                if hi - lo <= 1:
                    break
                side = (lo + hi) // 2
        side = min(max(side, d + 1), cap)
    return best


# ----------------------------------------------------------------------------
# Generic bi-Cayley lift search from a precomputed right-multiplication table.
# Vertices: A_{i,g} = i*G + g, B_{j,h} = (k+j)*G + h.
# Dart (layer l, base vertex i) with voltage s joins A_{i,g} to B_{p_l(i), g*s}.
# ----------------------------------------------------------------------------

def _table_search(d, D, k, MT, rng, deadline, iters):
    """Simulated annealing over voltages of a k-vertex-per-side base over the group with table MT."""
    G = MT.shape[0]
    N = 2 * k * G
    ar = np.arange(G, dtype=np.int64)
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nb = np.zeros((N, d), dtype=np.int64)

    def assign(l, i, s):
        j = layers[l][i]
        pm = MT[:, s]                       # g -> g*s, a permutation of the group
        nb[i * G:(i + 1) * G, l] = (k + j) * G + pm
        inv = np.empty(G, dtype=np.int64)
        inv[pm] = ar
        nb[(k + j) * G:(k + j + 1) * G, l] = i * G + inv

    for l in range(d):
        for i in range(k):
            assign(l, i, S[l][i])

    base = np.zeros(N, dtype=np.int64)
    for r in range(k):
        base[r * G] = 1 << r
    for j in range(k):
        base[(k + j) * G] = 1 << (k + j)
    nreps = 2 * k

    def dup_count():
        seen = set()
        dup = 0
        for l in range(d):
            for i in range(k):
                key = (i, layers[l][i], S[l][i])
                if key in seen:
                    dup += 1
                else:
                    seen.add(key)
        return dup

    def cost():
        reach = base
        for _ in range(D):
            reach = reach | np.bitwise_or.reduce(reach[nb], axis=1)
        reached = 0
        for r in range(nreps):
            reached += int(np.count_nonzero(reach & (1 << r)))
        return N * nreps - reached + _PENALTY * dup_count()

    cur = cost()
    for t in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        l = rng.randrange(d)
        i = rng.randrange(k)
        old_s = S[l][i]
        new_s = rng.randrange(G)
        assign(l, i, new_s)
        S[l][i] = new_s
        c2 = cost()
        temp = 2.0 * (1.0 - t / iters) + 0.05
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            cur = c2
        else:
            assign(l, i, old_s)
            S[l][i] = old_s

    if cur != 0:
        return None
    E = set()
    for x in range(N):
        for y in nb[x].tolist():
            if x != y:
                E.add((x, y) if x < y else (y, x))
    return N, sorted(E)


def _affine_arm(d, D, rng, deadline, lo):
    """Search lifts over AGL(1,q) x Z_c, targeting orders just above lo. Returns best (n, edges) or None."""
    found = None
    while time.monotonic() < deadline - 0.5:
        cands = _affine_candidates(lo)
        if not cands:
            break
        q, c, k, N = rng.choice(cands[:6])
        now = time.monotonic()
        remaining = deadline - now
        slice_end = min(deadline, now + max(2.0, 0.2 * remaining))
        MT = _affine_table(q, c)
        res = _table_search(d, D, k, MT, rng, slice_end, 6000)
        if res is not None:
            found = res
            lo = res[0]
    return found


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (previous arm).
# ----------------------------------------------------------------------------

def _groups_of_order(G, rng, limit=4):
    """Candidate semidirect products Z_m x| Z_k2 (as (m, k2, r)) with m*k2 = G."""
    out = []
    for k2 in range(1, min(G, 40) + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if not cands:
            continue
        rng.shuffle(cands)
        out += [(m, k2, r) for r in cands[:limit]]
    return out


def _search(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over the voltages of a base with k vertices per side (callable mul)."""
    N = 2 * k * G
    ar = np.arange(G, dtype=np.int64)
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nb = np.zeros((N, d), dtype=np.int64)

    def assign(l, i, s):
        j = layers[l][i]
        pm = np.fromiter((mul(g, s) for g in range(G)), dtype=np.int64, count=G)
        nb[i * G:(i + 1) * G, l] = (k + j) * G + pm
        inv = np.empty(G, dtype=np.int64)
        inv[pm] = ar
        nb[(k + j) * G:(k + j + 1) * G, l] = i * G + inv

    for l in range(d):
        for i in range(k):
            assign(l, i, S[l][i])

    base = np.zeros(N, dtype=np.int64)
    for r in range(k):
        base[r * G] = 1 << r
    for j in range(k):
        base[(k + j) * G] = 1 << (k + j)
    nreps = 2 * k

    def dup_count():
        seen = set()
        dup = 0
        for l in range(d):
            for i in range(k):
                key = (i, layers[l][i], S[l][i])
                if key in seen:
                    dup += 1
                else:
                    seen.add(key)
        return dup

    def cost():
        reach = base
        for _ in range(D):
            reach = reach | np.bitwise_or.reduce(reach[nb], axis=1)
        reached = 0
        for r in range(nreps):
            reached += int(np.count_nonzero(reach & (1 << r)))
        return N * nreps - reached + _PENALTY * dup_count()

    cur = cost()
    for t in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        l = rng.randrange(d)
        i = rng.randrange(k)
        old_s = S[l][i]
        new_s = rng.randrange(G)
        assign(l, i, new_s)
        S[l][i] = new_s
        c2 = cost()
        temp = 2.0 * (1.0 - t / iters) + 0.05
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            cur = c2
        else:
            assign(l, i, old_s)
            S[l][i] = old_s

    if cur != 0:
        return None
    E = set()
    for x in range(N):
        for y in nb[x].tolist():
            if x != y:
                E.add((x, y) if x < y else (y, x))
    return N, sorted(E)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions (calibration-style cases return immediately).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Arm 1: random regular bipartite graphs repaired by edge-switch annealing (small share).
    if D >= 3 and d >= 3 and time.monotonic() < deadline:
        rr_deadline = start + 0.1 * budget
        try:
            res = _rr_arm(d, D, rng, rr_deadline)
            if res is not None:
                consider(res[0], res[1])
        except Exception:
            pass

    # Arm 2 (new): lifts over AGL(1,q) x Z_c, the main search for large orders.
    if D >= 3 and time.monotonic() < deadline:
        aff_deadline = start + 0.75 * budget
        try:
            res = _affine_arm(d, D, rng, aff_deadline, best_n)
            if res is not None:
                consider(res[0], res[1])
        except Exception:
            pass

    # Arm 3: bi-Cayley lifts over semidirect products, sweeping orders near best_n.
    try:
        while time.monotonic() < deadline:
            now = time.monotonic()
            remaining = deadline - now
            k = rng.choice([1, 1, 2, 2, 3, 4])
            G0 = best_n // (2 * k) + 1
            G = G0 + rng.randrange(0, max(2, G0 // 12) + 1)
            cands = _groups_of_order(G, rng)
            if not cands:
                continue
            m, k2, r = rng.choice(cands)
            try:
                order, mul, _ = lib.semidirect_group(m, k2, r)
            except ValueError:
                continue
            slice_end = min(deadline, now + max(2.0, 0.25 * remaining))
            res = _search(d, D, k, order, mul, rng, slice_end, 4000)
            if res is not None:
                consider(res[0], res[1])
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
