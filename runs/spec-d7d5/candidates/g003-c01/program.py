import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact constructions for D = 3 and D = 4 (unchanged from the parent).
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
# New construction family: Cayley-double (bipartite) graphs over NON-cyclic
# groups. A group G with d distinct generators s_1..s_d gives the bipartite graph
# on A_g, B_h (g, h in G) with A_g ~ B_{g*s} for each generator s.
# Degree is exactly d, and left multiplication is an automorphism, so only the
# two representatives A_e and B_e need to be checked for diameter.
#
# Groups used: PSL(2,p), PGL(2,p) (matrix groups, nonsolvable for p >= 5),
# and semidirect products Z_m x| Z_k (vectorised multiplication tables).
# Generators are found by simulated annealing against a bit-parallel cost:
# the number of (vertex, representative) pairs not within distance D.
# ----------------------------------------------------------------------------

def _psl_pgl(p, proj):
    """Multiplication table of PSL(2,p) or PGL(2,p) for prime p.

    Returns (order, MUL, identity_index) with MUL[i, j] = index of E_i * E_j.
    """
    mats = np.array(list(itertools.product(range(p), repeat=4)), dtype=np.int64)
    det = (mats[:, 0] * mats[:, 3] - mats[:, 1] * mats[:, 2]) % p
    M = mats[det == 1] if proj == "psl" else mats[det != 0]

    def enc(X):
        return ((X[..., 0] * p + X[..., 1]) * p + X[..., 2]) * p + X[..., 3]

    def canon(X):
        if proj == "psl":
            return np.minimum(enc(X), enc((-X) % p))
        res = None
        for lam in range(1, p):
            e = enc((lam * X) % p)
            res = e if res is None else np.minimum(res, e)
        return res

    keys = np.unique(canon(M))
    G = len(keys)
    x3 = keys % p
    r = keys // p
    x2 = r % p
    r = r // p
    x1 = r % p
    x0 = r // p
    E = np.stack([x0, x1, x2, x3], axis=1)
    lut = np.full(p ** 4, -1, dtype=np.int64)
    lut[keys] = np.arange(G)

    A = E[:, None, :]
    B = E[None, :, :]
    a1, b1, c1, d1 = A[..., 0], A[..., 1], A[..., 2], A[..., 3]
    a2, b2, c2, d2 = B[..., 0], B[..., 1], B[..., 2], B[..., 3]
    P = np.stack([
        (a1 * a2 + b1 * c2) % p,
        (a1 * b2 + b1 * d2) % p,
        (c1 * a2 + d1 * c2) % p,
        (c1 * b2 + d1 * d2) % p,
    ], axis=-1)
    MUL = lut[canon(P)]
    eidx = int(lut[int(canon(np.array([1, 0, 0, 1], dtype=np.int64)))])
    return G, MUL, eidx


def _sd_table(m, k, r):
    """Multiplication table of Z_m x| Z_k with (a, b) * (c, d) = (a + r^b c, b + d), coded a*k + b."""
    G = m * k
    x = np.arange(G)
    a = x // k
    b = x % k
    powers = np.array([pow(r, bb, m) for bb in range(k)], dtype=np.int64)
    A = (a[:, None] + powers[b][:, None] * a[None, :]) % m
    Bv = (b[:, None] + b[None, :]) % k
    MUL = (A * k + Bv).astype(np.int64)
    return G, MUL, 0


def _make_specs(hi, rng):
    """Candidate groups with order <= hi, sorted by order."""
    specs = []
    for p in (5, 7, 11, 13):
        specs.append(("psl", p))
        specs.append(("pgl", p))
    for order in range(2, hi + 1):
        divs = [k for k in range(1, min(order, 60) + 1) if order % k == 0]
        k = rng.choice(divs)
        m = order // k
        r = 1
        found = False
        if k > 1 and m >= 2:
            for _ in range(60):
                rr = rng.randrange(1, m)
                if math.gcd(rr, m) == 1 and pow(rr, k, m) == 1 % m:
                    r = rr
                    found = True
                    break
        if not found:
            k, m, r = 1, order, 1
        if m >= 1:
            specs.append(("sd", m, k, r))

    def order_of(s):
        return _spec_order(s)

    specs = [s for s in specs if _spec_order(s) <= hi]
    specs.sort(key=order_of)
    return specs


def _spec_order(spec):
    if spec[0] == "sd":
        return spec[1] * spec[2]
    p = spec[1]
    if spec[0] == "psl":
        return p * (p * p - 1) // 2
    return p * (p * p - 1)


def _build_group(spec):
    if spec[0] == "sd":
        return _sd_table(spec[1], spec[2], spec[3])
    return _psl_pgl(spec[1], spec[0])


_POP2 = np.array([0, 1, 1, 2], dtype=np.int64)


def _sa(d, D, G, MUL, INV, eidx, rng, deadline):
    """Simulated annealing over d distinct generators of a group of order G.

    Returns (n, edges) with diameter <= D, or None.
    """
    N = 2 * G
    S = rng.sample(range(G), min(d, G))
    if len(S) < d:
        return None
    nbr = np.empty((d, N), dtype=np.int64)

    def setrow(l, s):
        nbr[l, :G] = G + MUL[:, s]
        nbr[l, G:] = MUL[:, INV[s]]

    for l in range(d):
        setrow(l, S[l])

    def cost():
        reach = np.zeros(N, dtype=np.int64)
        reach[eidx] = 1
        reach[G + eidx] = 2
        for _ in range(D):
            new = reach.copy()
            for l in range(d):
                new |= reach[nbr[l]]
            if np.array_equal(new, reach):
                break
            reach = new
        return 4 * G - int(_POP2[reach].sum())

    c = cost()
    t0 = time.monotonic()
    total = max(1e-3, deadline - t0)
    while c > 0:
        now = time.monotonic()
        if now > deadline:
            break
        frac = (now - t0) / total
        l = rng.randrange(d)
        old = S[l]
        new = rng.randrange(G)
        if new in S:
            continue
        S[l] = new
        setrow(l, new)
        c2 = cost()
        temp = max(0.2, 3.0 * (1.0 - frac))
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
            c = c2
        else:
            S[l] = old
            setrow(l, old)

    if c != 0:
        return None
    edges = []
    for s in S:
        for g in range(G):
            edges.append((g, G + int(MUL[g, s])))
    return N, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
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

    # Main search: Cayley-double graphs over non-cyclic groups.
    hi = min(max(2, lib._moore_bound(d, D) // 2), 1500)
    specs = _make_specs(hi, rng)
    SLICE = 6.0

    while time.monotonic() < deadline - 0.5:
        for spec in specs:
            now = time.monotonic()
            if now >= deadline - 0.5:
                break
            best_G = best_n // 2
            order = _spec_order(spec)
            if order <= best_G or order > hi:
                continue
            try:
                G, MUL, eidx = _build_group(spec)
            except (ValueError, ZeroDivisionError):
                continue
            if G < d:
                continue
            INV = np.argmax(MUL == eidx, axis=1)
            slice_end = now + min(SLICE, deadline - now)
            res = _sa(d, D, G, MUL, INV, eidx, rng, slice_end)
            if res is not None:
                consider(res[0], res[1])
        if not specs:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
