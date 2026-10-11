import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (kept from the parent).
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
# Groups. Each group is (order G, mul) where mul(x, y) maps ints in 0..G-1 to
# ints in 0..G-1 and is associative. Left multiplication by any element is an
# automorphism of the lift, so one representative per part suffices.
# A spec is a hashable tuple describing a group.
# ----------------------------------------------------------------------------

def _agl(q):
    """Affine group x -> a x + b over GF(q), a != 0. Order q(q-1)."""
    F = lib.GF(q)

    def mul(x, y):
        a, b = x // q + 1, x % q
        c, d = y // q + 1, y % q
        return (F.mul(a, c) - 1) * q + F.add(F.mul(a, d), b)

    return q * (q - 1), mul


def _heis(p):
    """Heisenberg group of order p^3 (p prime)."""
    pp = p * p

    def mul(x, y):
        a, rest = divmod(x, pp)
        b, c = divmod(rest, p)
        a2, rest2 = divmod(y, pp)
        b2, c2 = divmod(rest2, p)
        return ((a + a2) % p) * pp + ((b + b2) % p) * p + (c + c2 + a * b2) % p

    return p ** 3, mul


def _abelian(mods):
    """Abelian group Z_m1 x Z_m2 x ... (non-cyclic allowed)."""
    G = math.prod(mods)

    def dec(x):
        out = []
        for m in mods:
            out.append(x % m)
            x //= m
        return out

    def mul(x, y):
        res, mult = 0, 1
        for m, a, b in zip(mods, dec(x), dec(y)):
            res += ((a + b) % m) * mult
            mult *= m
        return res

    return G, mul


def _matrix_group(kind, q):
    """SL(2,q), PSL(2,q) or PGL(2,q) as canonical 2x2 matrices over GF(q)."""
    F = lib.GF(q)

    def neg(M):
        return tuple(F.neg(x) for x in M)

    def normalize(M):
        for x in M:
            if x:
                inv = F.inv(x)
                return tuple(F.mul(inv, y) for y in M)
        return M

    def canon(M):
        if kind == 'psl':
            return min(M, neg(M))
        if kind == 'pgl':
            return normalize(M)
        return M

    elems = set()
    for a, b, c, d in itertools.product(range(q), repeat=4):
        det = F.sub(F.mul(a, d), F.mul(b, c))
        if kind == 'pgl':
            if det == 0:
                continue
        elif det != 1:
            continue
        elems.add(canon((a, b, c, d)))
    elems = sorted(elems)
    idx = {M: i for i, M in enumerate(elems)}

    def mul(x, y):
        a, b, c, d = elems[x]
        e, f, g, h = elems[y]
        P = (F.add(F.mul(a, e), F.mul(b, g)), F.add(F.mul(a, f), F.mul(b, h)),
             F.add(F.mul(c, e), F.mul(d, g)), F.add(F.mul(c, f), F.mul(d, h)))
        return idx[canon(P)]

    return len(elems), mul


def _spec_order(spec):
    kind = spec[0]
    if kind == 'sd':
        return spec[1] * spec[2]
    if kind == 'agl':
        q = spec[1]
        return q * (q - 1)
    if kind == 'heis':
        return spec[1] ** 3
    if kind == 'ab':
        return math.prod(spec[1])
    if kind == 'psl':
        q = spec[1]
        return q * (q * q - 1) // 2
    if kind in ('sl', 'pgl'):
        q = spec[1]
        return q * (q * q - 1)
    if kind == 'prod':
        return _spec_order(spec[1]) * _spec_order(spec[2])
    return 0


def _build_group(spec):
    kind = spec[0]
    if kind == 'sd':
        order, mul, _ = lib.semidirect_group(spec[1], spec[2], spec[3])
        return order, mul
    if kind == 'agl':
        return _agl(spec[1])
    if kind == 'heis':
        return _heis(spec[1])
    if kind == 'ab':
        return _abelian(spec[1])
    if kind in ('psl', 'sl', 'pgl'):
        return _matrix_group(kind, spec[1])
    if kind == 'prod':
        G1, m1 = _build_group(spec[1])
        G2, m2 = _build_group(spec[2])

        def mul(x, y, G2=G2, m1=m1, m2=m2):
            return m1(x // G2, y // G2) * G2 + m2(x % G2, y % G2)

        return G1 * G2, mul
    raise ValueError(kind)


def _sd_specs(G, rng):
    """Semidirect specs Z_m x| Z_kk of total order G: one random action plus the abelian one."""
    out = []
    for kk in range(1, 13):
        if G % kk:
            continue
        m = G // kk
        if m < 2:
            continue
        if kk == 1:
            out.append(('sd', m, 1, 1))
            continue
        out.append(('sd', m, kk, 1))
        if m < 3:
            continue
        for _ in range(30):
            r = rng.randrange(2, m)
            if math.gcd(r, m) == 1 and pow(r, kk, m) == 1 % m:
                out.append(('sd', m, kk, r))
                break
    return out


_SPECIAL = [
    ('agl', 19), ('heis', 7), ('ab', (7, 7, 7)), ('heis', 5), ('ab', (5, 5, 5)),
    ('psl', 5), ('pgl', 5), ('sl', 5), ('psl', 7), ('sl', 7), ('pgl', 7), ('psl', 9),
    ('prod', ('psl', 7), ('sd', 2, 1, 1)),
]
for _m in range(2, 13):
    _SPECIAL.append(('prod', ('psl', 5), ('sd', _m, 1, 1)))
    _SPECIAL.append(('prod', ('pgl', 5), ('sd', _m, 1, 1)))


def _pool(lo, hi, rng):
    """Configurations (n, k, group spec) with lo <= n <= hi, sorted by n."""
    pool = []
    for k in range(1, 5):
        Gmin = max(2, -(-lo // (2 * k)))
        Gmax = hi // (2 * k)
        for G in range(Gmin, Gmax + 1):
            n = 2 * k * G
            for sp in _sd_specs(G, rng):
                pool.append((n, k, sp))
    for sp in _SPECIAL:
        order = _spec_order(sp)
        for k in range(1, 5):
            n = 2 * k * order
            if lo <= n <= hi:
                pool.append((n, k, sp))
    pool.sort(key=lambda e: e[0])
    return pool


# ----------------------------------------------------------------------------
# Lift search. Vertices: A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h.
# A dart (i, j, s) joins A_{i,g} to B_{j, g*s}. Each A_i and each B_j has
# degree d (d layers of permutations), and moves keep these degrees fixed.
#
# Cost is computed with a numpy boolean reachability iteration from the 2k
# representatives. Cost 0 means every vertex is within distance D of each
# representative, which by transitivity makes the whole lift valid.
# ----------------------------------------------------------------------------

def _cost(k, G, D, darts, perms):
    N = 2 * k * G
    A = np.zeros((N, N), dtype=np.float32)
    ar = np.arange(G, dtype=np.int64)
    for (i, j, _), pm in zip(darts, perms):
        a = i * G + ar
        b = (k + j) * G + pm
        A[a, b] = 1.0
        A[b, a] = 1.0
    reps = np.array([i * G for i in range(k)] + [(k + j) * G for j in range(k)],
                    dtype=np.int64)
    M = np.zeros((2 * k, N), dtype=np.float32)
    M[np.arange(2 * k), reps] = 1.0
    for _ in range(D):
        M = ((M + M @ A) > 0).astype(np.float32)
    return int(2 * k * N - M.sum())


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g, h in enumerate(pm.tolist()):
            E.add((base_a + g, base_b + h))
    return 2 * k * G, sorted(E)


def _try_config(d, D, k, spec, rng, end, gcache):
    """Simulated annealing over voltages and endpoints. Returns (n, edges) or None."""
    try:
        if spec not in gcache:
            G0, mul0 = _build_group(spec)
            gcache[spec] = (G0, mul0, {})
        G, mul, pcache = gcache[spec]

        def perm(s):
            p = pcache.get(s)
            if p is None:
                p = np.array([mul(g, s) for g in range(G)], dtype=np.int64)
                pcache[s] = p
            return p

        darts = []
        for _ in range(d):
            p = list(range(k))
            rng.shuffle(p)
            for i in range(k):
                darts.append([i, p[i], rng.randrange(G)])
        perms = [perm(s) for _, _, s in darts]
        cost = _cost(k, G, D, darts, perms)

        t0 = time.monotonic()
        span = max(1e-3, end - t0)
        while cost > 0:
            now = time.monotonic()
            if now >= end:
                break
            T = 3.0 * (1.0 - (now - t0) / span) + 0.05
            if k > 1 and rng.random() < 0.4:
                t1, t2 = rng.sample(range(len(darts)), 2)
                j1, j2 = darts[t1][1], darts[t2][1]
                if j1 == j2:
                    continue
                darts[t1][1], darts[t2][1] = j2, j1
                c2 = _cost(k, G, D, darts, perms)
                if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                    cost = c2
                else:
                    darts[t1][1], darts[t2][1] = j1, j2
            else:
                t = rng.randrange(len(darts))
                old_s, old_p = darts[t][2], perms[t]
                new_s = rng.randrange(G)
                darts[t][2] = new_s
                perms[t] = perm(new_s)
                c2 = _cost(k, G, D, darts, perms)
                if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                    cost = c2
                else:
                    darts[t][2] = old_s
                    perms[t] = old_p

        if cost == 0:
            return _edges(k, G, darts, perms)
        return None
    except Exception:
        return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 1.0)
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

    try:
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
        if D >= 4 and time.monotonic() < deadline:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
    except Exception:
        pass

    # Main search: group lifts over a broad family of groups (cyclic-by-cyclic
    # semidirect products, Heisenberg, abelian, affine, PSL/SL/PGL(2,q), products),
    # with 1-4 base vertices per side. Attempt the lowest few candidates above
    # the current best, a random one at a time, until the deadline.
    try:
        moore = lib._moore_bound(d, D)
        lo = max(2 * d, int(0.3 * moore))
        hi = min(int(0.6 * moore), 900)
        if hi >= lo and hi > best_n:
            pool = _pool(lo, hi, rng)
            gcache = {}
            while time.monotonic() < deadline:
                cands = [e for e in pool if e[0] > best_n]
                if not cands:
                    break
                n_, k, spec = rng.choice(cands[:40])
                remaining = deadline - time.monotonic()
                budget = min(3.5, remaining)
                if budget <= 0.05:
                    break
                end = time.monotonic() + budget
                res = _try_config(d, D, k, spec, rng, end, gcache)
                if res is not None:
                    consider(res[0], res[1])
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
