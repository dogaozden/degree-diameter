import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact and safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez graph of degree d (q = d - 2 a prime power >= 3); diameter 3."""
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    return lib.araujo_lopez_graph(q)


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
# NEW FAMILY: bipartite doubles of Cayley graphs of PSL(2, p).
#
# Group G = PSL(2, p), elements = matrices of det 1 modulo sign.
# Vertices: A_g = g (side 0) and B_h = |G| + h (side 1).
# Edges: A_g ~ B_{g*s} for each of d distinct generators s in S.
# Left multiplication is an automorphism, so the diameter is decided by two BFS
# runs, from (e, side 0) and (e, side 1). The search anneals over the generator set S.
# ----------------------------------------------------------------------------

_PSL_ITERS = 6000


def _psl2_tables(p):
    """Return (R, keyidx): R is a (|G|, 4) int array of canonical matrices, keyidx maps codes to indices."""
    def enc(a, b, c, d):
        return ((a * p + b) * p + c) * p + d

    keyidx = np.full(p ** 4, -1, dtype=np.int64)
    reps = []
    for a, b, c, d in itertools.product(range(p), repeat=4):
        if (a * d - b * c) % p != 1:
            continue
        k1 = enc(a, b, c, d)
        k2 = enc((-a) % p, (-b) % p, (-c) % p, (-d) % p)
        if k1 < k2:
            keyidx[k1] = len(reps)
            reps.append((a, b, c, d))
    return np.array(reps, dtype=np.int64), keyidx


def _rperm(R, keyidx, p, s):
    """Permutation g -> g*s on group indices, for matrix s = (s11, s12, s21, s22)."""
    A, B, C, D = R[:, 0], R[:, 1], R[:, 2], R[:, 3]
    s11, s12, s21, s22 = s
    P11 = (A * s11 + B * s21) % p
    P12 = (A * s12 + B * s22) % p
    P21 = (C * s11 + D * s21) % p
    P22 = (C * s12 + D * s22) % p
    k1 = ((P11 * p + P12) * p + P21) * p + P22
    k2 = (((-P11) % p * p + (-P12) % p) * p + (-P21) % p) * p + (-P22) % p
    perm = keyidx[np.minimum(k1, k2)]
    return perm


def _psl_search(p, d, D, rng, deadline):
    """Anneal a generator set S (size d) in PSL(2, p) until the bipartite double has diameter <= D."""
    R, keyidx = _psl2_tables(p)
    G = len(R)
    e = int(keyidx[min(((1 * p + 0) * p + 0) * p + 1,
                       (((p - 1) * p + 0) * p + 0) * p + (p - 1))])
    cache = {}

    def get(i):
        if i not in cache:
            s = tuple(int(x) for x in R[i])
            sinv = (s[3], (-s[1]) % p, (-s[2]) % p, s[0])
            cache[i] = (_rperm(R, keyidx, p, s), _rperm(R, keyidx, p, sinv))
        return cache[i]

    def cost(S):
        perms = [get(s) for s in S]
        total = 0
        for side in (0, 1):
            seen = [np.zeros(G, dtype=bool), np.zeros(G, dtype=bool)]
            seen[side][e] = True
            frontier = np.array([e], dtype=np.int64)
            cur = side
            for _ in range(D):
                tgt = 1 - cur
                if cur == 0:
                    nb = np.concatenate([pf[0][frontier] for pf in perms])
                else:
                    nb = np.concatenate([pf[1][frontier] for pf in perms])
                nb = np.unique(nb)
                nb = nb[~seen[tgt][nb]]
                seen[tgt][nb] = True
                frontier = nb
                cur = tgt
                if frontier.size == 0:
                    break
            total += 2 * G - int(seen[0].sum()) - int(seen[1].sum())
        return total

    while time.monotonic() < deadline:
        S = rng.sample(range(G), d)
        c = cost(S)
        for it in range(_PSL_ITERS):
            if c == 0 or time.monotonic() > deadline:
                break
            frac = 1.0 - it / _PSL_ITERS
            T = max(0.2, 0.3 * c * frac)
            i = rng.randrange(d)
            new = rng.randrange(G)
            if new in S:
                continue
            S2 = list(S)
            S2[i] = new
            c2 = cost(S2)
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
                S, c = S2, c2
        if c == 0:
            edges = []
            for s in S:
                perm = get(s)[0]
                tgt = perm.tolist()
                for g in range(G):
                    edges.append((g, G + tgt[g]))
            return 2 * G, edges
    return None


# ----------------------------------------------------------------------------
# Parent family: bi-Cayley lifts over semidirect products Z_m x| Z_k2 (kept as
# the fallback search for the remaining time).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)
_SWAP_PROB = 0.3
_STRUCT_PROB = 0.5
_ITERS = 4000


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e))."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _structured_init(d, k, G, Ts, rng):
    x = rng.randrange(1, G)
    powers = [0]
    for _ in range(d):
        powers.append(int(Ts[x, powers[-1]]))
    ys = [rng.randrange(G) for _ in range(k)]
    layers = [[(i + l) % k for i in range(k)] for l in range(d)]
    S = [[int(Ts[ys[i], powers[l + 1]]) for i in range(k)] for l in range(d)]
    return layers, S


def _random_init(d, k, G, rng):
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    return layers, S


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _cost(k, G, D, nbr):
    d, N = nbr.shape
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters):
    N = 2 * k * G
    if rng.random() < _STRUCT_PROB:
        layers, S = _structured_init(d, k, G, Ts, rng)
    else:
        layers, S = _random_init(d, k, G, rng)
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    cost = _cost(k, G, D, nbr) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        l = rng.randrange(d)

        if k > 1 and rng.random() < _SWAP_PROB:
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            c2 = _cost(k, G, D, nbr) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        i = rng.randrange(k)
        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        c2 = _cost(k, G, D, nbr) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.9 * time_limit, time_limit - 5.0))
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
        try:
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
        except Exception:
            pass

    # Exact constructions: return immediately when they are optimal.
    if D >= 3:
        try:
            pg = _best_pg(d)
        except Exception:
            pg = None
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

        if D == 3:
            try:
                aj = _araujo(d)
            except Exception:
                aj = None
            if aj is not None:
                consider(aj[0], aj[1])
                return best

    if D >= 4 and time.monotonic() < deadline:
        try:
            gq = _best_gq(d)
        except Exception:
            gq = None
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # NEW: bipartite doubles of Cayley graphs of PSL(2, p), tried largest first.
    # Each candidate must fit the Moore bound and beat the current best.
    moore = lib.moore_bound(d, D)
    cands = []
    for p in (13, 11, 7, 5):
        order = p * (p * p - 1) // 2
        if 2 * order <= moore and 2 * order > best_n:
            cands.append((order, p))
    cands.sort(reverse=True)

    psl_end = start + 0.75 * budget
    for idx, (order, p) in enumerate(cands):
        now = time.monotonic()
        remaining = psl_end - now
        if remaining <= 0.5:
            break
        share = remaining * (0.6 if idx < len(cands) - 1 else 1.0)
        try:
            res = _psl_search(p, d, D, rng, now + share)
        except Exception:
            res = None
        if res is not None:
            consider(res[0], res[1])

    # Parent bandit search over semidirect bi-Cayley lifts for the remaining time.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        try:
            res = _search(d, D, k, G, Ts, Invs, rng, deadline, _ITERS)
        except Exception:
            res = None
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
