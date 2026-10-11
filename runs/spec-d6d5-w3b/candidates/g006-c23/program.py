import math
import random
import time

import numpy as np

import lib

BIG = 10 ** 9
_EMPTY = np.zeros(0, dtype=np.int64)


# ----------------------------------------------------------------------------
# Small-number helpers.
# ----------------------------------------------------------------------------

def _is_prime(n):
    if n < 2:
        return False
    f = 2
    while f * f <= n:
        if n % f == 0:
            return False
        f += 1
    return True


def _prime_factors(n):
    fs = set()
    f = 2
    x = n
    while f * f <= x:
        while x % f == 0:
            fs.add(f)
            x //= f
        f += 1
    if x > 1:
        fs.add(x)
    return fs


def _primitive_root(p):
    if p == 2:
        return 1
    fs = _prime_factors(p - 1)
    for r in range(2, p):
        if all(pow(r, (p - 1) // q, p) != 1 for q in fs):
            return r
    return 1


# ----------------------------------------------------------------------------
# Groups of a given order: affine groups AGL(1,p) (order p(p-1)) and general
# semidirect products Z_m x| Z_k2 (order m*k2).
# ----------------------------------------------------------------------------

def _random_group(G, rng):
    """Return (order, mul, inv) for a group of order G, or None."""
    if rng.random() < 0.5:
        for p in range(2, G + 1):
            if p * (p - 1) == G:
                if _is_prime(p):
                    r = _primitive_root(p)
                    try:
                        return lib.semidirect_group(p, p - 1, r)
                    except ValueError:
                        pass
                break
    opts = []
    for k2 in range(1, G + 1):
        if G % k2:
            continue
        m = G // k2
        if m == 1:
            continue
        if k2 == 1:
            opts.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                opts.append((m, k2, r))
    if not opts:
        return None
    m, k2, r = rng.choice(opts)
    try:
        return lib.semidirect_group(m, k2, r)
    except ValueError:
        return None


# ----------------------------------------------------------------------------
# Algebraic candidates for D = 3 (valid, cheap, and optimal at d = 3, D = 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley (voltage) graphs over a finite group G with k A-orbits and k B-orbits.
#
# Vertices: A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h.
# Dart (i, j, s) joins A_{i,g} to B_{j,g*s} for all g.
# Each layer of d layers assigns one dart per A-orbit with a permutation onto
# B-orbits, so every vertex has degree exactly d.
#
# Left multiplication by the group is an automorphism that is transitive on each
# orbit, so diameter <= D is checked by BFS from the 2k representatives
# A_{i,e} and B_{j,e} (vectorised with numpy).
# ----------------------------------------------------------------------------

def _eval(k, G, D, darts, F, Bw):
    """Number of (representative, vertex) pairs at distance > D. Zero means valid."""
    N = 2 * k * G
    keys = {(i, j, s) for i, j, s in darts}
    if len(keys) < len(darts):
        return BIG
    Ain = [[] for _ in range(k)]
    Bin = [[] for _ in range(k)]
    for t, (i, j, s) in enumerate(darts):
        Ain[i].append(t)
        Bin[j].append(t)

    total = 0
    reps = [(0, i) for i in range(k)] + [(1, j) for j in range(k)]
    for side, o in reps:
        vis = [[np.zeros(G, dtype=bool) for _ in range(k)] for _ in range(2)]
        front = [[_EMPTY] * k for _ in range(2)]
        vis[side][o][0] = True
        front[side][o] = np.zeros(1, dtype=np.int64)
        count = 1
        for _ in range(D):
            newA = [[] for _ in range(k)]
            newB = [[] for _ in range(k)]
            for i in range(k):
                f = front[0][i]
                if f.size:
                    for t in Ain[i]:
                        _, j_, s = darts[t]
                        newB[j_].append(F(s)[f])
            for j in range(k):
                f = front[1][j]
                if f.size:
                    for t in Bin[j]:
                        i_, _, s = darts[t]
                        newA[i_].append(Bw(s)[f])
            grew = False
            for sd, news in ((0, newA), (1, newB)):
                for x in range(k):
                    if news[x]:
                        c = np.unique(np.concatenate(news[x]))
                        c = c[~vis[sd][x][c]]
                        vis[sd][x][c] = True
                        front[sd][x] = c
                        count += int(c.size)
                        if c.size:
                            grew = True
                    else:
                        front[sd][x] = _EMPTY
            if not grew:
                break
        total += N - count
    return total


def _attempt(d, D, k, G, mul, inv, rng, deadline, iters):
    """Anneal a bi-Cayley lift of order 2kG. Returns (n, edges) on success, else None."""
    if k == 1 and G < d:
        return None
    fc, bc = {}, {}

    def F(s):
        a = fc.get(s)
        if a is None:
            a = np.array([mul(g, s) for g in range(G)], dtype=np.int64)
            fc[s] = a
        return a

    def Bw(s):
        a = bc.get(s)
        if a is None:
            si = inv(s)
            a = np.array([mul(h, si) for h in range(G)], dtype=np.int64)
            bc[s] = a
        return a

    darts = []
    if k == 1:
        for s in rng.sample(range(G), d):
            darts.append([0, 0, s])
    else:
        for _ in range(d):
            p = list(range(k))
            rng.shuffle(p)
            for i in range(k):
                darts.append([i, p[i], rng.randrange(G)])

    cur = _eval(k, G, D, darts, F, Bw)
    T0 = 1.5
    for it in range(iters):
        if cur == 0 or time.monotonic() >= deadline:
            break
        T = max(0.08, T0 * (1.0 - it / float(iters)))
        if k == 1 or rng.random() < 0.7:
            t = rng.randrange(len(darts))
            old = darts[t][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[t][2] = new
            c2 = _eval(k, G, D, darts, F, Bw)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                darts[t][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            t1, t2 = L * k + a, L * k + b
            darts[t1][1], darts[t2][1] = darts[t2][1], darts[t1][1]
            c2 = _eval(k, G, D, darts, F, Bw)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                darts[t1][1], darts[t2][1] = darts[t2][1], darts[t1][1]

    if cur != 0:
        return None
    E = set()
    for i, j, s in darts:
        fl = F(s).tolist()
        for g in range(G):
            E.add((i * G + g, (k + j) * G + fl[g]))
    return 2 * k * G, sorted(E)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    ks = [1, 1, 1, 2]
    while best[0] < moore and time.monotonic() < deadline - 0.3:
        k = rng.choice(ks)
        lo = best[0] // (2 * k) + 1
        hi = min(moore // (2 * k), lo + max(4, lo // 6))
        if hi < lo:
            k = 1
            lo = best[0] // 2 + 1
            hi = min(moore // 2, lo + max(4, lo // 6))
            if hi < lo:
                break
        G = rng.randint(lo, hi)
        grp = _random_group(G, rng)
        if grp is None:
            continue
        order, mul, inv = grp
        seg = 2.5 if k == 1 else 4.0
        seg_end = min(deadline, time.monotonic() + seg)
        iters = 2500 if k == 1 else 1500
        res = _attempt(d, D, k, order, mul, inv, rng, seg_end, iters)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], best[1]
