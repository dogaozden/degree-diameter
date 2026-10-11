import math
import random
import time

import numpy as np

import lib


_BIG = 10 ** 9

# Matrix groups as (order, mode, prime, generators) over GF(p).
_MATS = {
    "PSL7": (168, "PSL", 7, [(1, 1, 0, 1), (0, 6, 1, 0)]),
    "SL7": (336, "SL", 7, [(1, 1, 0, 1), (0, 6, 1, 0)]),
    "PGL7": (336, "PGL", 7, [(1, 1, 0, 1), (0, 1, 1, 0), (3, 0, 0, 1)]),
    "SL5": (120, "SL", 5, [(1, 1, 0, 1), (0, 4, 1, 0)]),
    "PGL5": (120, "PGL", 5, [(1, 1, 0, 1), (0, 1, 1, 0), (2, 0, 0, 1)]),
}
_MAT_CACHE = {}


# ----------------------------------------------------------------------------
# Group construction. A group is given as (mul, inv): mul[x, y] = x*y as an
# int64 table, inv[x] = x^-1, identity coded as 0.
# ----------------------------------------------------------------------------

def _mat_group(mode, p, gens):
    """Closure of matrix generators over GF(p), modulo scalars (PGL), signs (PSL), or not at all (SL)."""
    def norm(M):
        if mode == "PGL":
            c = next(x for x in M if x)
            ic = pow(c, p - 2, p)
            return tuple((x * ic) % p for x in M)
        if mode == "PSL":
            neg = tuple((-x) % p for x in M)
            return min(M, neg)
        return tuple(M)

    def mm(A, B):
        a, b, c, d = A
        e, f, g, h = B
        return ((a * e + b * g) % p, (a * f + b * h) % p,
                (c * e + d * g) % p, (c * f + d * h) % p)

    gs = [norm(tuple(g)) for g in gens]
    I = norm((1, 0, 0, 1))
    elems = [I]
    index = {I: 0}
    frontier = [I]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gs:
                y = norm(mm(x, g))
                if y not in index:
                    index[y] = len(elems)
                    elems.append(y)
                    nxt.append(y)
        frontier = nxt
    N = len(elems)
    mul = np.zeros((N, N), dtype=np.int64)
    for i, x in enumerate(elems):
        for j, y in enumerate(elems):
            mul[i, j] = index[norm(mm(x, y))]
    inv = np.argmax(mul == 0, axis=1).astype(np.int64)
    return mul, inv


def _mat_cached(name):
    if name not in _MAT_CACHE:
        _, mode, p, gens = _MATS[name]
        _MAT_CACHE[name] = _mat_group(mode, p, gens)
    return _MAT_CACHE[name]


def _cyclic(n):
    ar = np.arange(n, dtype=np.int64)
    mul = (ar[:, None] + ar[None, :]) % n
    inv = (-ar) % n
    return mul, inv


def _semidirect(m, k, r):
    """Z_m x|_r Z_k, element (a, b) coded as a*k + b; mirrors lib.semidirect_group."""
    N = m * k
    x = np.arange(N, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, bb, m) for bb in range(k)], dtype=np.int64)
    A = a[:, None]
    B = b[:, None]
    C = a[None, :]
    Dd = b[None, :]
    mul = ((A + pw[B] * C) % m) * k + (B + Dd) % k
    nb = (-b) % k
    inv = ((-pw[nb] * a) % m) * k + nb
    return mul.astype(np.int64), inv.astype(np.int64)


def _direct(A, C):
    mA, iA = A
    mC, iC = C
    NA = mA.shape[0]
    NC = mC.shape[0]
    N = NA * NC
    idx = np.arange(N)
    ia = idx // NC
    ib = idx % NC
    mul = mA[ia[:, None], ia[None, :]] * NC + mC[ib[:, None], ib[None, :]]
    inv = iA[ia] * NC + iC[ib]
    return mul.astype(np.int64), inv.astype(np.int64)


def _specs(G):
    """Group specifications of order G: semidirect products, matrix groups, and products with cyclic groups."""
    specs = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                specs.append(("sd", m, k, r))
    for name, (order, _, _, _) in _MATS.items():
        if G % order == 0:
            c = G // order
            specs.append(("mat", name) if c == 1 else ("prodc", name, c))
    return specs


def _build(spec):
    if spec[0] == "sd":
        return _semidirect(spec[1], spec[2], spec[3])
    if spec[0] == "mat":
        return _mat_cached(spec[1])
    return _direct(_mat_cached(spec[1]), _cyclic(spec[2]))


# ----------------------------------------------------------------------------
# Multi-base voltage lifts over a group G. There are k base vertices per side
# and d layers. Layer L pairs A-copy i with B-copy p_L(i) through voltage g_L,
# so A(i,x) ~ B(p_L(i), x*g_L). Left translation is an automorphism, so the
# cost is counted from the 2k copy representatives.
# ----------------------------------------------------------------------------

def _cost(mul, inv, k, D, P, Gs):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    G = mul.shape[0]
    kG = k * G
    V = 2 * kG
    d = len(Gs)
    for i in range(k):
        seen = set()
        for L in range(d):
            key = (P[L][i], Gs[L])
            if key in seen:
                return _BIG
            seen.add(key)
    tA = []
    tB = []
    for L in range(d):
        p = P[L]
        g = Gs[L]
        ta = np.empty(kG, dtype=np.int64)
        pinv = [0] * k
        for i in range(k):
            ta[i * G:(i + 1) * G] = (k + p[i]) * G + mul[:, g]
            pinv[p[i]] = i
        ginv = int(inv[g])
        tb = np.empty(kG, dtype=np.int64)
        for j in range(k):
            tb[j * G:(j + 1) * G] = pinv[j] * G + mul[:, ginv]
        tA.append(ta)
        tB.append(tb)
    total = 0
    for src in [i * G for i in range(k)] + [(k + j) * G for j in range(k)]:
        seen = np.zeros(V, dtype=bool)
        seen[src] = True
        fr = np.array([src], dtype=np.int64)
        cnt = 1
        for _ in range(D):
            fa = fr[fr < kG]
            fb = fr[fr >= kG] - kG
            parts = []
            if fa.size:
                parts.extend(t[fa] for t in tA)
            if fb.size:
                parts.extend(t[fb] for t in tB)
            if not parts:
                break
            cand = np.unique(np.concatenate(parts))
            cand = cand[~seen[cand]]
            if cand.size == 0:
                break
            seen[cand] = True
            cnt += int(cand.size)
            fr = cand
        total += V - cnt
    return total


def _search(mul, inv, k, d, D, rng, iters, deadline):
    """Simulated annealing over layer voltages and (for k > 1) layer permutations."""
    G = mul.shape[0]
    P = []
    Gs = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        P.append(p)
        Gs.append(rng.randrange(G))
    cost = _cost(mul, inv, k, D, P, Gs)
    if cost == 0:
        return P, Gs
    T0 = 2.0 if cost >= _BIG else max(2.0, 0.05 * cost)
    T1 = 0.3
    for it in range(iters):
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / max(1, iters))
        L = rng.randrange(d)
        if k > 1 and rng.random() < 0.3:
            a, b = rng.sample(range(k), 2)
            old = P[L][:]
            P[L][a], P[L][b] = P[L][b], P[L][a]
            c2 = _cost(mul, inv, k, D, P, Gs)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                P[L] = old
        else:
            new = rng.randrange(G)
            old = Gs[L]
            if new == old:
                continue
            Gs[L] = new
            c2 = _cost(mul, inv, k, D, P, Gs)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                Gs[L] = old
        if cost == 0:
            return P, Gs
    return None


def _to_edges(mul, k, P, Gs):
    G = mul.shape[0]
    E = set()
    for L in range(len(Gs)):
        p = P[L]
        col = mul[:, Gs[L]].tolist()
        for i in range(k):
            ba = i * G
            bb = (k + p[i]) * G
            for x in range(G):
                E.add((ba + x, bb + col[x]))
    return 2 * k * G, sorted(E)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and order 2d.
    n0, e0 = lib.haar_graph(d, range(d))
    best = (n0, list(e0))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Projective plane for D = 3, when available.
    if D == 3 and d >= 3:
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
        if qs:
            n1, e1 = lib.projective_plane_incidence(qs[0])
            consider(n1, e1)

    # Main search: multi-base voltage lifts over nonabelian groups, round-robin
    # over (k, G) pairs with growing annealing budgets.
    iters = 60
    while best[0] < moore and time.monotonic() < deadline:
        pairs = []
        for k in (1, 2, 3):
            lo_g = best[0] // (2 * k) + 1
            hi_g = moore // (2 * k)
            for G in range(max(lo_g, 2), hi_g + 1):
                pairs.append((2 * k * G, k, G))
        if not pairs:
            break
        pairs.sort()
        progressed = False
        for total, k, G in pairs:
            if time.monotonic() >= deadline:
                break
            specs = _specs(G)
            if not specs:
                continue
            mul, inv = _build(specs[rng.randrange(len(specs))])
            res = _search(mul, inv, k, d, D, rng, iters, deadline)
            if res is not None:
                P, Gs = res
                n2, e2 = _to_edges(mul, k, P, Gs)
                consider(n2, e2)
                progressed = True
                break
        if not progressed:
            iters = min(iters * 2, 4000)

    if not lib.is_valid(best[0], best[1], d, D):
        n0, e0 = lib.haar_graph(d, range(d))
        return n0, list(e0)
    return best
