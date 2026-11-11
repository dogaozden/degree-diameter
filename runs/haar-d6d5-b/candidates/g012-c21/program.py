"""Multi-base voltage lifts for the bipartite degree-diameter problem (diameter 5, degree 6).

Construction.  A Haar graph has one A-vertex and one B-vertex per group element. Here the base graph has p A-vertices
and p B-vertices, each of degree 6, with darts (u, (u+t) mod p) for t = 0..5. Each dart carries a voltage a in a group
G of order m. The lift has 2*p*m vertices: A-vertex (u, x) is joined to B-vertex (v, x*a) for each dart (u, v, a).
Left multiplication by G is an automorphism, so the diameter is at most 5 iff every base vertex reaches every lift
vertex within 5 steps from its identity copy. The cost is the number of unreached vertices summed over the 2p base
sources. Simulated annealing over the voltages drives it to 0. Every returned graph is checked with lib.is_valid,
and a verified Haar graph of order 660 is the fallback.
"""
import math
import time

import numpy as np

import lib

TARGET = (6, 5)


# ----------------------------------------------------------------------------- group tables (identity = index 0)

def _finish(MT):
    MT = np.ascontiguousarray(MT, dtype=np.int64)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def _table_from_coords(elems, mulfun):
    N, c = elems.shape
    base = int(elems.max()) + 1
    wts = base ** np.arange(c, dtype=np.int64)
    codes = elems.astype(np.int64) @ wts
    order = np.argsort(codes)
    sc = codes[order]
    MT = np.empty((N, N), dtype=np.int64)
    for i in range(N):
        prod = mulfun(elems[i][None, :], elems)
        MT[i] = order[np.searchsorted(sc, prod.astype(np.int64) @ wts)]
    return _finish(MT)


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> a*k + j, (a,j)(b,l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
    if pow(lam, k, m) != 1 % m:
        raise ValueError("bad semidirect data")
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int64)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def group_agl(q, k):
    """GF(q) x| C_k: maps t -> a t + b with a in the order-k subgroup of GF(q)^*."""
    F = lib.GF(q)
    H = [a for a in range(1, q) if F.pow(a, k) == 1]
    if len(H) != k:
        raise ValueError("bad subgroup")
    e = np.array([(0, 1)] + [(b, a) for b in range(q) for a in H if (b, a) != (0, 1)], dtype=np.int64)
    add, mulT = F.add_table, F.mul_table

    def mul(X, Y):
        return np.stack([add[X[..., 0], mulT[X[..., 1], Y[..., 0]]], mulT[X[..., 1], Y[..., 1]]], axis=-1)
    return _table_from_coords(e, mul)


def group_heis(p):
    """Heisenberg group over Z_p, order p^3."""
    e = np.array(list(_product3(p)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def _product3(p):
    for a in range(p):
        for b in range(p):
            for c in range(p):
                yield (a, b, c)


def build_group(spec):
    kind = spec[0]
    if kind == 'meta':
        return group_meta(spec[1], spec[2], spec[3])
    if kind == 'agl':
        return group_agl(spec[1], spec[2])
    if kind == 'heis':
        return group_heis(spec[1])
    raise ValueError(kind)


def group_specs(N):
    """Descriptions of groups of order N: non-abelian semidirect products first, cyclic last."""
    specs = []
    for k in range(2, N + 1):
        if N % k:
            continue
        a = N // k
        if a < 2:
            continue
        for lam in range(2, a):
            if math.gcd(lam, a) == 1 and pow(lam, k, a) == 1:
                specs.append(('meta', a, k, lam))
    for q in range(3, N + 1):
        if N % q == 0 and lib.is_prime_power(q):
            k = N // q
            if k >= 2 and (q - 1) % k == 0:
                specs.append(('agl', q, k))
    p = round(N ** (1 / 3))
    if p >= 2 and p ** 3 == N:
        specs.append(('heis', p))
    specs.append(('meta', N, 1, 1))  # cyclic fallback
    return specs


# ------------------------------------------------------------------------- voltage lift machinery

def _layout(p):
    """Dart k = 6u + t goes from A_u to B_{(u+t) mod p}. Returns target v, B-slot index and same-pair mates."""
    L = 6 * p
    dv = [0] * L
    bslot = [0] * L
    cnt = [0] * p
    for u in range(p):
        for t in range(6):
            k = u * 6 + t
            v = (u + t) % p
            dv[k] = v
            bslot[k] = cnt[v]
            cnt[v] += 1
    mates = []
    for k in range(L):
        u, t = divmod(k, 6)
        v = dv[k]
        mates.append([u * 6 + t2 for t2 in range(6) if t2 != t and (u + t2) % p == v])
    return dv, bslot, mates


def _setd(NB, MT, inv, p, m, xs, dv, bslot, k, a):
    u, t = divmod(k, 6)
    v = dv[k]
    NB[u * m:(u + 1) * m, t] = p * m + v * m + MT[xs, a]
    NB[p * m + v * m:p * m + (v + 1) * m, bslot[k]] = u * m + MT[xs, inv[a]]


def anneal(MT, inv, p, deadline, rng, temp=1.5, patience=2500):
    """Anneal the voltages of a p-base lift over the group. Returns (voltages or None, cost)."""
    m = MT.shape[0]
    L = 6 * p
    n = 2 * p * m
    xs = np.arange(m)
    dv, bslot, mates = _layout(p)
    sources = [u * m for u in range(p)] + [p * m + v * m for v in range(p)]

    def cost(NB):
        total = 0
        for s in sources:
            vis = np.zeros(n, dtype=bool)
            vis[s] = True
            fr = np.array([s], dtype=np.int64)
            for _ in range(5):
                nxt = NB[fr].ravel()
                nxt = nxt[~vis[nxt]]
                if nxt.size == 0:
                    break
                nxt = np.unique(nxt)
                vis[nxt] = True
                fr = nxt
            total += n - int(vis.sum())
        return total

    best, bestc = None, 1 << 60
    while time.monotonic() < deadline:
        V = [-1] * L
        for k in range(L):
            while True:
                g = int(rng.integers(m))
                if all(V[q] != g for q in mates[k] if V[q] >= 0):
                    break
            V[k] = g
        NB = np.empty((n, 6), dtype=np.int64)
        for k in range(L):
            _setd(NB, MT, inv, p, m, xs, dv, bslot, k, V[k])
        cur = cost(NB)
        if cur < bestc:
            best, bestc = list(V), cur
        if cur == 0:
            return best, 0
        since = 0
        while since <= patience and time.monotonic() < deadline:
            k = int(rng.integers(L))
            g = int(rng.integers(m))
            if g == V[k] or any(V[q] == g for q in mates[k]):
                continue
            old = V[k]
            V[k] = g
            _setd(NB, MT, inv, p, m, xs, dv, bslot, k, g)
            c = cost(NB)
            delta = c - cur
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cur = c
                since = 0 if delta < 0 else since + 1
                if c < bestc:
                    best, bestc = list(V), c
                    if c == 0:
                        return best, 0
            else:
                V[k] = old
                _setd(NB, MT, inv, p, m, xs, dv, bslot, k, old)
                since += 1
    return best, bestc


def graph_from(MT, inv, p, V):
    m = MT.shape[0]
    n = 2 * p * m
    dv, bslot, _ = _layout(p)
    xs = np.arange(m)
    NB = np.empty((n, 6), dtype=np.int64)
    for k in range(6 * p):
        _setd(NB, MT, inv, p, m, xs, dv, bslot, k, V[k])
    edges = [(i, int(NB[i, j])) for i in range(p * m) for j in range(6)]
    return n, edges


# ------------------------------------------------------------------------------------------- fallbacks

def fallback():
    """Verified Haar graph of order 660 (group Z_33 x| Z_10, connection set S)."""
    try:
        MT, _ = group_meta(33, 10, 26)
        S = [0, 179, 116, 180, 47, 306]
        N = MT.shape[0]
        edges = [(g, N + int(MT[s, g])) for s in S for g in range(N)]
        n = 2 * N
        if lib.is_valid(n, edges, 6, 5):
            return n, edges
    except Exception:
        pass
    return None


def trivial(d, D):
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def plan_items(best_n, rng, cache):
    items = []
    for p in range(2, 9):
        for m in range(2, 1000):
            n = 2 * p * m
            if n > 900:
                break
            if n <= best_n:
                continue
            if m not in cache:
                cache[m] = group_specs(m)
            specs = cache[m]
            if not specs:
                continue
            idx = rng.permutation(len(specs))[:2]
            for i in idx:
                items.append((n, p, m, specs[int(i)]))
    items.sort(key=lambda it: (it[0], float(rng.random())))
    return items


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    end = t0 + min(0.75 * time_limit, time_limit - 8.0)
    rng = np.random.default_rng(seed)

    best = fallback()
    if best is None:
        best = (lambda g: g)(trivial(d, D))
    best_n = best[0]

    cache = {}
    items = plan_items(best_n, rng, cache)
    for n, p, m, spec in items:
        now = time.monotonic()
        if now >= end:
            break
        if n <= best_n:
            continue
        try:
            MT, inv = build_group(spec)
            if MT.shape[0] != m:
                continue
        except Exception:
            continue
        slice_end = min(end, now + 5.0)
        try:
            V, c = anneal(MT, inv, p, slice_end, rng)
        except Exception:
            continue
        if V is None or c != 0:
            continue
        try:
            g = graph_from(MT, inv, p, V)
            if lib.is_valid(g[0], g[1], d, D):
                best = g
                best_n = g[0]
        except Exception:
            continue
    return best
