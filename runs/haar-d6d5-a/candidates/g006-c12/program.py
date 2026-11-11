"""Two-stage search for the bipartite degree-diameter problem at diameter 5 (numpy only).

STAGE 1 (new): voltage lifts of small bipartite base graphs over finite groups.
  The base graph has k vertices per side. It is d-regular and is the union of d perfect matchings
  (perms[r] is the B-index that A_i joins in slot r). Each base dart gets a group voltage, so the lift
  has 2*k*|G| vertices. Left multiplication by h is an automorphism of the lift that fixes each fiber setwise
  and acts transitively on it. So the diameter is at most D iff, for each of the 2k base vertices s, every
  vertex is within distance D of the representative (s, identity). The cost is the number of unreached
  (source, vertex) pairs plus a penalty for parallel edges. Simulated annealing over voltages and matchings
  drives this cost to 0. Lifts with k = 2, 3, 4, 5 and orders chosen so that 2*k*|G| >= 688 are tried,
  smallest first. Every candidate is checked with lib.is_valid.

STAGE 2 (kept from the previous version): Haar graphs, (g,A) ~ (s*g,B), searched with the one-swap and
  product-move annealing, which reached the record 684 earlier. This is the fallback path.

The largest valid graph found by either stage is returned. If nothing is valid, a trivial graph is returned.
"""
import itertools
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------- group tables (identity = 0)

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> a*k + j, (a, j)(b, l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def _table_from_coords(elems, mulfun):
    """Group table from an (N, c) coordinate array (identity first) and a vectorised product."""
    N, c = elems.shape
    base = int(elems.max()) + 1
    wts = base ** np.arange(c, dtype=np.int64)
    codes = elems.astype(np.int64) @ wts
    order = np.argsort(codes)
    sorted_codes = codes[order]
    MT = np.empty((N, N), dtype=np.int32)
    for i in range(N):
        prod = mulfun(elems[i][None, :], elems)
        MT[i] = order[np.searchsorted(sorted_codes, prod.astype(np.int64) @ wts)]
    return _finish(MT)


def group_heis(p):
    """Heisenberg group mod p, order p^3."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_sl2(p):
    """SL(2, p) for a prime p, order p(p^2-1)."""
    allm = np.array(list(itertools.product(range(p), repeat=4)), dtype=np.int64)
    allm = allm[(allm[:, 0] * allm[:, 3] - allm[:, 1] * allm[:, 2]) % p == 1]
    ident = np.nonzero((allm == np.array([1, 0, 0, 1])).all(axis=1))[0][0]
    allm = np.vstack([allm[ident:ident + 1], np.delete(allm, ident, axis=0)])

    def mul(X, Y):
        a, b, c, d = (X[..., i] for i in range(4))
        e, f, g, h = (Y[..., i] for i in range(4))
        return np.stack([(a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p], axis=-1)
    return _table_from_coords(allm, mul)


def group_agl(q, k=None):
    """GF(q) x| C_k: maps t -> a*t + b with a in the subgroup of order k of GF(q)^* (default AGL(1, q))."""
    F = lib.GF(q)
    k = q - 1 if k is None else k
    H = [a for a in range(1, q) if F.pow(a, k) == 1]
    assert len(H) == k
    e = np.array([(0, 1)] + [(b, a) for b in range(q) for a in H if (b, a) != (0, 1)], dtype=np.int64)
    add, mulT = F.add_table, F.mul_table

    def mul(X, Y):
        return np.stack([add[X[..., 0], mulT[X[..., 1], Y[..., 0]]], mulT[X[..., 1], Y[..., 1]]], axis=-1)
    return _table_from_coords(e, mul)


def group_times_cyclic(grp, k):
    """Direct product of a table group with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


def metacyclic_candidates(lo, hi, limit):
    """Non-abelian metacyclic Z_m x|_lam Z_k with lo <= m*k <= hi (one lam per (m, k)), smallest order first."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) != 1 or lam % m == 1:
                    continue
                if pow(lam, k, m) == 1 % m:
                    out.append((m, k, lam))
                    break
        if len(out) >= limit:
            break
    return out[:limit]


# ------------------------------------------------------------------ STAGE 1: voltage lifts of small base graphs

def lift_tables(MT, inv, k, d, perms, volt):
    """Neighbour table of the lift. A-fibre i is vertices i*N..i*N+N-1, B-fibre j is k*N + j*N + y.
    perms[r, i] = B-index joined to A_i in slot r. volt[i, r] = group voltage of that dart.
    A-vertex (i, x) ~ (j, x*g). B-vertex (j, y) ~ (i, y*g^-1) for the slot r with pinv[r, j] = i."""
    N = MT.shape[0]
    NB = np.empty((2 * k * N, d), dtype=np.int64)
    x = np.arange(N)
    pinv = np.empty_like(perms)
    for r in range(d):
        pinv[r, perms[r]] = np.arange(k)
    for i in range(k):
        for r in range(d):
            j = int(perms[r, i])
            NB[i * N + x, r] = k * N + j * N + MT[x, volt[i, r]]
    for j in range(k):
        for r in range(d):
            i = int(pinv[r, j])
            NB[k * N + j * N + x, r] = i * N + MT[x, inv[volt[i, r]]]
    return NB


def lift_dups(k, d, perms, volt):
    """Number of parallel edges in the lift (slots of the same A-vertex landing on the same neighbour)."""
    dup = 0
    for i in range(k):
        keys = {(int(perms[r, i]), int(volt[i, r])) for r in range(d)}
        dup += d - len(keys)
    return dup


def lift_cost(NB, N, k, D):
    """Unreached (source, vertex) pairs over the 2k base representatives (s, identity), after D rounds."""
    V = NB.shape[0]
    S = 2 * k
    R = np.zeros((S, V), dtype=bool)
    R[np.arange(S), np.arange(S) * N] = True
    for _ in range(D):
        R = R | R[:, NB].any(axis=2)
    return int(S * V - R.sum())


def lift_score(MT, inv, k, d, D, perms, volt):
    N = MT.shape[0]
    NB = lift_tables(MT, inv, k, d, perms, volt)
    return lift_cost(NB, N, k, D) + N * lift_dups(k, d, perms, volt)


def lift_anneal(MT, inv, k, d, D, deadline, rng, iters=4000):
    """Simulated annealing over voltages and matchings, with random restarts. Returns ((perms, volt), cost)."""
    N = MT.shape[0]
    best, bestc = None, 10 ** 18
    while time.monotonic() < deadline:
        perms = np.array([rng.permutation(k) for _ in range(d)], dtype=np.int64)
        volt = rng.integers(0, N, size=(k, d)).astype(np.int64)
        cur = lift_score(MT, inv, k, d, D, perms, volt)
        for t in range(iters):
            if (t & 63) == 0 and time.monotonic() >= deadline:
                break
            T = 10.0 * (0.03 ** (t / iters))
            if rng.random() < 0.15:
                r = int(rng.integers(d))
                a, b = rng.choice(k, 2, replace=False)
                p2 = perms.copy()
                p2[r, a], p2[r, b] = perms[r, b], perms[r, a]
                v2 = volt
            else:
                p2 = perms
                v2 = volt.copy()
                i = int(rng.integers(k))
                r = int(rng.integers(d))
                v2[i, r] = int(rng.integers(N))
            c = lift_score(MT, inv, k, d, D, p2, v2)
            if c <= cur or rng.random() < math.exp(-(c - cur) / T):
                perms, volt, cur = p2, v2, c
                if cur < bestc:
                    bestc = cur
                    best = (perms.copy(), volt.copy())
                    if cur == 0:
                        return best, 0
    return best, bestc


def lift_specs():
    """(k, group order N, name, builder) with 2*k*N >= 688, so every lift beats the 684-vertex record."""
    specs = []
    for m, kk, lam in metacyclic_candidates(172, 200, 3):
        specs.append((2, m * kk, f'meta {m}/{kk}/{lam}', lambda m=m, kk=kk, lam=lam: group_meta(m, kk, lam)))
    for q, kk in [(29, 7), (31, 6)]:
        specs.append((2, q * kk, f'AGL(1,{q}) sub {kk}', lambda q=q, kk=kk: group_agl(q, kk)))
    specs.append((3, 120, 'SL(2,5)', lambda: group_sl2(5)))
    specs.append((3, 125, 'Heis 5', lambda: group_heis(5)))
    for m, kk, lam in metacyclic_candidates(115, 125, 2):
        specs.append((3, m * kk, f'meta {m}/{kk}/{lam}', lambda m=m, kk=kk, lam=lam: group_meta(m, kk, lam)))
    for m, kk, lam in metacyclic_candidates(86, 100, 2):
        specs.append((4, m * kk, f'meta {m}/{kk}/{lam}', lambda m=m, kk=kk, lam=lam: group_meta(m, kk, lam)))
    for m, kk, lam in metacyclic_candidates(70, 80, 1):
        specs.append((5, m * kk, f'meta {m}/{kk}/{lam}', lambda m=m, kk=kk, lam=lam: group_meta(m, kk, lam)))
    return specs


def run_lifts(d, D, seed, deadline):
    """Stage 1. Returns the largest valid lift (n, edges) found by the deadline, or None."""
    rng = np.random.default_rng(seed + 12345)
    specs = sorted(lift_specs(), key=lambda s: 2 * s[0] * s[1])
    best, bestn = None, 0
    for idx, (k, N0, name, builder) in enumerate(specs):
        now = time.monotonic()
        if now >= deadline:
            break
        if 2 * k * N0 <= bestn:
            continue
        end = now + (deadline - now) / (len(specs) - idx)
        try:
            MT, inv = builder()
            N = MT.shape[0]
            (perms, volt), c = lift_anneal(MT, inv, k, d, D, end, rng)
            if perms is None or c != 0:
                continue
            NB = lift_tables(MT, inv, k, d, perms, volt)
            n = 2 * k * N
            edges = [(u, int(w)) for u in range(k * N) for w in NB[u]]
            if n > bestn and lib.is_valid(n, edges, d, D):
                best, bestn = (n, edges), n
        except Exception:
            continue
    return best


# ------------------------------------------------------------------ STAGE 2: Haar-graph search (fallback path)

def _cover(MT, N, P):
    cov = np.zeros(N, dtype=bool)
    cov[MT[P[:, None], P[None, :]].ravel()] = True
    return cov


def _pairs(MT, inv, S):
    Si = inv[S]
    return MT[Si[:, None], S[None, :]].ravel(), MT[S[:, None], Si[None, :]].ravel()


def cost(MT, inv, S):
    N = MT.shape[0]
    return sum(N - int(_cover(MT, N, np.unique(P)).sum()) for P in _pairs(MT, inv, S))


def batch_costs(MT, inv, S, i, X):
    N = MT.shape[0]
    K = len(X)
    rest = np.delete(S, i)
    total = np.zeros(K, dtype=np.int64)
    offs = (np.arange(K, dtype=np.int64) * N)[:, None]
    ri = inv[rest]
    for side in (0, 1):
        F = np.unique(MT[ri[:, None], rest[None, :]] if side == 0 else MT[rest[:, None], ri[None, :]])
        base = _cover(MT, N, F)
        xi = inv[X]
        if side == 0:
            Q = np.concatenate([MT[xi[:, None], rest[None, :]], MT[ri[None, :], X[:, None]]], axis=1)
        else:
            Q = np.concatenate([MT[X[:, None], ri[None, :]], MT[rest[None, :], xi[:, None]]], axis=1)
        W = np.concatenate([MT[Q[:, :, None], F[None, None, :]].reshape(K, -1),
                            MT[F[None, None, :], Q[:, :, None]].reshape(K, -1),
                            MT[Q[:, :, None], Q[:, None, :]].reshape(K, -1)], axis=1)
        new = ~base[W]
        flat = (W + offs)[new]
        cnt = np.bincount(flat, minlength=K * N).reshape(K, N)
        total += N - int(base.sum()) - (cnt > 0).sum(axis=1)
    return total


def one_swap_scan(MT, inv, S, deadline, chunk=512):
    N = MT.shape[0]
    best, bestS = 10 ** 9, None
    for i in range(len(S)):
        rest = np.delete(S, i)
        for lo in range(0, N, chunk):
            if time.monotonic() >= deadline:
                return best, bestS
            X = np.arange(lo, min(N, lo + chunk), dtype=np.int32)
            X = X[~np.isin(X, rest)]
            if len(X) == 0:
                continue
            cs = batch_costs(MT, inv, S, i, X)
            j = int(np.argmin(cs))
            if cs[j] < best:
                best, bestS = int(cs[j]), S.copy()
                bestS[i] = X[j]
    return best, bestS


def proposals(MT, inv, S, i, rng, K):
    N = MT.shape[0]
    rest = np.delete(S, i)
    npr = K // 2
    a = rest[rng.integers(0, len(rest), npr)]
    b = S[rng.integers(0, len(S), npr)]
    prod = np.where(rng.integers(0, 2, npr) == 0, MT[inv[a], b], MT[a, b])
    xr = rng.integers(0, N, K - npr)
    X = np.concatenate([prod, xr]).astype(np.int32)
    return X[~np.isin(X, rest)]


def search(MT, inv, d, S0, deadline, rng, K=24, temp=0.45, patience=4000):
    N = MT.shape[0]
    S0 = None if S0 is None else np.array(S0, dtype=np.int32)
    best, bestc = None, 10 ** 9
    S, cur, since = S0.copy() if S0 is not None else None, None, 0

    def random_set():
        return np.concatenate([[0], rng.choice(np.arange(1, N), d - 1, replace=False)]).astype(np.int32)

    if S0 is not None:
        c0 = cost(MT, inv, S0)
        best, bestc = S0.copy(), c0
        if c0 == 0:
            return best, 0
        c1, S1 = one_swap_scan(MT, inv, S0, time.monotonic() + 0.25 * max(0.0, deadline - time.monotonic()))
        if S1 is not None and c1 < bestc:
            best, bestc, S = S1.copy(), c1, S1.copy()
            if c1 == 0:
                return best, 0
    while time.monotonic() < deadline:
        if S is None:
            if S0 is not None and rng.random() < 0.5:
                S = S0.copy()
                for i in rng.choice(d, 2, replace=False):
                    S[i] = rng.integers(N)
                if len(set(S.tolist())) < d:
                    S = random_set()
            else:
                S = random_set()
        if cur is None:
            cur = cost(MT, inv, S)
            since = 0
            if cur < bestc:
                best, bestc = S.copy(), cur
            if cur == 0:
                return best, 0
        i = int(rng.integers(d))
        X = proposals(MT, inv, S, i, rng, K)
        if len(X) == 0:
            continue
        cs = batch_costs(MT, inv, S, i, X)
        j = int(np.argmin(cs + rng.random(len(cs)) * 0.5))
        delta = int(cs[j]) - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S[i] = X[j]
            cur = int(cs[j])
            if cur < bestc:
                best, bestc, since = S.copy(), cur, 0
                if cur == 0:
                    return best, 0
            elif delta < 0:
                since = 0
        since += 1
        if since > patience:
            S, cur = None, None
    return best, bestc


def haar_edges(MT, S):
    """Haar graph edges: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def run(d, D, seed, time_limit, plan, fallback):
    """Stage 2 driver. plan: list of (name, order, builder, S0 or None, weight), sorted by order."""
    t0 = time.monotonic()
    deadline_all = t0 + 0.85 * time_limit
    rng = np.random.default_rng(seed)
    total_w = sum(e[4] for e in plan)
    best_g, best_n = None, 0
    for name, order, builder, S0, w in plan:
        now = time.monotonic()
        if now >= deadline_all:
            break
        if 2 * order <= best_n:
            total_w -= w
            continue
        end = now + (deadline_all - now) * w / total_w
        total_w -= w
        try:
            MT, inv = builder()
            S, c = search(MT, inv, d, S0, end, rng)
        except Exception:
            continue
        if S is not None and c == 0:
            g = checked(MT, S, d, D)
            if g is not None and g[0] > best_n:
                best_g, best_n = g, g[0]
    try:
        MT, inv = fallback[0]()
        g = checked(MT, fallback[1], d, D)
        if g is not None and (best_g is None or g[0] > best_n):
            best_g = g
    except Exception:
        pass
    if best_g is not None:
        return best_g
    return trivial(d, D)


# ============================================================================= cell: d6D5

TARGET = (6, 5)
NEAR = {(117, 3), (71, 5)}


def _plan():
    E = []
    for m, k, lam in metacyclic_candidates(331, 341, 6):
        E.append((f'meta {m}/{k}/{lam}', m * k,
                  (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), None, 0.5))
    E.append(('AGL(1,19), order 342', 342, lambda: group_agl(19), None, 1.5))
    for m, k, lam in metacyclic_candidates(342, 342, 2):
        E.append((f'meta {m}/{k}/{lam}, order 342', m * k,
                  (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), None, 1.0))
    E.append(('Heisenberg mod 7, order 343', 343, lambda: group_heis(7), None, 2.0))
    for m, k, lam in metacyclic_candidates(343, 360, 8):
        if (m, k) in NEAR:
            continue
        E.append((f'meta {m}/{k}/{lam}, order {m * k}', m * k,
                  (lambda m=m, k=k, lam=lam: group_meta(m, k, lam)), None, 1.0))
    E.append(('meta 117/3/16, order 351, 2 short', 351,
              lambda: group_meta(117, 3, 16), [0, 184, 47, 48, 65, 21], 4.0))
    E.append(('meta 71/5/5, order 355, 2 short', 355,
              lambda: group_meta(71, 5, 5), [0, 92, 218, 269, 205, 88], 4.0))
    E.append(('SL(2,5) x Z_3, order 360, 4 short', 360,
              lambda: group_times_cyclic(group_sl2(5), 3), [0, 246, 216, 211, 99, 132], 3.0))
    E.sort(key=lambda e: e[1])
    return E


PLAN = _plan()
FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    total = 0.8 * time_limit
    best, bestn = None, 0
    try:
        g = run_lifts(d, D, seed, t0 + 0.4 * total)
        if g is not None:
            best, bestn = g, g[0]
    except Exception:
        pass
    try:
        remaining = max(1.0, total - (time.monotonic() - t0))
        g = run(d, D, seed, remaining, PLAN, FALLBACK)
        if g is not None and g[0] > bestn and lib.is_valid(g[0], g[1], d, D):
            best, bestn = g, g[0]
    except Exception:
        pass
    if best is None:
        return trivial(d, D)
    return best
