import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley (Haar-type) search over finite groups of order N = m*kk.
#
# Groups are semidirect products Z_m x| Z_kk (r^kk = 1 mod m), which include
# cyclic, dihedral and direct-product groups. A lift has k orbits per side:
# A_{i,x} ~ B_{j,x*s} for each dart (i, j, s). Left multiplication by a group
# element is an automorphism, so only one representative per orbit needs a BFS.
# Validity then reduces to BFS from the k A-representatives and k B-representatives
# to depth D. Each BFS is vectorised with numpy bool arrays.
# ----------------------------------------------------------------------------

def _tables(m, kk, r):
    """Multiplication table T[x, y] = x*y, its transpose TT, and right inverses inv[x]."""
    N = m * kk
    powers = np.array([pow(r, b, m) for b in range(kk)], dtype=np.int64)
    x = np.arange(N, dtype=np.int64)
    A = x // kk
    B = x % kk
    a = (A[:, None] + powers[B][:, None] * A[None, :]) % m
    b = (B[:, None] + B[None, :]) % kk
    T = a * kk + b
    inv = np.argmax(T == 0, axis=1)
    TT = np.ascontiguousarray(T.T)
    return T, TT, inv


def _group_params(N):
    """All (m, kk, r) with m*kk = N, m >= 2, describing Z_m x| Z_kk."""
    out = []
    for kk in range(1, min(N, 24) + 1):
        if N % kk:
            continue
        m = N // kk
        if m < 2:
            continue
        if kk == 1:
            out.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, kk, m) == 1 % m:
                out.append((m, kk, r))
    return out


def _fb(darts, TT, inv):
    """Attach precomputed forward and backward permutations to each dart."""
    return [(i, j, TT[s], TT[inv[s]]) for i, j, s in darts]


def _unreached(fdarts, N, k, D, side, src):
    """Number of vertices not reached within D steps from the representative (src, 0) on `side`."""
    vis = [np.zeros((k, N), dtype=bool), np.zeros((k, N), dtype=bool)]
    cur = np.zeros((k, N), dtype=bool)
    cur[src, 0] = True
    vis[side][src, 0] = True
    cs = side
    for _ in range(D):
        nxt = np.zeros((k, N), dtype=bool)
        if cs == 0:
            for i, j, fp, _bp in fdarts:
                if cur[i].any():
                    nxt[j][fp] |= cur[i]
        else:
            for i, j, _fp, bp in fdarts:
                if cur[j].any():
                    nxt[i][bp] |= cur[j]
        ns = 1 - cs
        nxt &= ~vis[ns]
        vis[ns] |= nxt
        cur = nxt
        cs = ns
        if not cur.any():
            break
    return 2 * k * N - int(vis[0].sum()) - int(vis[1].sum())


def _total(fdarts, N, k, D):
    """Total number of unreached (representative, vertex) pairs. Zero means diameter <= D."""
    s = 0
    for i in range(k):
        s += _unreached(fdarts, N, k, D, 0, i)
    for j in range(k):
        s += _unreached(fdarts, N, k, D, 1, j)
    return s


def _run_search(d, D, k, N, params, rng, deadline, iters):
    """Simulated annealing over darts for one random group. Returns (darts, T) on success, else None."""
    m, kk, r = rng.choice(params)
    T, TT, inv = _tables(m, kk, r)
    darts = []
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        for i in range(k):
            darts.append([i, perm[i], rng.randrange(N)])
    cur = _total(_fb(darts, TT, inv), N, k, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() >= deadline:
            break
        temp = 1.5 * (1.0 - it / iters) + 0.05
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            darts[idx][2] = rng.randrange(N)
            nc = _total(_fb(darts, TT, inv), N, k, D)
            if nc <= cur or rng.random() < math.exp(-(nc - cur) / temp):
                cur = nc
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            nc = _total(_fb(darts, TT, inv), N, k, D)
            if nc <= cur or rng.random() < math.exp(-(nc - cur) / temp):
                cur = nc
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    if cur == 0:
        return darts, T
    return None


def _edges(darts, T, N, k):
    """Build the lifted graph: vertices A_i,x = i*N + x and B_j,y = (k+j)*N + y."""
    E = set()
    for i, j, s in darts:
        col = T[:, s].tolist()
        for x in range(N):
            E.add((i * N + x, (k + j) * N + col[x]))
    return 2 * k * N, sorted(E)


def _attempt(N, params, d, D, rng, att_end):
    """Several annealing restarts at order N with a randomly chosen orbit count k."""
    k = 1 if rng.random() < 0.55 else 2
    while time.monotonic() < att_end:
        res = _run_search(d, D, k, N, params, rng, att_end, 500)
        if res is not None:
            return k, res[0], res[1]
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit

    if D <= 0 or d <= 0:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, optimal for D = 2 and valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Diameter-3 seeds (cheap and valid for any D >= 3).
    if lib.is_prime_power(d - 1):
        try:
            n, e = lib.projective_plane_incidence(d - 1)
            consider(n, e)
        except Exception:
            pass
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            n, e = lib.araujo_lopez_graph(d - 2)
            consider(n, e)
        except Exception:
            pass

    rng = random.Random(seed * 1000003 + d * 97 + D)

    # Exponential search and bisection over the group order N.
    # lo is the largest N with a success; hi is the smallest N that failed.
    lo = max(2, best[0] // 4)
    hi = None
    step = 1
    cache = {}
    while time.monotonic() < deadline:
        if hi is None:
            N = lo + step
        elif hi - lo > 1:
            N = (lo + hi) // 2
        else:
            # Boundary reached: reset and retry lo + 1 with fresh randomness.
            hi = None
            step = 1
            continue

        if N not in cache:
            if len(cache) > 256:
                cache.clear()
            cache[N] = _group_params(N)
        params = cache[N]
        if not params:
            if hi is None:
                step *= 2
            else:
                hi = N
            continue

        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0:
            break
        budget = min(3.0, max(0.3, 0.03 * remaining))
        att_end = min(deadline, now + budget)
        res = _attempt(N, params, d, D, rng, att_end)

        if res is not None:
            k, darts, T = res
            n, e = _edges(darts, T, N, k)
            consider(n, e)
            lo = max(lo, N)
            if hi is None:
                step = min(step * 2, 1 << 20)
        else:
            if hi is None or N < hi:
                hi = N

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
