import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baselines: record AL graph, projective plane incidence, and K_{d,d}.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Phase A (parent family): bi-Cayley graphs over non-abelian groups, a_x ~ b_{xs}.
# Requires S S^-1 = G, which is necessary for same-side distance <= 2.
# ----------------------------------------------------------------------------

def _delta(cnt, S, skip, v, sign, Q):
    change = 0
    for j, b in enumerate(S):
        if j == skip:
            continue
        for y in (Q[v][b], Q[b][v]):
            if sign > 0:
                if cnt[y] == 0:
                    change -= 1
                cnt[y] += 1
            else:
                cnt[y] -= 1
                if cnt[y] == 0:
                    change += 1
    return change


def _anneal_cayley(N, d, Q, rng, deadline, moves):
    S = [0] + rng.sample(range(1, N), d - 1)
    cnt = [0] * N
    unc = N - 1
    for j in range(d):
        for k in range(d):
            if j != k:
                y = Q[S[j]][S[k]]
                if cnt[y] == 0:
                    unc -= 1
                cnt[y] += 1
    if unc == 0:
        return S
    for it in range(moves):
        if (it & 255) == 0 and time.monotonic() >= deadline:
            return None
        T = 0.5 * (0.02 ** (it / moves))
        idx = rng.randrange(1, d)
        x = rng.randrange(1, N)
        if x in S:
            continue
        old = S[idx]
        delta = _delta(cnt, S, idx, old, -1, Q) + _delta(cnt, S, idx, x, 1, Q)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[idx] = x
            unc += delta
            if unc == 0:
                return S
        else:
            _delta(cnt, S, idx, x, -1, Q)
            _delta(cnt, S, idx, old, 1, Q)
    return None


def _specs(N, rng, cap=16):
    cands = []
    for k in range(2, N + 1):
        if N % k:
            continue
        a = N // k
        if a == 1:
            continue
        for r in range(1, a):
            if math.gcd(r, a) == 1 and pow(r, k, a) == 1:
                cands.append((a, k, r))
    rng.shuffle(cands)
    return [("cyc",)] + cands[:cap]


def _tables(spec, N):
    if spec[0] == "cyc":
        _, mul, inv = lib.cyclic_group(N)
    else:
        a, k, r = spec
        _, mul, inv = lib.semidirect_group(a, k, r)
    M = [[mul(x, y) for y in range(N)] for x in range(N)]
    I = [inv(x) for x in range(N)]
    Q = [[M[x][I[y]] for y in range(N)] for x in range(N)]
    return M, Q


def _search_N(N, d, rng, deadline):
    specs = _specs(N, rng)
    cache = {}
    rounds = 0
    while time.monotonic() < deadline:
        spec = specs[rounds % len(specs)]
        rounds += 1
        if spec not in cache:
            try:
                cache[spec] = _tables(spec, N)
            except Exception:
                cache[spec] = None
        tab = cache[spec]
        if tab is None:
            continue
        M, Q = tab
        S = _anneal_cayley(N, d, Q, rng, deadline, 30000)
        if S is not None:
            return S, M
    return None


def _edges_from(N, d, S, M):
    return [(x, N + M[x][s]) for x in range(N) for s in S]


def _phase_a(d, D, best, rng, deadline):
    bound = d * (d - 1) + 1
    N = best[0] // 2 + 1
    while N <= bound and N >= d and time.monotonic() < deadline:
        res = _search_N(N, d, rng, deadline)
        if res is None:
            break
        S, M = res
        n, e = 2 * N, _edges_from(N, d, S, M)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
        N += 1
    return best


# ----------------------------------------------------------------------------
# Phase B (new): multi-orbit bi-Cayley graphs over Z_N.
#
# The graph has k orbits per side. A-vertex (g, i) and B-vertex (h, j) are
# joined iff h - g lies in T[i][j] (a set of shifts in Z_N). With the balanced
# size matrix M[i][j] (row and column sums equal d), every vertex has degree d.
# Same-side pairs need k*N <= d(d-1)+1, so the order can reach
# 2*k*N <= 2(d^2-d+1) for any k.
#
# Verification uses translation symmetry: the map (g, block) -> (g - c, block)
# is an automorphism, so the diameter is <= 3 iff every vertex within distance 3
# of the 2k sources A(0,i), B(0,j) is reached. Each ball is computed with
# N-bit integers: shifting a set by t is a bit-rotation.
#
# Search: simulated annealing over the shift sets, minimising the total number
# of unreached (source, vertex) pairs. A round-robin over candidate (k, N)
# pairs with growing time slices shares the budget.
# ----------------------------------------------------------------------------

def _balanced_sizes(k, d):
    """k x k matrix of nonnegative sizes with every row and column summing to d."""
    base, rem = divmod(d, k)
    return [[base + (1 if (j - i) % k < rem else 0) for j in range(k)] for i in range(k)]


def _rot(x, t, N, full):
    """Shift the N-bit set x by +t (element g goes to g + t mod N)."""
    if t == 0:
        return x
    return ((x << t) | (x >> (N - t))) & full


def _step(cur, T, k, N, full, fwd):
    """One walk step. fwd: A-blocks -> B-blocks (shift +t). Otherwise B -> A (shift -t)."""
    out = [0] * k
    if fwd:
        for i in range(k):
            x = cur[i]
            if x:
                for j in range(k):
                    o = 0
                    for t in T[i][j]:
                        o |= _rot(x, t, N, full)
                    out[j] |= o
    else:
        for j in range(k):
            y = cur[j]
            if y:
                for i in range(k):
                    for t in T[i][j]:
                        out[i] |= _rot(y, (N - t) % N, N, full)
    return out


def _unreached(T, k, N, full, side, b):
    """Number of vertices at distance > 3 from the source (side, block b, element 0)."""
    cur = [0] * k
    cur[b] = 1
    levels = [cur]
    fwd = (side == 0)
    for _ in range(3):
        cur = _step(cur, T, k, N, full, fwd)
        levels.append(cur)
        fwd = not fwd
    # levels 0 and 2 lie on the source side, levels 1 and 3 on the other side.
    same = [levels[0][x] | levels[2][x] for x in range(k)]
    other = [levels[1][x] | levels[3][x] for x in range(k)]
    return 2 * k * N - sum(v.bit_count() for v in same) - sum(v.bit_count() for v in other)


def _cost(T, k, N, full):
    tot = 0
    for b in range(k):
        tot += _unreached(T, k, N, full, 0, b)
        tot += _unreached(T, k, N, full, 1, b)
    return tot


def _anneal_orbits(k, N, sizes, rng, deadline, moves):
    """Find shift sets T[i][j] (sizes[i][j] distinct elements of Z_N) with diameter <= 3."""
    full = (1 << N) - 1
    T = [[rng.sample(range(N), sizes[i][j]) for j in range(k)] for i in range(k)]
    cur = _cost(T, k, N, full)
    if cur == 0:
        return T
    for it in range(moves):
        if (it & 127) == 0 and time.monotonic() >= deadline:
            return None
        temp = 1.5 * (0.02 ** (it / moves))
        i = rng.randrange(k)
        j = rng.randrange(k)
        if not T[i][j]:
            continue
        p = rng.randrange(len(T[i][j]))
        old = T[i][j][p]
        new = rng.randrange(N)
        if new in T[i][j]:
            continue
        T[i][j][p] = new
        c = _cost(T, k, N, full)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur = c
            if cur == 0:
                return T
        else:
            T[i][j][p] = old
    return None


def _edges(k, N, T):
    """A-vertex (g, i) is index i*N+g; B-vertex (h, j) is index k*N + j*N + h."""
    edges = []
    for i in range(k):
        for g in range(N):
            a = i * N + g
            for j in range(k):
                for t in T[i][j]:
                    edges.append((a, k * N + j * N + (g + t) % N))
    return 2 * k * N, edges


def _phase_b(d, D, best, rng, deadline):
    bound = d * (d - 1) + 1
    best_m = best[0] // 2
    cap = min(bound, best_m + 12)
    cands = []
    for k in range(1, min(d, 8) + 1):
        sizes = _balanced_sizes(k, d)
        smax = max(max(r) for r in sizes)
        for N in range(best_m // k + 1, cap // k + 1):
            if N >= smax and best_m < k * N <= bound:
                cands.append((k * N, k, N, sizes))
    cands.sort(key=lambda c: c[0])
    pending = cands
    slice_s = 0.5
    while pending and time.monotonic() < deadline:
        for c in list(pending):
            if time.monotonic() >= deadline:
                break
            if c[0] <= best_m:
                continue
            _, k, N, sizes = c
            sl = min(deadline, time.monotonic() + slice_s)
            T = _anneal_orbits(k, N, sizes, rng, sl, 20000)
            if T is not None:
                n, e = _edges(k, N, T)
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
                    best_m = n // 2
        pending = [c for c in pending if c[0] > best_m]
        slice_s *= 1.5
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    if D < 3 or d < 2:
        return best

    try:
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n_a, e_a = lib.araujo_lopez_graph(d - 2)
                if n_a > best[0] and lib.is_valid(n_a, e_a, d, D):
                    best = (n_a, e_a)
            except Exception:
                pass
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg
    except Exception:
        pass

    try:
        best = _phase_a(d, D, best, rng, start + 0.25 * total)
    except Exception:
        pass

    try:
        best = _phase_b(d, D, best, rng, start + total)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
