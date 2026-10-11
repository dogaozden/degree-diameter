import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Small helpers: D = 3 projective-plane baseline.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over groups.
#
# Vertices A_x and B_y (x, y in G) with A_x ~ B_{x g} for g in S, |S| = d.
# Left translation is an automorphism, so checking eccentricities of A_0 and
# B_0 suffices for the diameter. S is normalised to contain the identity.
#
# NEW in this version: exact matrix groups over finite fields,
#   SL(2,7) (order 336), GL(2,4) (order 180), GL(3,2) (order 168),
#   SL(2,5) (order 120).
# Built from lib.GF, with determinant tests and a full multiplication table.
# Non-abelian groups of this type are not covered by the semidirect
# parametrisation used in the annealing branch.
# ----------------------------------------------------------------------------

MATRIX_CLIMB = 400     # hill-climb steps per restart for matrix groups
CLIMB_ITERS = 300      # hill-climb steps per group (semidirect sweep)
ANNEAL_ITERS = 600     # annealing steps for multi-base lifts
BAND_EXTRA = 12        # sweep window above the lower bound for bi-Cayley orders
MAX_GROUPS = 8         # semidirect groups tried per order N
_BIG = 10 ** 9
_TABLE_CACHE = {}
_LIN_CACHE = {}

# (q, n, special) -> order. special=True means SL(n, q), else GL(n, q).
_LIN_SPECS = {
    (7, 2, True): 336,   # SL(2,7)
    (4, 2, False): 180,  # GL(2,4)
    (2, 3, False): 168,  # GL(3,2) = PSL(2,7)
    (5, 2, True): 120,   # SL(2,5)
}


def _det(F, M, n):
    """Determinant of the n x n matrix M (flat tuple, row-major) over field F."""
    A = [list(M[i * n:(i + 1) * n]) for i in range(n)]
    det = 1
    for c in range(n):
        piv = next((r for r in range(c, n) if A[r][c]), None)
        if piv is None:
            return 0
        if piv != c:
            A[c], A[piv] = A[piv], A[c]
            det = F.neg(det)
        det = F.mul(det, A[c][c])
        inv = F.inv(A[c][c])
        for r in range(c + 1, n):
            if A[r][c]:
                f = F.mul(A[r][c], inv)
                for k in range(c, n):
                    A[r][k] = F.sub(A[r][k], F.mul(f, A[c][k]))
    return det


def _linear_group(q, n, special):
    """Return (order, T, invs) for GL(n,q) or SL(n,q); identity has index 0.

    T[x][g] = index of x*g, invs[g] = index of g^-1.
    """
    key = (q, n, special)
    hit = _LIN_CACHE.get(key)
    if hit is not None:
        return hit
    F = lib.GF(q)
    ADD = F.add_table.tolist()
    MUL = F.mul_table.tolist()
    I = tuple(int(i == j) for i in range(n) for j in range(n))
    els = [I]
    for M in itertools.product(range(q), repeat=n * n):
        if M == I:
            continue
        dt = _det(F, M, n)
        if (dt == 1) if special else (dt != 0):
            els.append(M)
    idx = {M: i for i, M in enumerate(els)}
    N = len(els)

    def mm(A, B):
        C = []
        for i in range(n):
            for j in range(n):
                s = 0
                for k in range(n):
                    s = ADD[s][MUL[A[i * n + k]][B[k * n + j]]]
                C.append(s)
        return tuple(C)

    T = [[idx[mm(els[x], els[g])] for g in range(N)] for x in range(N)]
    invs = [row.index(0) for row in T]   # g * h = identity (index 0)
    val = (N, T, invs)
    if len(_LIN_CACHE) >= 8:
        _LIN_CACHE.clear()
    _LIN_CACHE[key] = val
    return val


# ----------------------------------------------------------------------------
# Semidirect-product tables (Z_m x|_r Z_k), used by the sweep branch.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(m, k, r):
    """Cached (order, mul, T, invs) for Z_m x|_r Z_k."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, mul, T, invs)
    if len(_TABLE_CACHE) >= 48:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Count vertex pairs (source, target) not within distance D, from A_0 and B_0."""
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _climb(N, T, invs, d, D, rng, iters, deadline):
    """Hill-climb a connection set S (identity fixed as one element, WLOG) to zero unreached pairs.

    Sideways moves are accepted, so the walk can drift across plateaus.
    """
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur:
            S, cur = S2, v
    return S if cur == 0 else None


def _matrix_phase(d, D, cur_n, moore, rng, deadline):
    """Try exact matrix groups whose bi-Cayley lift (2N vertices) beats cur_n.

    Larger groups are tried first. Time is shared among eligible groups.
    Returns (n, edges) or None.
    """
    eligible = sorted((s for s, N in _LIN_SPECS.items() if cur_n < 2 * N <= moore),
                      key=lambda s: -_LIN_SPECS[s])
    for i, spec in enumerate(eligible):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(eligible) - i)
        N = _LIN_SPECS[spec]
        _, T, invs = _linear_group(*spec)
        while time.monotonic() < slice_end:
            S = _climb(N, T, invs, d, D, rng, MATRIX_CLIMB, slice_end)
            if S is not None:
                return 2 * N, [(x, N + T[x][g]) for x in range(N) for g in S]
    return None


# ----------------------------------------------------------------------------
# General multi-base voltage lifts over semidirect products, annealed.
# ----------------------------------------------------------------------------

def _right_perm(mul, G, s):
    """Permutation g -> g*s of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best  # K_{d,d} meets the Moore bound 2d for D = 2

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Phase 1: exact non-abelian matrix groups (new in this version).
    if best[0] < moore:
        res = _matrix_phase(d, D, best[0], moore, rng, start + 0.6 * budget)
        if res is not None:
            consider(res[0], res[1])

    # Phase 2: semidirect bi-Cayley sweep and multi-base annealing.
    ks = (2, 3)
    sweep_next = None
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]

        if rng.random() < 0.6:
            lo = n_best // 2 + 1
            if lo > moore // 2:
                break
            if sweep_next is None or sweep_next < lo or sweep_next > lo + BAND_EXTRA:
                sweep_next = lo
            N = sweep_next
            sweep_next += 1
            groups = _groups(N)
            rng.shuffle(groups)
            found = None
            for m, k2, r in groups[:MAX_GROUPS]:
                if time.monotonic() > deadline:
                    break
                _, _, T, invs = _tables(m, k2, r)
                S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
                if S is not None:
                    found = (T, S)
                    break
            if found is not None:
                T, S = found
                edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                consider(2 * N, edges)
        else:
            k = rng.choice(ks)
            lo = n_best // (2 * k) + 1
            if 2 * k * lo > moore:
                continue
            G = lo + rng.randrange(max(2, lo // 10))
            if G < 2:
                continue
            m, k2, r = rng.choice(_groups(G))
            order, mul, _ = lib.semidirect_group(m, k2, r)
            res = _anneal(d, D, k, order, mul, rng, deadline, ANNEAL_ITERS)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
