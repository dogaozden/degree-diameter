import math
import random
import time

import lib

ITERS = 500                 # annealing steps per (base matrix, group) try
T_HOT = 1.5                 # initial annealing temperature (unreached-pair units)
T_COLD = 0.15               # final annealing temperature
GROUPS_PER_TRY = 6          # groups tried per chosen order N
ATTEMPT_SECONDS = 8.0       # wall-clock cap per (N, group) annealing run
A_CHOICES = (2, 2, 3, 2, 1) # number of base vertices per side (lift has 2*a*N vertices)


# ----------------------------------------------------------------------------
# Safe baselines (always checked with lib.is_valid before use).
# ----------------------------------------------------------------------------

def _baseline(d, D):
    """K_{d,d} (diameter 2), or K_2 when D = 1 or d = 1."""
    if D == 0 or d == 0:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    n = 2 * d
    return n, [(i, d + j) for i in range(d) for j in range(d)]


# ----------------------------------------------------------------------------
# Multigraph base structure: a x a matrices of nonnegative ints with all row
# and column sums equal to d. Entry M[i][j] = number of darts from base
# vertex A_i to base vertex B_j.
# ----------------------------------------------------------------------------

def _mats(a, d):
    out = []

    def rec_row(r, colrem, acc):
        if r == a:
            if not any(colrem):
                out.append(tuple(acc))
            return

        def rec_cell(j, rem, row, cr):
            if j == a:
                if rem == 0:
                    rec_row(r + 1, cr, acc + [tuple(row)])
                return
            for x in range(min(rem, cr[j]) + 1):
                cr2 = cr[:]
                cr2[j] -= x
                rec_cell(j + 1, rem - x, row + [x], cr2)

        rec_cell(0, d, [], colrem)

    rec_row(0, [d] * a, [])
    return out


def _groups(N):
    """Semidirect parameters (m, k, r) giving groups Z_m x|_r Z_k of order N (cyclic included)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(N, m, k, r):
    _, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    Ti = [inv(g) for g in range(N)]
    return T, Ti


# ----------------------------------------------------------------------------
# Voltage lift search. Vertices: A_{i,x} = i*N + x and B_{j,y} = a*N + j*N + y.
# Dart (i, j, g) joins A_{i,x} to B_{j, x*g} for all x. Left multiplication by
# any group element is an automorphism, so the diameter is at most D iff every
# base vertex (A_{i,e}, B_{j,e}) has eccentricity at most D.
# ----------------------------------------------------------------------------

def _unreached(N, a, T, Ti, darts, D):
    nA = a * N
    V = 2 * nA
    dA = [[] for _ in range(a)]
    dB = [[] for _ in range(a)]
    for i, j, g in darts:
        dA[i].append((j, g))
        dB[j].append((i, Ti[g]))
    sources = [i * N for i in range(a)] + [nA + j * N for j in range(a)]
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < nA:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in dA[i]:
                        w = nA + j * N + row[g]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    j, y = divmod(u - nA, N)
                    row = T[y]
                    for i, gi in dB[j]:
                        w = i * N + row[gi]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - cnt
    return total


def _anneal(N, a, d, T, Ti, mats, D, rng, iters, deadline):
    M = rng.choice(mats)
    darts = []
    for i in range(a):
        for j in range(a):
            for g in rng.sample(range(N), M[i][j]):
                darts.append([i, j, g])
    if not darts:
        return None
    cur = _unreached(N, a, T, Ti, darts, D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        k = rng.randrange(len(darts))
        i, j, g = darts[k]
        used = {gg for (ii, jj, gg) in darts if ii == i and jj == j and gg != g}
        newg = rng.randrange(N)
        if newg in used or newg == g:
            continue
        old = darts[k]
        darts[k] = [i, j, newg]
        v = _unreached(N, a, T, Ti, darts, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            darts[k] = old
    if cur == 0:
        return darts
    return None


def _edges(N, a, T, darts):
    nA = a * N
    edges = []
    for i, j, g in darts:
        for x in range(N):
            edges.append((i * N + x, nA + j * N + T[x][g]))
    return 2 * nA, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit - 1.0
    rng = random.Random(seed)

    if d <= 0 or D < 0:
        return 1, []

    best_n, best_e = 1, []

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    bn, be = _baseline(d, D)
    consider(bn, be)

    # Record-matching constructions for D = 3.
    if D == 3:
        if lib.is_prime_power(d - 1):
            n, e = lib.projective_plane_incidence(d - 1)
            consider(n, e)
            return best_n, best_e
        if d >= 5 and lib.is_prime_power(d - 2):
            try:
                n, e = lib.araujo_lopez_graph(d - 2)
                consider(n, e)
            except (ValueError, ZeroDivisionError):
                pass

    if d < 2 or D < 2:
        return best_n, best_e

    moore = lib._moore_bound(d, D)
    mats_cache = {}

    def mats_for(a):
        if a not in mats_cache:
            mats_cache[a] = _mats(a, d)
        return mats_cache[a]

    while time.monotonic() < deadline:
        feasible = [a for a in (1, 2, 3)
                    if max(d, best_n // (2 * a) + 1) <= moore // (2 * a)]
        if not feasible:
            break
        a = rng.choice(A_CHOICES)
        if a not in feasible:
            a = rng.choice(feasible)
        mats = mats_for(a)
        if not mats:
            continue

        Nmax = moore // (2 * a)
        lo = max(d, best_n // (2 * a) + 1)
        hi = Nmax
        if lo > hi:
            continue
        # Bias toward the top of the feasible range.
        N = hi - int((rng.random() ** 2) * (hi - lo))

        groups = _groups(N)
        rng.shuffle(groups)
        found = None
        for m, k, r in groups[:GROUPS_PER_TRY]:
            now = time.monotonic()
            if now >= deadline:
                break
            att_deadline = min(deadline, now + ATTEMPT_SECONDS)
            T, Ti = _tables(N, m, k, r)
            darts = _anneal(N, a, d, T, Ti, mats, D, rng, ITERS, att_deadline)
            if darts is not None:
                found = (T, darts)
                break
        if found is not None:
            T, darts = found
            n, e = _edges(N, a, T, darts)
            consider(n, e)

    if not lib.is_valid(best_n, best_e, d, D):
        return 1, []
    return best_n, best_e
