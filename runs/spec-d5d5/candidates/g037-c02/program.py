import itertools
import math
import random
import time

import lib

ITERS0 = 300      # annealing steps for the first pass over the candidate pool
T_HOT = 1.5       # initial annealing temperature (in unreached-pair units)
T_COLD = 0.15     # final annealing temperature


# ----------------------------------------------------------------------------
# Baseline families (fast, always valid when they pass lib.is_valid).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Group tables. Every group is given as a multiplication table T with identity 0.
# ----------------------------------------------------------------------------

def _table(order, mul):
    return [[mul(x, g) for g in range(order)] for x in range(order)]


def _z2_table(T1):
    """Direct product G x Z_2 for a group G given by table T1; element code = 2*g + b."""
    n1 = len(T1)
    N = 2 * n1
    T = []
    for x in range(N):
        g, b = divmod(x, 2)
        row1 = T1[g]
        out = [0] * N
        for y in range(N):
            h, c = divmod(y, 2)
            out[y] = 2 * row1[h] + (b ^ c)
        T.append(out)
    return T


def _pgl2_table(p, square_only):
    """Table of PGL(2,p) (or PSL(2,p) when square_only) for prime p; identity is index 0."""
    def norm(m):
        for t in m:
            if t % p:
                iv = pow(t, p - 2, p)
                return tuple((x * iv) % p for x in m)
        return None

    els = []
    for m in itertools.product(range(p), repeat=4):
        a, b, c, d = m
        det = (a * d - b * c) % p
        if det == 0:
            continue
        if norm(m) != m:
            continue
        if square_only and pow(det, (p - 1) // 2, p) != 1:
            continue
        els.append(m)
    ident = (1, 0, 0, 1)
    els.remove(ident)
    els.insert(0, ident)
    idx = {e: i for i, e in enumerate(els)}
    T = []
    for x in els:
        a, b, c, d = x
        row = []
        for y in els:
            e, f, g, h = y
            row.append(idx[norm(((a * e + b * g) % p, (a * f + b * h) % p,
                                 (c * e + d * g) % p, (c * f + d * h) % p))])
        T.append(row)
    return T


def _sd_params(N):
    """All (m, k, r) with m*k = N giving semidirect products Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _specs(lo, hi):
    """Lazy group specifications with order in [lo, hi]."""
    specs = []
    for N in range(lo, hi + 1):
        for par in _sd_params(N):
            specs.append((N, 'sd', par))
        if N % 2 == 0:
            for par in _sd_params(N // 2):
                specs.append((N, 'z2', par))
    if lo <= 336 <= hi:
        specs.append((336, 'pgl', None))
        specs.append((336, 'z2psl', None))
    return specs


def _make_table(spec):
    N, kind, par = spec
    if kind == 'sd':
        m, k, r = par
        order, mul, _ = lib.semidirect_group(m, k, r)
        return _table(order, mul)
    if kind == 'z2':
        m, k, r = par
        order, mul, _ = lib.semidirect_group(m, k, r)
        return _z2_table(_table(order, mul))
    if kind == 'pgl':
        return _pgl2_table(7, False)
    if kind == 'z2psl':
        return _z2_table(_pgl2_table(7, True))
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley search. Vertices A_x = x and B_y = N + y, with x, y in G.
# Edge A_x -- B_{x s} for s in S, |S| = d, with identity in S WLOG.
# Left multiplication is an automorphism, so only the sources A_0 and B_0 matter.
# ----------------------------------------------------------------------------

def _unreached(N, T, invs, S, D):
    """Count (source, vertex) pairs not within distance D, for sources A_0 and B_0."""
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


def _anneal(N, T, invs, d, D, rng, iters, deadline):
    """Simulated annealing over S = {0, s_1, ..., s_{d-1}} to zero the unreached count."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.8 * time_limit, time_limit - 6.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    best = (1, [])
    best_n = 1

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2 or D < 2:
        return best

    Nmax = lib._moore_bound(d, D) // 2
    lo = max(d + 1, Nmax // 2)
    hi = Nmax
    if lo > hi:
        return best

    try:
        specs = _specs(lo, hi)
        iters = ITERS0
        best_N = 0
        while time.monotonic() < deadline and specs:
            pool = [s for s in specs if s[0] > best_N]
            if not pool:
                break
            rng.shuffle(pool)
            for spec in pool:
                if time.monotonic() >= deadline:
                    break
                N = spec[0]
                if N <= best_N:
                    continue
                T = _make_table(spec)
                if T is None:
                    continue
                invs = [T[g].index(0) for g in range(N)]
                S = _anneal(N, T, invs, d, D, rng, iters, deadline)
                if S is None:
                    continue
                edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                before = best_n
                consider(2 * N, edges)
                if best_n > before:
                    best_N = N
            iters *= 2
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
