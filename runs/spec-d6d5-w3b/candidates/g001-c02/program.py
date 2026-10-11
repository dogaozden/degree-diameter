"""Bi-Cayley lifts over non-abelian groups (diameter search), with a safe fallback.

For D >= 4, the search samples a group G of order N, where N is chosen so that
2*k*N just exceeds the current best order. The graph has k base vertices per side,
A_i,g = i*N+g and B_j,h = (k+j)*N+h, with darts (i, j, s) joining A_i,g to B_j,g*s.
Each dart layer is a permutation of the k base vertices, so the lift is d-regular.
Because left multiplication is an automorphism, diameter <= D only needs checking
from one representative per base class, which keeps each cost evaluation cheap.
The groups come from semidirect products Z_m x| Z_k and from PSL(2,7) and SL(2,7).
Simulated annealing over voltages and layer permutations drives the cost (uncovered
pairs) to zero. Every returned graph is checked with lib.is_valid, and the program
falls back to the best valid baseline (projective plane, Araujo-Pardo-Lopez, or K_{d,d}).
"""
import itertools
import math
import random
import time

import numpy as np

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Baselines (valid for D >= 3 or D >= 2).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """PG(2, q) incidence for the largest prime power q <= d-1 (capped for speed)."""
    for q in range(min(d - 1, 13), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Group tables: R[s, g] = index of g*s, with identity-free indexing.
# ----------------------------------------------------------------------------

def _semidirect_table(m, k2, r):
    """Z_m x| Z_k2 with (a,b)*(c,d) = (a + r^b c, b + d); element (a,b) coded as a*k2+b."""
    N = m * k2
    pw = np.array([pow(r, b, m) for b in range(k2)], dtype=np.int64)
    g = np.arange(N, dtype=np.int64)
    A = g // k2
    B = g % k2
    R = np.empty((N, N), dtype=np.int64)
    for s in range(N):
        c, dd = divmod(s, k2)
        R[s] = ((A + pw[B] * c) % m) * k2 + (B + dd) % k2
    return N, 0, R


def _canon_py(p, psl, x0, x1, x2, x3):
    c = ((x0 * p + x1) * p + x2) * p + x3
    if psl:
        n0, n1, n2, n3 = (-x0) % p, (-x1) % p, (-x2) % p, (-x3) % p
        c = min(c, ((n0 * p + n1) * p + n2) * p + n3)
    return c


def _canon_np(p, psl, x0, x1, x2, x3):
    c = ((x0 * p + x1) * p + x2) * p + x3
    if psl:
        n0 = (-x0) % p
        n1 = (-x1) % p
        n2 = (-x2) % p
        n3 = (-x3) % p
        n = ((n0 * p + n1) * p + n2) * p + n3
        c = np.minimum(c, n)
    return c


def _sl2_table(p, psl):
    """SL(2,p), or PSL(2,p) = SL(2,p)/{+-I} when psl is True. Returns (N, identity_index, R)."""
    reps = set()
    for a, b, c, d_ in itertools.product(range(p), repeat=4):
        if (a * d_ - b * c) % p == 1:
            reps.add(_canon_py(p, psl, a, b, c, d_))
    reps = sorted(reps)
    N = len(reps)
    idx = np.full(p ** 4, -1, dtype=np.int64)
    idx[np.array(reps, dtype=np.int64)] = np.arange(N, dtype=np.int64)
    dec = np.array([[c // p ** 3 % p, c // p ** 2 % p, c // p % p, c % p] for c in reps],
                   dtype=np.int64)
    x0, x1, x2, x3 = dec[:, 0], dec[:, 1], dec[:, 2], dec[:, 3]
    R = np.empty((N, N), dtype=np.int64)
    for s in range(N):
        sa, sb, sc, sd = (int(v) for v in dec[s])
        y0 = (x0 * sa + x1 * sc) % p
        y1 = (x0 * sb + x1 * sd) % p
        y2 = (x2 * sa + x3 * sc) % p
        y3 = (x2 * sb + x3 * sd) % p
        row = idx[_canon_np(p, psl, y0, y1, y2, y3)]
        if (row < 0).any():
            raise ValueError("inconsistent matrix group table")
        R[s] = row
    e = int(idx[_canon_py(p, psl, 1, 0, 0, 1)])
    return N, e, R


def _sample_group(N, rng):
    """Random group of order N as (N, identity, R), or None."""
    if N in (168, 336) and rng.random() < 0.5:
        return _sl2_table(7, N == 168)
    divs = [k2 for k2 in range(1, N + 1) if N % k2 == 0 and N // k2 >= 2]
    if not divs:
        return None
    for _ in range(30):
        k2 = rng.choice(divs)
        m = N // k2
        if k2 == 1:
            r = 1
        else:
            rs = [r for r in range(1, m)
                  if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not rs:
                continue
            r = rng.choice(rs)
        return _semidirect_table(m, k2, r)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts: cost, annealing, construction.
# ----------------------------------------------------------------------------

def _cost(k, N, Rl, darts, D, limit):
    """Uncovered (representative, vertex) pairs at distance > D; 0 means valid.

    Left multiplication is an automorphism, so one representative per base class
    (2k of them) suffices. Returns early once the total exceeds `limit`.
    """
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    NT = 2 * k * N
    adj = [[] for _ in range(NT)]
    for i, j, s in darts:
        row = Rl[s]
        ai = i * N
        bj = (k + j) * N
        for g in range(N):
            a = ai + g
            b = bj + row[g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    reps = [i * N for i in range(k)] + [(k + j) * N for j in range(k)]
    for src in reps:
        seen = bytearray(NT)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += NT - cnt
        if total > limit:
            return total
    return total


def _edges(k, N, Rl, darts):
    E = set()
    for i, j, s in darts:
        row = Rl[s]
        for g in range(N):
            E.add((i * N + g, (k + j) * N + row[g]))
    return 2 * k * N, sorted(E)


def _anneal(k, N, Rl, D, d, rng, iters, deadline):
    """Anneal voltages and layer permutations. Returns darts with cost 0, or None."""
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(N)])
    cost = _cost(k, N, Rl, darts, D, float("inf"))
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)
        limit = cost - T * math.log(1.0 - rng.random())
        if k == 1 or rng.random() < 0.6:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(N)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _cost(k, N, Rl, darts, D, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, N, Rl, darts, D, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    return darts if cost == 0 else None


def _search(d, D, deadline, rng, get_best, consider):
    """Repeatedly try bi-Cayley lifts just above the current best order."""
    moore = lib.moore_bound(d, D)
    KS = [1, 1, 2, 2, 2, 3, 3, 4, 5, 6]
    iters = 500
    while time.monotonic() < deadline:
        best_n = get_best()
        if best_n >= moore:
            break
        k = rng.choice(KS)
        lo = best_n // (2 * k) + 1
        hi_cap = moore // (2 * k)
        if lo > hi_cap:
            continue
        span = max(3, lo // 6)
        hi = min(hi_cap, lo + span)
        N = rng.randint(lo, hi)
        g = _sample_group(N, rng)
        if g is None:
            continue
        NN, _e, R = g
        Rl = R.tolist()
        darts = _anneal(k, NN, Rl, D, d, rng, iters, deadline)
        if darts is not None:
            n, E = _edges(k, NN, Rl, darts)
            consider(n, E)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    base = lib.haar_graph(d, range(d))
    state = {"n": base[0], "e": base[1]}

    def consider(n, e):
        if n > state["n"] and lib.is_valid(n, e, d, D):
            state["n"], state["e"] = n, e
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            try:
                consider(pg[0], pg[1])
            except Exception:
                pass
        q = d - 2
        if q >= 3 and lib.is_prime_power(q):
            try:
                ar = lib.araujo_lopez_graph(q)
                consider(ar[0], ar[1])
            except Exception:
                pass

    if D >= 4 and d >= 3:
        try:
            _search(d, D, deadline, rng, lambda: state["n"], consider)
        except Exception:
            pass

    n, e = state["n"], state["e"]
    if not lib.is_valid(n, e, d, D):
        n, e = base
    return n, e
