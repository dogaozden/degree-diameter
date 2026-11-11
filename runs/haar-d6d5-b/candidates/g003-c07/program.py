"""Non-Haar voltage lifts for the bipartite degree-diameter problem (d=6, D=5).

Base multigraph: kb A-vertices and kb B-vertices, 6-regular (sum of 6 random permutation matrices).
Each dart (i, j, g) joins (x, A_i) to (x*g, B_j) over a finite group G of order N. Left multiplication
is an automorphism, so the diameter is at most 5 iff every one of the 2*kb fibre-representatives reaches
all 2*kb*N vertices within 5 steps. Cost = number of unreached (source, vertex) cells. Annealing over
the dart voltages drives the cost to 0. Every returned graph is checked with lib.is_valid. If nothing
beats the fallback, the parent's valid Haar graph (660 vertices) is returned.
"""
import itertools
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
DEG = 6
DIAM = 5


# ----------------------------------------------------------------------------- groups (identity = index 0)

def _finish(MT):
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> a*k + j, (a, j)(b, l) = (a + lam^j b, j + l)."""
    if m < 1 or k < 1 or math.gcd(lam, m) != 1 or pow(lam, k, m) != 1 % m:
        raise ValueError("bad metacyclic parameters")
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def group_cyclic(N):
    a = np.arange(N)
    return _finish((a[:, None] + a[None, :]) % N)


def group_times_cyclic(grp, c):
    """Direct product of a table group with Z_c; element (g, t) has index g*c + t."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    cc = np.arange(c)
    MT = np.empty((n0 * c, n0 * c), dtype=np.int32)
    for g in range(n0):
        blk = MT0[g].astype(np.int64)[None, :, None] * c + ((cc[:, None, None] + cc[None, None, :]) % c)
        MT[g * c:(g + 1) * c] = blk.reshape(c, n0 * c)
    return _finish(MT)


def metacyclic_list(N):
    out = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        for lam in range(2, m):
            if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                out.append((m, k, lam))
    return out


def group_builders(N, rng):
    out = []
    meta = metacyclic_list(N)
    if meta:
        m, k, lam = meta[int(rng.integers(len(meta)))]
        out.append(lambda m=m, k=k, lam=lam: group_meta(m, k, lam))
    for c in range(2, N):
        if N % c == 0 and N // c >= 6:
            sub = metacyclic_list(N // c)
            if sub:
                m, k, lam = sub[int(rng.integers(len(sub)))]
                out.append(lambda c=c, m=m, k=k, lam=lam: group_times_cyclic(group_meta(m, k, lam), c))
                break
    if not out:
        out.append(lambda N=N: group_cyclic(N))
    return out


# ----------------------------------------------------------------------------- voltage-lift annealing

def anneal(kb, N, MT, inv, rng, deadline, patience=3000, temp=3.0):
    """Anneal dart voltages of a random 6-regular base on kb+kb vertices over a group of order N.
    Returns (n, edges) with cost 0 (not yet checked), or None at the deadline."""
    V = 2 * kb * N
    T = DEG * kb
    xs = np.arange(N)

    # dart t = r*kb + i joins A_i to B_{p_r[i]}, for DEG random permutations p_r.
    di = np.empty(T, dtype=np.int64)
    dj = np.empty(T, dtype=np.int64)
    dr = np.empty(T, dtype=np.int64)
    for r in range(DEG):
        p = rng.permutation(kb)
        for i in range(kb):
            t = r * kb + i
            di[t], dj[t], dr[t] = i, p[i], r
    blocks = {}
    for t in range(T):
        blocks.setdefault((int(di[t]), int(dj[t])), []).append(t)
    others = [[s for s in blocks[(int(di[t]), int(dj[t]))] if s != t] for t in range(T)]

    dg = np.zeros(T, dtype=np.int64)
    nbr = np.zeros((V, DEG), dtype=np.int64)

    def set_dart(t, g):
        dg[t] = g
        i, j, r = int(di[t]), int(dj[t]), int(dr[t])
        # A_i vertex x -> B_j vertex x*g ; B_j vertex y -> A_i vertex y*g^-1
        nbr[i * N:(i + 1) * N, r] = (kb + j) * N + MT[xs, g]
        nbr[(kb + j) * N:(kb + j + 1) * N, r] = i * N + MT[xs, inv[g]]

    def randomize():
        for ts in blocks.values():
            gs = rng.choice(N, size=len(ts), replace=False)
            for t, g in zip(ts, gs):
                set_dart(t, int(g))

    S = 2 * kb
    R0 = np.zeros((S, V), dtype=bool)
    R0[np.arange(S), np.arange(S) * N] = True
    total = S * V

    def cost():
        R = R0
        for _ in range(DIAM):
            R = R | R[:, nbr].any(axis=2)
        return total - int(R.sum())

    while time.monotonic() < deadline:
        randomize()
        cur = cost()
        local_best = cur
        stall = 0
        while stall < patience:
            if cur == 0:
                edges = [(v, int(nbr[v, c])) for v in range(kb * N) for c in range(DEG)]
                return V, edges
            if time.monotonic() >= deadline:
                return None
            t = int(rng.integers(T))
            used = {int(dg[s]) for s in others[t]}
            g = int(rng.integers(N))
            while g in used:
                g = int(rng.integers(N))
            old = int(dg[t])
            set_dart(t, g)
            c2 = cost()
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
                cur = c2
            else:
                set_dart(t, old)
            if cur < local_best:
                local_best = cur
                stall = 0
            else:
                stall += 1
    return None


# ----------------------------------------------------------------------------- fallbacks

def haar_edges(MT, S):
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    if D >= 2 and d >= 1:
        return 2 * d, [(a, d + b) for a in range(d) for b in range(d)]
    return 2, [(0, 1)]


def fallback(d, D):
    try:
        MT, _ = group_meta(33, 10, 26)
        g = checked(MT, [0, 179, 116, 180, 47, 306], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


def build_configs(rng):
    cfgs = []
    for kb in (2, 3, 4, 6):
        Nmin = 684 // (2 * kb) + 1
        for N in range(Nmin, Nmin + 3):
            for gb in group_builders(N, rng):
                cfgs.append((2 * kb * N, kb, N, gb))
    cfgs.sort(key=lambda c: (c[0], c[1]))
    return cfgs


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = min(0.80 * time_limit, time_limit - 8.0)
    deadline = t0 + max(1.0, budget)
    rng = np.random.default_rng(seed)
    best = fallback(d, D)
    best_n = best[0]
    try:
        configs = build_configs(rng)
        done = set()
        while True:
            now = time.monotonic()
            remaining = deadline - now
            if remaining <= 0.5:
                break
            pending = [i for i, c in enumerate(configs) if i not in done and c[0] > best_n]
            if not pending:
                break
            i = pending[0]
            done.add(i)
            V, kb, N, gb = configs[i]
            share = remaining / min(len(pending), 8)
            slice_end = now + min(remaining, max(2.5, share))
            try:
                MT, inv = gb()
                res = anneal(kb, N, MT, inv, rng, slice_end)
            except Exception:
                res = None
            if res is not None:
                n, edges = res
                if n > best_n and lib.is_valid(n, edges, d, D):
                    best, best_n = (n, edges), n
    except Exception:
        pass
    return best
