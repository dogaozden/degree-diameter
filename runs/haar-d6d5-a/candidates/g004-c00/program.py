"""Degree-6, diameter-5 target: searched Haar graphs over non-abelian groups of order just above 342.

Haar graph H(G, S): A-vertex g ~ B-vertex s*g for s in S, with |S| = 6. It is bipartite, 6-regular and has
2|G| vertices. Its diameter is at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G. Both sets are computed directly
from group products, so no BFS is needed. Left translation and relabelling let us fix the identity inside S.
Each candidate is checked with lib.is_valid, and a valid smaller Haar graph is the fallback.
"""
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
RECORD = 684
DEG = 6
SLICE = 2.5         # seconds per (group, restart) annealing slice in the round-robin
PATIENCE = 3000     # steps without improvement before a fresh random S
K_BEST = 8          # candidate moves per step, the best one is kept
TEMP = 0.6          # Metropolis temperature in units of missing elements

FALLBACK_SPEC = (33, 10, 26)            # semidirect Z_33 x| Z_10, order 330
FALLBACK_S = [0, 179, 116, 180, 47, 306]


# ----------------------------------------------------------------------------- groups

def sd_table(m, k, r):
    """Multiplication table of Z_m x|_r Z_k, element (a, b) coded a*k+b, built with numpy."""
    powers = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    idx = np.arange(m * k, dtype=np.int64)
    ax, bx = idx // k, idx % k
    A = (ax[:, None] + powers[bx][:, None] * ax[None, :]) % m
    B = (bx[:, None] + bx[None, :]) % k
    return A * k + B


def heis_mul(p):
    """Heisenberg group mod p, element (a, b, c) coded a*p^2 + b*p + c."""
    q2 = p * p

    def mul(x, y):
        a1, rest1 = divmod(x, q2)
        b1, c1 = divmod(rest1, p)
        a2, rest2 = divmod(y, q2)
        b2, c2 = divmod(rest2, p)
        return ((a1 + a2) % p) * q2 + ((b1 + b2) % p) * p + (c1 + c2 + a1 * b2) % p
    return mul


def group_table(order, mul):
    """Table MT[x, y] = mul(x, y) with identity 0, and the inverse array."""
    MT = np.empty((order, order), dtype=np.int64)
    for x in range(order):
        MT[x] = [mul(x, y) for y in range(order)]
    return MT


def make_group(spec):
    """Return (MT, inv) for a group spec."""
    if spec[0] == 'sd':
        _, a, b, s = spec
        MT = sd_table(a, b, s)
    else:  # ('heis', p)
        p = spec[1]
        MT = group_table(p ** 3, heis_mul(p))
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def candidate_specs():
    """Non-abelian groups of order just above RECORD // 2, smallest first (Heisenberg first at 343)."""
    jobs = []
    lo = RECORD // 2 + 1
    for G in range(lo, lo + 12):
        specs = []
        if G == 343:
            specs.append(('heis', 7))
        sd = []
        for b in range(2, G):
            if G % b:
                continue
            a = G // b
            if a < 3:
                continue
            for s in range(2, a):
                if math.gcd(s, a) == 1 and pow(s, b, a) == 1:
                    sd.append(('sd', a, b, s))
        specs += sd[::max(1, len(sd) // 3)][:3]
        for sp in specs:
            jobs.append((G, sp))
    return jobs


# ----------------------------------------------------------------------------- Haar cost

def haar_cost(MT, inv, S):
    """Number of group elements missing from (S^-1 S)^2 plus those missing from (S S^-1)^2. 0 means diameter <= 5."""
    m = MT.shape[0]
    Sa = np.asarray(S, dtype=np.int64)
    iS = inv[Sa]
    mark = np.zeros(m, dtype=bool)
    mark[MT[iS[:, None], Sa[None, :]].ravel()] = True
    T = np.flatnonzero(mark)
    mark[:] = False
    mark[MT[T[:, None], T[None, :]].ravel()] = True
    c1 = m - int(mark.sum())
    mark[:] = False
    mark[MT[Sa[:, None], iS[None, :]].ravel()] = True
    U = np.flatnonzero(mark)
    mark[:] = False
    mark[MT[U[:, None], U[None, :]].ravel()] = True
    return c1 + (m - int(mark.sum()))


def anneal(MT, inv, rng, deadline):
    """Anneal a connection set S (identity fixed in slot 0) until cost 0, returning S, or return None at the deadline."""
    m = MT.shape[0]

    def fresh():
        S = [0] + [int(x) for x in rng.choice(np.arange(1, m), size=DEG - 1, replace=False)]
        return S, haar_cost(MT, inv, S)

    S, cur = fresh()
    best, stall = cur, 0
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        cand = None
        for _ in range(K_BEST):
            i = int(rng.integers(1, DEG))
            v = int(rng.integers(1, m))
            if v in S:
                continue
            T_ = S.copy()
            T_[i] = v
            c = haar_cost(MT, inv, T_)
            if cand is None or c < cand[0]:
                cand = (c, i, v)
        if cand is None:
            continue
        c, i, v = cand
        if c <= cur or rng.random() < math.exp(-(c - cur) / TEMP):
            S[i] = v
            cur = c
        if cur < best:
            best, stall = cur, 0
        else:
            stall += 1
        if stall > PATIENCE:
            S, cur = fresh()
            best, stall = cur, 0
    return S


# ----------------------------------------------------------------------------- graphs

def haar(MT, S):
    """Haar graph: A-vertex g ~ B-vertex s*g for s in S. Returns (2N, edges)."""
    N = MT.shape[0]
    edges = [(g, N + int(MT[s, g])) for s in S for g in range(N)]
    return 2 * N, edges


def safe_small(d, D):
    """Small graph that is valid for (d, D), chosen among simple constructions."""
    cands = []
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        cands.append(lib.projective_plane_incidence(d - 1))
    if D >= 2 and d >= 1:
        cands.append((2 * d, [(i, d + j) for i in range(d) for j in range(d)]))
    if D >= 1 and d >= 1:
        cands.append((2, [(0, 1)]))
    cands.append((1, []))
    for n, edges in cands:
        try:
            if lib.is_valid(n, edges, d, D):
                return n, edges
        except Exception:
            pass
    return 1, []


# ----------------------------------------------------------------------------- entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return safe_small(d, D)

    t0 = time.monotonic()
    budget = max(1.0, min(0.7 * time_limit, time_limit - 12.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    jobs = candidate_specs()
    tables = {}
    best = None
    k = 0
    while jobs and time.monotonic() < deadline:
        if best is not None and all(2 * G <= best[0] for G, _ in jobs):
            break
        G, spec = jobs[k % len(jobs)]
        k += 1
        if best is not None and 2 * G <= best[0]:
            continue
        try:
            if spec not in tables:
                tables[spec] = make_group(spec)
            MT, inv = tables[spec]
            slice_end = min(deadline, time.monotonic() + SLICE)
            S = anneal(MT, inv, rng, slice_end)
            if S is None:
                continue
            n, edges = haar(MT, S)
            if lib.is_valid(n, edges, d, D):
                if best is None or n > best[0]:
                    best = (n, edges)
        except Exception:
            continue

    if best is not None:
        return best

    try:
        MT, _ = group_table(*lib.semidirect_group(*FALLBACK_SPEC)[:2])
        n, edges = haar(MT, FALLBACK_S)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return safe_small(d, D)
