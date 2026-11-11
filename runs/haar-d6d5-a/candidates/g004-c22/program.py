"""Degree-6, diameter-5 target: Haar graphs over non-abelian metacyclic groups of order just above 342.

Haar graph H(G, S): vertices A_g and B_g (g in G), with A_g ~ B_{s*g} for s in S, |S| = 6. It is bipartite,
6-regular, and has 2|G| vertices. Let T = S^-1 S and U = S S^-1. Then A-A and A-B distances are at most 5 when
T^2 = G, and B-B distances are at most 5 when U^2 = G. Both are needed for A-A and B-B pairs, so the cost

    cost(S) = |G \\ T^2| + |G \\ U^2|

is zero exactly when the candidate is a valid diameter-5 graph. Each candidate S is found by simulated annealing
over single-element replacements. Groups of order N in [343, 400] are tried in increasing order, so any success
gives 2N >= 686 > 684. Every graph is checked with lib.is_valid. If nothing is found, a known-valid Haar graph
(660 vertices) is returned, backed by a tiny always-valid graph.
"""
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
DEG = 6
N_LO = 343          # 2 * 343 = 686 > record 684
N_HI = 400
TEMP = 1.0
PATIENCE = 4000
SLICE = 3.0         # seconds of annealing per candidate per pass

FALLBACK_SD = (33, 10, 26)              # semidirect Z_33 x| Z_10, order 330
FALLBACK_S = [0, 179, 116, 180, 47, 306]


# ----------------------------------------------------------------------------- groups

def sd_table(m, k, r):
    """Multiplication table of Z_m x|_r Z_k, element (a, b) coded a*k+b, identity 0.

    (a, b)(c, d) = (a + r^b c, b + d). Returns (MT, inv).
    """
    N = m * k
    a = np.arange(N, dtype=np.int64) // k
    b = np.arange(N, dtype=np.int64) % k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    MT = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    if not np.all((MT == 0).sum(axis=1) == 1):
        raise ValueError("bad group table")
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def cand_specs(N):
    """Up to three non-abelian metacyclic specs (m, k, r) with m*k = N, spread over the options."""
    specs = []
    for k in range(2, N):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        for r in range(2, m):
            if r != 1 and math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                specs.append((m, k, r))
    if len(specs) <= 3:
        return specs
    step = len(specs) / 3.0
    return [specs[int(i * step)] for i in range(3)]


# ----------------------------------------------------------------------------- Haar graphs

def haar_cost(MT, inv, S, N):
    """Number of group elements missed by T^2 (T = S^-1 S) plus those missed by U^2 (U = S S^-1)."""
    Si = inv[S]
    T = MT[Si[:, None], S[None, :]].ravel()
    mark = np.zeros(N, dtype=bool)
    mark[MT[T[:, None], T[None, :]].ravel()] = True
    c1 = N - int(mark.sum())
    U = MT[S[:, None], Si[None, :]].ravel()
    mark[:] = False
    mark[MT[U[:, None], U[None, :]].ravel()] = True
    c2 = N - int(mark.sum())
    return c1 + c2


def anneal(MT, inv, N, rng, deadline):
    """Anneal a connection set S of size DEG until cost 0 (return S) or the deadline (return None)."""
    S = rng.choice(N, size=DEG, replace=False).astype(np.int64)
    cur = haar_cost(MT, inv, S, N)
    best, since = cur, 0
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        i = int(rng.integers(DEG))
        new = int(rng.integers(N))
        if new in S:
            continue
        old = int(S[i])
        S[i] = new
        c = haar_cost(MT, inv, S, N)
        if c <= cur or rng.random() < math.exp(-(c - cur) / TEMP):
            cur = c
            if cur < best:
                best, since = cur, 0
            else:
                since += 1
        else:
            S[i] = old
            since += 1
        if since > PATIENCE:
            S = rng.choice(N, size=DEG, replace=False).astype(np.int64)
            cur = haar_cost(MT, inv, S, N)
            best, since = cur, 0
    return S


def haar(MT, S):
    """Haar graph: A-vertex g ~ B-vertex s*g for s in S. Returns (2N, edges); A_g = g, B_g = N + g."""
    N = MT.shape[0]
    edges = []
    for s in S:
        row = MT[int(s)]
        edges.extend((g, N + int(row[g])) for g in range(N))
    return 2 * N, edges


# ----------------------------------------------------------------------------- fallbacks

def safe_small(d, D):
    """Small graph that is valid for (d, D), chosen among a few simple constructions."""
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
    budget = max(0.5, min(0.8 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    cands = []
    for N in range(N_LO, N_HI + 1):
        for spec in cand_specs(N):
            cands.append((N, spec))

    best = None  # (n, edges)
    while cands and time.monotonic() < deadline:
        if best is not None and all(2 * N <= best[0] for N, _ in cands):
            break
        for N, spec in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            if best is not None and 2 * N <= best[0]:
                continue
            try:
                MT, inv = sd_table(*spec)
                S = anneal(MT, inv, N, rng, min(deadline, now + SLICE))
                if S is None:
                    continue
                n, edges = haar(MT, S)
                if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                    best = (n, edges)
            except Exception:
                continue

    if best is not None:
        return best

    try:
        MT, inv = sd_table(*FALLBACK_SD)
        n, edges = haar(MT, FALLBACK_S)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return safe_small(d, D)
