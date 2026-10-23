"""Degree-6, diameter-5 target: annealed Haar graphs over non-abelian groups.

A Haar graph over a group G with connection set S (|S| = 6) has vertices (g, A) and (g, B) for g in G, and
edges (g, A) ~ (s*g, B) for s in S. It is bipartite, 6-regular, and has 2|G| vertices. Its diameter is at most 5
when (S^-1 S)^2 = G and (S S^-1)^2 = G. The cost of S is the number of uncovered group elements in those two
sets, so a cost of 0 gives a valid graph. Simulated annealing over S searches non-abelian groups with
|G| >= 343 (so 2|G| > 684). Every returned graph is checked with lib.is_valid. If no Haar graph beats the
record, the earlier 660-vertex Haar fallback is returned, and a tiny always-valid graph backs that up.
"""
import math
import time

import numpy as np

import lib

TARGET = (6, 5)
RECORD = 684
K = 6                 # connection-set size = degree
BASE_N = 343          # 2*343 = 686 > 684
SPAN = 30             # group orders tried: BASE_N .. BASE_N + SPAN - 1
TEMP = 0.8            # annealing temperature in uncovered-element units
PATIENCE = 3000       # steps without improvement before a restart
JOB_CAP = 8.0         # seconds per (group, S) annealing job

FALLBACK_SPEC = (33, 10, 26)            # semidirect Z_33 x| Z_10, order 330
FALLBACK_S = [0, 179, 116, 180, 47, 306]


# ----------------------------------------------------------------------------- groups

def group_table(order, mul):
    """Multiplication table MT[x, y] = mul(x, y) (identity at index 0) and the inverse array."""
    MT = np.empty((order, order), dtype=np.int64)
    for x in range(order):
        MT[x] = [mul(x, y) for y in range(order)]
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def heis_mul(p):
    """Heisenberg group mod p, element (a, b, c) coded as a*p^2 + b*p + c."""
    q2 = p * p

    def mul(x, y):
        a1, rest1 = divmod(x, q2)
        b1, c1 = divmod(rest1, p)
        a2, rest2 = divmod(y, q2)
        b2, c2 = divmod(rest2, p)
        return ((a1 + a2) % p) * q2 + ((b1 + b2) % p) * p + (c1 + c2 + a1 * b2) % p
    return mul


def make_group(spec):
    """Build (MT, inv) for a group spec."""
    if spec[0] == 'sd':
        _, a, b, s = spec
        order, mul, _ = lib.semidirect_group(a, b, s)
        return group_table(order, mul)
    p = spec[1]
    return group_table(p ** 3, heis_mul(p))


def specs_of_order(N, rng):
    """Candidate non-abelian groups of order N: Heisenberg if applicable, then a few metacyclic groups."""
    specs = []
    p = round(N ** (1.0 / 3.0))
    if p >= 2 and p ** 3 == N and lib.is_prime_power(p):
        specs.append(('heis', p))
    sd = []
    for b in range(2, N):
        if N % b:
            continue
        a = N // b
        if a < 3:
            continue
        for s in range(2, a):
            if math.gcd(s, a) == 1 and pow(s, b, a) == 1:
                sd.append(('sd', a, b, s))
    if sd:
        order = rng.permutation(len(sd))
        sd = [sd[i] for i in order]
        specs.extend(sd[:3])
    return specs


# ----------------------------------------------------------------------------- Haar search

def cost(MT, inv, S):
    """Uncovered elements in (S^-1 S)^2 and (S S^-1)^2. Zero means diameter <= 5."""
    N = MT.shape[0]
    iS = inv[S]
    A = np.unique(MT[iS[:, None], S[None, :]])          # S^-1 S
    B = np.unique(MT[A[:, None], A[None, :]])           # (S^-1 S)^2
    C = np.unique(MT[S[:, None], iS[None, :]])          # S S^-1
    D2 = np.unique(MT[C[:, None], C[None, :]])          # (S S^-1)^2
    return (N - B.size) + (N - D2.size)


def fresh_set(N, rng):
    return rng.choice(N, size=K, replace=False).astype(np.int64)


def anneal(MT, inv, rng, deadline):
    """Anneal a connection set S with cost 0 until the deadline. Returns S or None."""
    N = MT.shape[0]
    S = fresh_set(N, rng)
    cur = cost(MT, inv, S)
    since = 0
    while cur > 0 and time.monotonic() < deadline:
        i = int(rng.integers(K))
        x = int(rng.integers(N))
        if np.any(S == x):
            continue
        old = int(S[i])
        S[i] = x
        c = cost(MT, inv, S)
        if c <= cur or rng.random() < math.exp(-(c - cur) / TEMP):
            cur = c
            since = 0 if c < cur + 1 else since + 1
        else:
            S[i] = old
            since += 1
        if since > PATIENCE:
            S = fresh_set(N, rng)
            cur = cost(MT, inv, S)
            since = 0
    return S if cur == 0 else None


def haar_graph(MT, S):
    """Haar graph: A-vertex g ~ B-vertex N + s*g for s in S; returns (2N, edges)."""
    N = MT.shape[0]
    edges = [(g, N + int(MT[int(s), g])) for s in S for g in range(N)]
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
    budget = max(1.0, min(0.7 * time_limit, time_limit - 12.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best = None
    for N in range(BASE_N, BASE_N + SPAN):
        if time.monotonic() >= deadline:
            break
        if best is not None and 2 * N <= best[0]:
            continue
        for spec in specs_of_order(N, rng):
            now = time.monotonic()
            if now >= deadline:
                break
            try:
                MT, inv = make_group(spec)
                S = anneal(MT, inv, rng, min(deadline, now + JOB_CAP))
                if S is None:
                    continue
                n, edges = haar_graph(MT, S)
                if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                    best = (n, edges)
                    break   # found at this order; move on to larger orders
            except Exception:
                continue

    if best is not None:
        return best

    try:
        MT, _ = group_table(*lib.semidirect_group(*FALLBACK_SPEC)[:2])
        n, edges = haar_graph(MT, FALLBACK_S)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return safe_small(d, D)
