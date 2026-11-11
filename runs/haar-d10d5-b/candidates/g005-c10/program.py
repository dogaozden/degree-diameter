"""Haar-graph search over non-abelian groups for the bipartite degree-diameter problem (d=10, D=5).

CONSTRUCTION.  For a finite group G with |G| = N and a set S of d distinct elements, the Haar graph has
vertices A_g = g and B_g = N + g, with edges A_g ~ B_{s*g} for s in S.  It is bipartite, d-regular, and has
2N vertices.  Its diameter is at most 5 when (S^-1 S)^2 = G and (S S^-1)^2 = G.

SEARCH.  Groups come from two families: affine groups Z_p x| Z_k (x -> a*x + b with a in a subgroup of order k of
Z_p^*), and metacyclic groups Z_m x| Z_k.  For each group, simulated annealing replaces one element of S at a time.
The cost is the number of group elements missing from (S^-1 S)^2 and (S S^-1)^2.  Any zero-cost S is confirmed with
lib.is_valid before it is accepted.  The fallback is the valid 3582-vertex Haar graph from the parent, so the output
is never worse than the parent.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------ group tables

def table(N, mul, e):
    """Multiplication table MT[x, y] = mul(x, y) (vectorised), inverses via identity index e."""
    MT = np.empty((N, N), dtype=np.int32)
    ar = np.arange(N, dtype=np.int64)
    for lo in range(0, N, 128):
        hi = min(N, lo + 128)
        MT[lo:hi] = mul(ar[lo:hi, None], ar[None, :])
    inv = np.argmax(MT == e, axis=1).astype(np.int64)
    return MT, inv


def meta_group(m, k, r):
    """Z_m x|_r Z_k, element a*k + j, (a, j)(c, l) = (a + r^j c, j + l)."""
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)

    def mul(x, y):
        a, j = x // k, x % k
        c, l = y // k, y % k
        return ((a + pw[j] * c) % m) * k + (j + l) % k

    return table(m * k, mul, 0)


def affine_group(p, k):
    """Z_p x| H, H the subgroup of order k of Z_p^*, element (b, a) coded as i*p + b with a = H[i]."""
    H = [x for x in range(1, p) if pow(x, k, p) == 1]
    Hl = np.array(H, dtype=np.int64)
    pos = np.zeros(p, dtype=np.int64)
    pos[Hl] = np.arange(len(H))

    def mul(x, y):
        ax = Hl[x // p]
        bx = x % p
        ay = Hl[y // p]
        by = y % p
        a = (ax * ay) % p
        b = (bx + ax * by) % p
        return pos[a] * p + b

    e = int(pos[1]) * p
    return p * len(H), table(p * len(H), mul, e)


def primes_upto(n):
    s = [True] * (n + 1)
    s[0] = s[1] = False
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            for j in range(i * i, n + 1, i):
                s[j] = False
    return [i for i in range(n + 1) if s[i]]


def affine_candidates(lo_all, hi_all):
    out = []
    for p in primes_upto(hi_all):
        if p < 3:
            continue
        for k in range(2, p):
            if (p - 1) % k == 0:
                N = p * k
                if lo_all <= N <= hi_all:
                    out.append((p, k, N))
    return out


def pick_group(lo, hi, rng, aff_list):
    """Return (N, MT, inv) for a random group of order in [lo, hi], or None."""
    if aff_list and rng.random() < 0.6:
        cands = [c for c in aff_list if lo <= c[2] <= hi]
        if cands:
            p, k, _ = cands[int(rng.integers(len(cands)))]
            N, MT, inv = affine_group(p, k)
            return N, MT, inv
    for _ in range(30):
        N = int(rng.integers(lo, hi + 1))
        divs = [m for m in range(2, N) if N % m == 0 and N // m >= 2]
        if not divs:
            continue
        m = divs[int(rng.integers(len(divs)))]
        k = N // m
        rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not rs:
            continue
        r = rs[int(rng.integers(len(rs)))]
        MT, inv = meta_group(m, k, r)
        return N, MT, inv
    return None


# ------------------------------------------------------------------ Haar graph

def cover_cost(MT, inv, S, N):
    """Uncovered elements of (S^-1 S)^2 plus uncovered elements of (S S^-1)^2."""
    Si = inv[S]
    A = np.unique(MT[Si[:, None], S[None, :]])
    seen = np.zeros(N, dtype=bool)
    seen[MT[A[:, None], A[None, :]]] = True
    c = N - int(np.count_nonzero(seen))
    B = np.unique(MT[S[:, None], Si[None, :]])
    seen = np.zeros(N, dtype=bool)
    seen[MT[B[:, None], B[None, :]]] = True
    c += N - int(np.count_nonzero(seen))
    return c


def anneal(MT, inv, N, d, rng, L, deadline):
    """Anneal a connection set S of size d. Returns a zero-cost S or None."""
    S = rng.choice(N, d, replace=False).astype(np.int64)
    cur = cover_cost(MT, inv, S, N)
    if cur == 0:
        return S
    for step in range(L):
        if time.monotonic() >= deadline:
            return None
        i = int(rng.integers(d))
        g = int(rng.integers(N))
        if np.any(S == g):
            continue
        old = S[i]
        S[i] = g
        c = cover_cost(MT, inv, S, N)
        accept = c <= cur
        if not accept:
            temp = 1.5 * (1.0 - step / L) + 0.1
            accept = rng.random() < math.exp(-(c - cur) / temp)
        if accept:
            cur = c
            if cur == 0:
                return S.copy()
        else:
            S[i] = old
    return None


def haar_edges(MT, S, N):
    """Haar graph: A-vertex g is g, B-vertex is N + g; edge A_g ~ B_{s*g}."""
    ar = np.arange(N, dtype=np.int64)
    us = np.tile(ar, len(S))
    vs = np.concatenate([N + MT[int(s), :].astype(np.int64) for s in S])
    return 2 * N, list(zip(us.tolist(), vs.tolist()))


# ------------------------------------------------------------------ build

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(3.0, min(0.75 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best_n, best_edges = 0, None
    try:
        m, k, r = FALLBACK_GROUP
        MT, _ = meta_group(m, k, r)
        n, e = haar_edges(MT, FALLBACK_S, m * k)
        if lib.is_valid(n, e, d, D):
            best_n, best_edges = n, e
    except Exception:
        pass

    try:
        aff_list = affine_candidates(1000, 2600)
    except Exception:
        aff_list = []

    while time.monotonic() < deadline:
        try:
            lo = best_n // 2 + 1
            hi = lo + 300
            grp = pick_group(lo, hi, rng, aff_list)
            if grp is None:
                continue
            N, MT, inv = grp
            if 2 * N <= best_n:
                continue
            S = anneal(MT, inv, N, d, rng, 3000, deadline)
            if S is None:
                continue
            n, e = haar_edges(MT, S, N)
            if lib.is_valid(n, e, d, D) and n > best_n:
                best_n, best_edges = n, e
        except Exception:
            continue

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
