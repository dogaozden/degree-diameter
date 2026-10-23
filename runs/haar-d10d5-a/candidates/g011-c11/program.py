"""Bi-Cayley search for the d=10, D=5 target, with a Haar-graph fallback.

The parent used Haar graphs: one group orbit per side, one connection set S with |S| = d. This version
uses r orbits per side (r = 2, 3, 4). Vertices are A_{i,g} and B_{j,h} for i, j < r and g, h in G.
Edges are A_{i,g} ~ B_{j, s*g} for each dart (i, j, s). Each A-orbit has d darts, and each B-orbit receives
exactly d darts, so the graph is d-regular and bipartite with 2*r*|G| vertices. Right multiplication by G
is an automorphism group with 2r vertex orbits, so the diameter-5 check needs only BFS from one
representative per orbit. Darts are annealed with an exact cost (unreached vertices). Only graphs that pass
lib.is_valid are returned. Otherwise the parent's valid Haar graph (3582 vertices) is returned.
"""
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------- groups

def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> a*k + j, identity 0. Needs gcd(lam, m) = 1 and lam^k = 1 mod m."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int64)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k \
            + (j[lo:hi, None] + j[None, :]) % k
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def nontrivial_groups(N):
    """Non-abelian metacyclic Z_m x| Z_k of order N, as (m, k, lam) triples."""
    out = []
    for k in range(2, 11):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        for lam in range(2, m):
            if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                out.append((m, k, lam))
    return out


# ------------------------------------------------------------- bi-Cayley graph

def make_nb(MT, inv, J, S):
    """Neighbour array (2*r*N, d). Rows 0..rN-1 are A-vertices, rows rN.. are B-vertices."""
    r, d = J.shape
    N = MT.shape[0]
    nbA = ((r + J)[:, None, :] * N + MT[S].transpose(0, 2, 1)).reshape(r * N, d)
    order = np.argsort(J.ravel(), kind="stable")   # darts grouped by target B-orbit, d per orbit
    sel_i = (order // d).reshape(r, d)              # source A-orbit of each dart
    sel_s = S.ravel()[order].reshape(r, d)          # element of each dart
    nbB = (sel_i[:, None, :] * N + MT[inv[sel_s]].transpose(0, 2, 1)).reshape(r * N, d)
    return np.vstack([nbA, nbB])


def cost(nb, reps, n):
    """Total number of vertices not within distance 5 of the representatives (0 = valid)."""
    tot = 0
    for s0 in reps:
        seen = np.zeros(n, dtype=bool)
        seen[s0] = True
        front = np.array([s0], dtype=np.int64)
        for _ in range(5):
            nxt = nb[front].ravel()
            nxt = np.unique(nxt[~seen[nxt]])
            if nxt.size == 0:
                break
            seen[nxt] = True
            front = nxt
        tot += n - int(seen.sum())
    return tot


def anneal(MT, inv, J, rng, deadline):
    """Anneal the connection elements with J fixed. Returns (best cost, best S)."""
    r, d = J.shape
    N = MT.shape[0]
    n = 2 * r * N
    reps = [i * N for i in range(r)] + [(r + j) * N for j in range(r)]

    S = np.zeros((r, d), dtype=np.int64)
    for i in range(r):
        for t in range(d):
            j = J[i, t]
            forb = {int(S[i, u]) for u in range(t) if J[i, u] == j}
            while True:
                s = int(rng.integers(N))
                if s not in forb:
                    break
            S[i, t] = s

    cur = cost(make_nb(MT, inv, J, S), reps, n)
    best, bestS = cur, S.copy()
    since, T = 0, 2.0
    while cur > 0 and since <= 1500 and time.monotonic() < deadline:
        i = int(rng.integers(r))
        t = int(rng.integers(d))
        j = J[i, t]
        forb = {int(S[i, u]) for u in range(d) if u != t and J[i, u] == j}
        while True:
            s = int(rng.integers(N))
            if s not in forb and s != S[i, t]:
                break
        old = S[i, t]
        S[i, t] = s
        c = cost(make_nb(MT, inv, J, S), reps, n)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c
            if c < best:
                best, bestS, since = c, S.copy(), 0
        else:
            S[i, t] = old
        since += 1
    return best, bestS


# ----------------------------------------------------------- fallbacks

def haar_edges(MT, S):
    """Edges of the Haar graph with A-vertex g = g and B-vertex g = N + g."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]


def fallback_graph(d, D):
    """Valid smaller Haar graph (3582 vertices for d=10, D=5), checked, else the trivial graph."""
    try:
        MT, _ = group_meta(199, 9, 180)
        n, edges = haar_edges(MT, FALLBACK_S)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ----------------------------------------------------------------- target

def target(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + min(0.8 * time_limit, time_limit - 8.0)
    rng = np.random.default_rng(seed)
    rs = [2, 3, 2, 4, 3]
    attempt = 0
    while time.monotonic() < deadline - 0.5:
        r = rs[attempt % len(rs)]
        attempt += 1
        N0 = 4000 // (2 * r) + 1        # 2*r*N0 > 4000
        Ns = list(range(N0, N0 + 12))
        rng.shuffle(Ns)
        cands = []
        for N in Ns:
            cands = nontrivial_groups(N)
            if cands:
                break
        if not cands:
            continue
        m, k, lam = cands[int(rng.integers(len(cands)))]
        N = m * k
        MT, inv = group_meta(m, k, lam)
        J = np.array([rng.permutation(r) for _ in range(d)]).T.astype(np.int64)
        slice_end = min(deadline, time.monotonic() + 12.0)
        c, S = anneal(MT, inv, J, rng, slice_end)
        if c == 0:
            nb = make_nb(MT, inv, J, S)
            n = 2 * r * N
            edges = [(a, int(b)) for a in range(r * N) for b in nb[a]]
            if lib.is_valid(n, edges, d, D):
                return n, edges
    return fallback_graph(d, D)


def build(d, D, seed, time_limit):
    if (d, D) != (10, 5):
        return trivial(d, D)
    try:
        return target(d, D, seed, time_limit)
    except Exception:
        return fallback_graph(d, D)
