import math
import random
import time

import numpy as np

import lib


# ---------------------------------------------------------------------------
# Non-abelian Haar graphs for diameter 5.
#
# Group G = Z_m x| Z_k (element (a, b) coded a*k + b, product (a,b)(c,d) = (a + r^b c, b + d)).
# Haar graph on G with connection set S: a_g ~ b_{g s} for s in S, so it is d-regular with 2|G| vertices.
# Walks show that the A-A distance-4 set is (S S^-1)^2 and the B-B distance-4 set is (S^-1 S)^2.
# If both equal G, every pair is within distance 5. Since the identity may be assumed in S
# (right translation preserves both sets up to conjugacy), S = {0, s_1, ..., s_{d-1}}.
# Search for S by annealing on the uncovered count, with a vectorised cost.
# ---------------------------------------------------------------------------


def _semidirect_table(m, k, r):
    """Multiplication table of Z_m x| Z_k with r^k = 1 mod m, element (a, b) coded a*k+b."""
    N = m * k
    X = np.arange(N, dtype=np.int64)
    a = X // k
    b = X % k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    A = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    B = (b[:, None] + b[None, :]) % k
    return A * k + B


def _group_candidates(N, rng):
    """Non-abelian semidirect products Z_m x| Z_k of order N (shuffled)."""
    cands = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                cands.append((m, k, r))
    rng.shuffle(cands)
    return cands


def _cost(S, mul, invt, N):
    """Number of uncovered elements in (S S^-1)^2 and (S^-1 S)^2 (0 means diameter <= 5)."""
    s = np.array(S, dtype=np.int64)
    si = invt[s]
    P = np.unique(mul[s[:, None], si[None, :]])          # S S^-1
    mark = np.zeros(N, dtype=bool)
    mark[mul[P[:, None], P[None, :]].ravel()] = True     # (S S^-1)^2
    Q = np.unique(mul[si[:, None], s[None, :]])          # S^-1 S
    mark2 = np.zeros(N, dtype=bool)
    mark2[mul[Q[:, None], Q[None, :]].ravel()] = True    # (S^-1 S)^2
    return 2 * N - int(mark.sum()) - int(mark2.sum())


def _anneal(mul, invt, N, d, rng, t_end):
    """Search for S (containing identity 0) with zero cost before t_end. Returns S or None."""
    T = 0.7
    while time.monotonic() < t_end:
        S = [0] + rng.sample(range(1, N), d - 1)
        cur = _cost(S, mul, invt, N)
        best_local, stale = cur, 0
        while cur > 0:
            if stale > 4000 or time.monotonic() >= t_end:
                break
            move = None
            for _ in range(6):                      # best of K random replacements
                i = rng.randrange(1, d)
                x = rng.randrange(1, N)
                if x in S:
                    continue
                S2 = S[:]
                S2[i] = x
                c = _cost(S2, mul, invt, N)
                if move is None or c < move[0]:
                    move = (c, S2)
            if move is None:
                continue
            c, S2 = move
            if c <= cur or rng.random() < math.exp(-(c - cur) / T):
                S, cur = S2, c
            if cur < best_local:
                best_local, stale = cur, 0
            else:
                stale += 1
        if cur == 0:
            return S
        if time.monotonic() >= t_end:
            return None
    return None


def _haar_from_table(mul, N, S):
    """Haar graph: A-vertex g is g, B-vertex g is N + g, edges g ~ N + g*s."""
    edges = []
    for s in S:
        col = mul[:, s].tolist()
        edges.extend((g, N + col[g]) for g in range(N))
    return 2 * N, edges


def _search(d, D, rng, deadline):
    """Find the largest group-Haar graph with diameter <= D, scanning group orders upward."""
    moore = lib.moore_bound(d, D)
    Nmax = moore // 2
    N = max(d + 1, int(0.44 * moore / 2))
    best = None
    fails = 0
    while N <= Nmax and fails < 2 and time.monotonic() < deadline:
        ok = False
        for (m, k, r) in _group_candidates(N, rng)[:5]:
            now = time.monotonic()
            if now >= deadline:
                break
            t_end = min(deadline, now + 2.0)
            mul = _semidirect_table(m, k, r)
            invt = np.argmax(mul == 0, axis=1)
            S = _anneal(mul, invt, N, d, rng, t_end)
            if S is None:
                continue
            n, edges = _haar_from_table(mul, N, S)
            if lib.is_valid(n, edges, d, D):
                best, ok = (n, edges), True
                break
        fails = 0 if ok else fails + 1
        N += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 6.0))
    deadline = start + budget

    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        n, edges = lib.projective_plane_incidence(q)
        if lib.is_valid(n, edges, d, D):
            return n, edges

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2

    if D == 5 and d >= 3:
        rng = random.Random(seed)
        res = _search(d, D, rng, deadline)
        if res is not None and res[0] > best[0]:
            best = res

    # Cyclic Haar fallback (parent method), used only if it is larger.
    rng2 = random.Random(seed)
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng2.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            misses = 0
            if found[0] > best[0] and lib.is_valid(found[0], found[1], d, D):
                best = found
        else:
            misses += 1
        m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
