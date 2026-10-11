import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (used only for D = 3 and as fallback).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Bold family: bi-Cayley graphs over semidirect products Z_m x| Z_k.
#
# Vertices A_x = x and B_w = w, for x, w in G. Edge A_x ~ B_{x*s} for s in S,
# |S| = d. Left multiplication is an automorphism that is transitive on each
# side, so the diameter is <= D iff A_1 and B_1 both reach all 2|G| vertices
# within D steps. Each evaluation is two numpy BFS sweeps, so the annealer can
# afford many thousands of moves per group.
# ----------------------------------------------------------------------------

def _semidirect_table(m, k, r):
    """Multiplication table of Z_m x| Z_k; element (a, b) is coded a*k + b, and (a,b)(c,e) = (a + r^b c, b + e)."""
    G = m * k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    left = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    right = (b[:, None] + b[None, :]) % k
    return left * k + right


def _specs(lo, hi, rng):
    """All (G, m, k, r) with order G in [lo, hi] and r giving a valid semidirect product; non-abelian first."""
    out = []
    for k in range(1, hi // 3 + 1):
        for m in range(max(3, -(-lo // k)), hi // k + 1):
            G = m * k
            for r in range(1, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    out.append((G, m, k, r))
    rng.shuffle(out)
    out.sort(key=lambda t: t[3] == 1)
    return out


def _adj(M, inv, S, G):
    """Adjacency (2G, d): row x lists B-nodes G + x*s; row G+w lists A-nodes w*s^-1."""
    Sa = np.asarray(S, dtype=np.int64)
    top = G + M[:, Sa]
    bot = M[:, inv[Sa]]
    return np.vstack([top, bot])


def _cost(adj, G, D):
    """Vertices not reached from A_1 (node 0) or B_1 (node G) within D steps. Zero means valid."""
    N = adj.shape[0]
    total = 0
    for src in (0, G):
        seen = np.zeros(N, dtype=bool)
        seen[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(D):
            nb = adj[front].ravel()
            nb = nb[~seen[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            seen[nb] = True
            front = nb
        total += N - int(np.count_nonzero(seen))
    return total


def _anneal(M, inv, G, d, D, end, rng):
    """Anneal a connection set S of size d until cost 0. Returns S or None at the time limit."""
    S = rng.sample(range(G), d)
    c = _cost(_adj(M, inv, S, G), G, D)
    it = 0
    while c > 0:
        it += 1
        if (it & 31) == 0 and time.monotonic() >= end:
            return None
        T = max(0.15, 1.2 * (0.997 ** (it % 3000)))
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        T2 = S[:]
        T2[i] = x
        c2 = _cost(_adj(M, inv, T2, G), G, D)
        if c2 <= c or rng.random() < math.exp((c - c2) / T):
            S, c = T2, c2
    return S


def _bc_edges(M, S, G):
    Sa = np.asarray(S, dtype=np.int64)
    cols = M[:, Sa]
    us = np.repeat(np.arange(G, dtype=np.int64), len(S))
    vs = G + cols.ravel()
    return 2 * G, list(zip(us.tolist(), vs.tolist()))


# ----------------------------------------------------------------------------
# Main build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, list(e))
            best_n = n
            return True
        return False

    if D == 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
        except Exception:
            pass
        try:
            ar = _araujo(d)
            if ar is not None:
                consider(ar[0], ar[1])
        except Exception:
            pass

    if best_n >= moore:
        return best

    # Bold phase: bi-Cayley search targeting group orders that beat the record.
    if D >= 3 and d >= 3:
        half_moore = moore // 2
        lo0 = max(2 * d, int(0.44 * half_moore))
        target = max(best_n // 2 + 1, lo0)
        per_group = 1.5
        while time.monotonic() < deadline and best_n < moore:
            floor = max(best_n // 2 + 1, 2 * d)
            target = max(target, floor)
            if target > half_moore:
                break
            W = max(6, target // 40)
            specs = _specs(target, target + W, rng)
            found = False
            tried = 0
            for G, m, k, r in specs:
                if time.monotonic() >= deadline or tried >= 8:
                    break
                tried += 1
                M = _semidirect_table(m, k, r)
                inv = np.argmax(M == 0, axis=1)
                end = min(deadline, time.monotonic() + per_group)
                S = _anneal(M, inv, G, d, D, end, rng)
                if S is not None:
                    n, e = _bc_edges(M, S, G)
                    if consider(n, e):
                        found = True
                        break
            if found:
                target = max(target, best_n // 2 + 1)
            else:
                target = max(best_n // 2 + 1, int(target * 0.98))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
