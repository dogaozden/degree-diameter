import itertools
import math
import random
import time

import numpy as np

import lib


BIG = 10 ** 6


# ----------------------------------------------------------------------------
# Small baseline families (valid for D >= 3): projective plane and Araujo-Pardo-Lopez.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 (diameter 3), or None."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over small groups with a different search engine.
#
# A graph with k A-orbits and k B-orbits over a group G of order |G|:
#   A_{i,g} ~ B_{j, g*s} for every layer L, where j = perm[L][i], s = volt[L][i].
# Every layer contributes one edge per vertex, so degree = d (number of layers).
# Left multiplication by G is an automorphism, so validity only needs BFS from
# one representative of each orbit (k A-reps and k B-reps).
#
# Search: vectorised numpy BFS cost (unreached pairs + duplicate-edge penalty),
# annealed over voltages and per-layer B-assignments, with restarts. Groups are
# taken from a band of orders chosen so that 2*k*|G| would beat the current best.
# ----------------------------------------------------------------------------

def _is_prime(p):
    if p < 2:
        return False
    i = 2
    while i * i <= p:
        if p % i == 0:
            return False
        i += 1
    return True


def _group_band(lo, hi, cap=40):
    """Group specs with order in [lo, hi]: affine groups AGL(1,p) first, then semidirect products."""
    specs = []
    for p in range(3, hi + 2):
        o = p * (p - 1)
        if lo <= o <= hi and _is_prime(p):
            specs.append((o, ("aff", p)))
    for m in range(2, hi + 1):
        for k2 in range(1, hi // m + 1):
            o = m * k2
            if o < lo or o > hi:
                continue
            found = 0
            for r in range(1, m):
                if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                    specs.append((o, ("sd", m, k2, r)))
                    found += 1
                    if found >= 4:
                        break
    specs.sort(key=lambda t: (0 if t[1][0] == "aff" else 1, t[0]))
    return specs[:cap]


def _table(spec):
    """Vectorised multiplication table M (M[x, y] = x*y), inverse array, and identity check."""
    if spec[0] == "aff":
        p = spec[1]
        G = p * (p - 1)
        X = np.arange(G, dtype=np.int64)
        u = X // p + 1
        b = X % p
        uv = (u[:, None] * u[None, :]) % p
        M = ((uv - 1) * p + (u[:, None] * b[None, :] + b[:, None]) % p).astype(np.int64)
    else:
        _, m, k2, r = spec
        G = m * k2
        X = np.arange(G, dtype=np.int64)
        A = X // k2
        B = X % k2
        pw = np.array([pow(r, bb, m) for bb in range(k2)], dtype=np.int64)
        M = (((A[:, None] + pw[B][:, None] * A[None, :]) % m) * k2
             + (B[:, None] + B[None, :]) % k2).astype(np.int64)
    inv = np.argmax(M == 0, axis=1)
    ar = np.arange(G)
    ok = bool(np.array_equal(M[0], ar) and np.array_equal(M[:, 0], ar))
    return G, M, inv, ok


def _adj(G, k, M, inv, volt, perm, d):
    """Adjacency array of shape (2kG, d); column L is the neighbour through layer L."""
    adj = np.empty((2 * k * G, d), dtype=np.int64)
    for L in range(d):
        pl = perm[L]
        vl = volt[L]
        for i in range(k):
            j = pl[i]
            s = vl[i]
            adj[i * G:(i + 1) * G, L] = (k + j) * G + M[:, s]
            adj[(k + j) * G:(k + j + 1) * G, L] = i * G + M[:, inv[s]]
    return adj


def _cost(adj, G, k, D):
    """Unreached (source, vertex) pairs over orbit representatives; duplicates give a big penalty."""
    N = adj.shape[0]
    srt = np.sort(adj, axis=1)
    dup = int(np.count_nonzero(srt[:, 1:] == srt[:, :-1]))
    if dup:
        return BIG + dup
    total = 0
    srcs = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    for src in srcs:
        seen = np.zeros(N, dtype=bool)
        seen[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(D):
            mk = np.zeros(N, dtype=bool)
            mk[adj[front].ravel()] = True
            mk &= ~seen
            front = np.flatnonzero(mk)
            if front.size == 0:
                break
            seen |= mk
        total += N - int(np.count_nonzero(seen))
    return total


def _anneal(tab, k, d, D, deadline, rng, iters):
    """One annealing run over voltages and layer permutations. Returns (volt, perm) or None."""
    G, M, inv = tab
    volt = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    perm = [list(range(k)) for _ in range(d)]
    for pl in perm:
        rng.shuffle(pl)
    adj = _adj(G, k, M, inv, volt, perm, d)
    c = _cost(adj, G, k, D)
    T0 = 1.5
    for it in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        T = T0 * (1.0 - it / iters) + 0.05
        L = rng.randrange(d)
        if k > 1 and rng.random() < 0.3:
            a, b = rng.sample(range(k), 2)
            pl = perm[L]
            pl[a], pl[b] = pl[b], pl[a]
            adj2 = _adj(G, k, M, inv, volt, perm, d)
            c2 = _cost(adj2, G, k, D)
            if c2 <= c or rng.random() < math.exp((c - c2) / T):
                adj, c = adj2, c2
            else:
                pl[a], pl[b] = pl[b], pl[a]
        else:
            i = rng.randrange(k)
            old = volt[L][i]
            new = rng.randrange(G)
            if new == old:
                continue
            volt[L][i] = new
            adj2 = _adj(G, k, M, inv, volt, perm, d)
            c2 = _cost(adj2, G, k, D)
            if c2 <= c or rng.random() < math.exp((c - c2) / T):
                adj, c = adj2, c2
            else:
                volt[L][i] = old
    if c == 0:
        return volt, perm
    return None


def _search_spec(tab, k, d, D, end, rng):
    """Repeated annealing restarts on one group until success or time runs out."""
    while time.monotonic() < end:
        res = _anneal(tab, k, d, D, end, rng, iters=3000)
        if res is not None:
            return res
    return None


def _edges(G, k, M, volt, perm, d):
    E = []
    for L in range(d):
        for i in range(k):
            j = perm[L][i]
            s = volt[L][i]
            col = M[:, s].tolist()
            for g in range(G):
                E.append((i * G + g, (k + j) * G + col[g]))
    return 2 * k * G, E


# ----------------------------------------------------------------------------
# Main build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Bi-Cayley voltage lifts with a vectorised annealing search.
    if d >= 3 and D >= 2 and best_n < moore:
        tables = {}
        rnd = 0
        while time.monotonic() < deadline and best_n < moore:
            for k in (1, 2):
                if time.monotonic() >= deadline or best_n >= moore:
                    break
                lo = max(best_n // (2 * k) + 1, int(0.4 * moore / (2 * k)), 2)
                hi = lo + max(12, lo // 6)
                for o, spec in _group_band(lo, hi):
                    now = time.monotonic()
                    if now >= deadline:
                        break
                    if spec not in tables:
                        tables[spec] = _table(spec)
                    G, M, inv, ok = tables[spec]
                    if not ok:
                        continue
                    budget = min(deadline - now, 2.0 + 1.5 * rnd)
                    res = _search_spec((G, M, inv), k, d, D, now + budget, rng)
                    if res is not None:
                        volt, perm = res
                        n, e = _edges(G, k, M, volt, perm, d)
                        if consider(n, e):
                            break  # band moved up; recompute it for this k
            rnd += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
