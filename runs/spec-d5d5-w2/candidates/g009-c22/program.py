import math
import random
import time

import itertools

import lib


# ----------------------------------------------------------------------------
# NEW HELPER: bitset ball evaluation for cyclic Bi-Cayley lifts.
#
# Vertices A_x = x and B_y = N + y (x, y in Z_N); A_x ~ B_{x+s} for s in S.
# The ball of radius D around a source is held as two N-bit integers (one per
# side). Translation by s is a cyclic rotation of an N-bit integer, so one BFS
# step costs about 2|S| big-int shifts instead of a Python loop over vertices.
# Translation invariance means only the sources A_0 and B_0 need checking.
# ----------------------------------------------------------------------------

def _rot(F, s, N, full):
    """Cyclic rotation of an N-bit set: bit i moves to (i + s) mod N."""
    if s == 0:
        return F
    return ((F << s) | (F >> (N - s))) & full


def _cyc_cost(N, S, D, full):
    """Number of vertex pairs (source, target) not within distance D, sources A_0 and B_0."""
    neg = [(N - s) % N for s in S]
    total = 0
    for A, B in ((1, 0), (0, 1)):
        for _ in range(D):
            nA, nB = A, B
            for s in neg:          # A-vertices adjacent to B-set: A_{y-s}
                nA |= _rot(B, s, N, full)
            for s in S:            # B-vertices adjacent to A-set: B_{x+s}
                nB |= _rot(A, s, N, full)
            if nA == A and nB == B:
                break
            A, B = nA, nB
        total += 2 * N - A.bit_count() - B.bit_count()
    return total


def _cyc_anneal(N, d, D, rng, deadline, iters):
    """Annealed search for a connection set S in Z_N with |S| = d and zero unreached pairs."""
    full = (1 << N) - 1
    S = [0] + rng.sample(range(1, N), d - 1)   # 0 in S is WLOG (translate B side)
    cur = _cyc_cost(N, S, D, full)
    best_v, best_S = cur, list(S)
    T0 = 2.0 + 0.1 * cur
    for step in range(iters):
        if cur == 0:
            break
        if (step & 127) == 0 and time.monotonic() > deadline:
            break
        temp = T0 * (1.0 - step / iters) + 0.3
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        old = S[i]
        S[i] = c
        v = _cyc_cost(N, S, D, full)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-min(50.0, delta / temp)):
            cur = v
            if cur < best_v:
                best_v, best_S = cur, list(S)
        else:
            S[i] = old
    return best_S if best_v == 0 else None


def _cyc_search(N, d, D, rng, deadline):
    """Repeated annealing runs on Z_N until a valid S is found or the deadline passes."""
    while time.monotonic() < deadline:
        S = _cyc_anneal(N, d, D, rng, deadline, 1500)
        if S is not None:
            return [(x, N + (x + s) % N) for x in range(N) for s in S]
    return None


# ----------------------------------------------------------------------------
# Projective-plane start for D = 3 (calibration case d = 3, D = 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x|_r Z_k (non-cyclic groups), kept for variety.
# ----------------------------------------------------------------------------

MAX_GROUPS = 12
CLIMB_ITERS = 1000
_TABLE_CACHE = {}


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(m, k, r):
    """Cached (order, mul, T, invs) for Z_m x|_r Z_k."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, mul, T, invs)
    if len(_TABLE_CACHE) >= 48:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


def _unreached(N, T, invs, S, D):
    """Unreached pairs from A_0 and B_0 for a Bi-Cayley graph over a group of order N."""
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _climb(N, T, invs, d, D, rng, iters, deadline):
    """Simulated annealing over S for a non-cyclic semidirect group."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    best_S, best_v = S, cur
    T0 = 4.0 + 0.05 * cur
    for step in range(iters):
        if best_v == 0 or time.monotonic() > deadline:
            break
        temp = T0 * (1.0 - step / iters) + 0.2
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S, cur = S2, v
            if cur < best_v:
                best_S, best_v = S, cur
    return best_S if best_v == 0 else None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    tried = {}
    try:
        while best[0] < moore and time.monotonic() < deadline:
            n_best = best[0]
            lo = n_best // 2 + 1
            if lo > moore // 2:
                break
            window = max(3, lo // 40)
            hi = min(lo + window, moore // 2 + 1)
            N = min(range(lo, hi), key=lambda x: (tried.get(x, 0), rng.random()))
            tried[N] = tried.get(N, 0) + 1
            if N < d:
                continue

            now = time.monotonic()
            slice_len = max(1.5, budget / 25.0)
            attempt_deadline = min(deadline, now + slice_len)

            if rng.random() < 0.7:
                # New helper: cyclic Bi-Cayley lift with bitset ball evaluation.
                edges = _cyc_search(N, d, D, rng, attempt_deadline)
                if edges is not None:
                    consider(2 * N, edges)
            else:
                # Non-cyclic semidirect Bi-Cayley lift.
                groups = _groups(N)
                rng.shuffle(groups)
                found = None
                for m, k2, r in groups[:MAX_GROUPS]:
                    if time.monotonic() > attempt_deadline:
                        break
                    _, _, T, invs = _tables(m, k2, r)
                    S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, attempt_deadline)
                    if S is not None:
                        found = (T, S)
                        break
                if found is not None:
                    T, S = found
                    edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                    consider(2 * N, edges)
    except Exception:
        pass  # keep the best valid graph found so far

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
