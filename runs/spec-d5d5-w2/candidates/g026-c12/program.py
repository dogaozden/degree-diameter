import math
import random
import time

import lib


ITERS = 5000
_KS = (1, 2, 3, 4)


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (degree q + 1 <= d)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _rot(x, s, N, full):
    """Rotate the N-bit mask x so that bit p moves to bit (p + s) mod N."""
    if s == 0:
        return x
    return ((x << s) | (x >> (N - s))) & full


def _uncovered(N, k, D, darts, full, total):
    """Number of (source, vertex) pairs not within distance D, over the 2k base sources.

    The lift is a bi-cyclic graph: A_{i,x} ~ B_{j,x+s} for every dart (i, j, s).
    Translations are automorphisms, so checking the base vertices A_{i,0} and B_{j,0}
    is enough. darts holds tuples (i, j, s, t) with t = (-s) mod N.
    """
    bad = 0
    for side in (0, 1):
        for src in range(k):
            A = [0] * k
            B = [0] * k
            if side == 0:
                A[src] = 1
            else:
                B[src] = 1
            for _ in range(D):
                nA = A[:]
                nB = B[:]
                for i, j, s, t in darts:
                    nB[j] |= _rot(A[i], s, N, full)
                    nA[i] |= _rot(B[j], t, N, full)
                if nA == A and nB == B:
                    break
                A, B = nA, nB
            cnt = sum(x.bit_count() for x in A) + sum(x.bit_count() for x in B)
            bad += total - cnt
    return bad


def _anneal(d, D, k, N, rng, deadline, iters):
    """Anneal voltages and layer permutations of a k-base bi-cyclic lift over Z_N.

    Layer L pairs A_i with B_{perm[L][i]} through voltage volt[L][i]; every layer is a
    permutation, so every vertex has degree d. Returns (n, edges) with zero uncovered
    pairs, or None.
    """
    full = (1 << N) - 1
    total = 2 * k * N
    perm = [rng.sample(range(k), k) for _ in range(d)]
    volt = [[rng.randrange(N) for _ in range(k)] for _ in range(d)]

    def cost():
        darts = []
        for L in range(d):
            for i in range(k):
                s = volt[L][i]
                darts.append((i, perm[L][i], s, (N - s) % N))
        # Repeated (i, j, s) produce duplicate edges, which lower the degree; penalise them.
        dup = len(darts) - len({(a, b, c) for a, b, c, _ in darts})
        return _uncovered(N, k, D, darts, full, total) + 4 * total * dup

    cur = cost()
    T0 = max(1.0, 0.02 * cur)
    T_end = 0.3
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for it in range(iters):
        if cur == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)
        if k > 1 and rng.random() < 0.4:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            row = perm[L]
            row[a], row[b] = row[b], row[a]
            c2 = cost()
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                row[a], row[b] = row[b], row[a]
        else:
            L = rng.randrange(d)
            i = rng.randrange(k)
            old = volt[L][i]
            new = rng.randrange(N)
            if new == old:
                continue
            volt[L][i] = new
            c2 = cost()
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                cur = c2
            else:
                volt[L][i] = old

    if cur != 0:
        return None
    E = set()
    for L in range(d):
        for i in range(k):
            j = perm[L][i]
            s = volt[L][i]
            for x in range(N):
                E.add((i * N + x, (k + j) * N + (x + s) % N))
    return 2 * k * N, sorted(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: multi-base bi-cyclic lifts over Z_N, evaluated with big-int bitsets.
    ks = _KS
    Nt = {k: 0 for k in ks}
    fails = {k: 0 for k in ks}
    slice_len = max(0.5, budget / 20.0)
    try:
        rnd = 0
        while best[0] < moore and time.monotonic() < deadline:
            k = ks[rnd % len(ks)]
            rnd += 1
            lower = best[0] // (2 * k) + 1
            N = max(Nt[k], lower, d + 1)
            if 2 * k * N > moore:
                continue
            until = min(deadline, time.monotonic() + slice_len)
            res = _anneal(d, D, k, N, rng, until, ITERS)
            if res is not None:
                consider(res[0], res[1])
                fails[k] = 0
                Nt[k] = N + max(1, N // 40)
            else:
                fails[k] += 1
                Nt[k] = N
                if fails[k] % 6 == 0:
                    Nt[k] = max(lower, N - 1)
    except Exception:
        pass  # keep the best valid graph found so far

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
