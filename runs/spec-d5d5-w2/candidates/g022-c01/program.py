import math
import random
import time

import lib


def _rot(x, s, N, full):
    """Rotate the N-bit set x by s: bit i moves to (i + s) mod N."""
    if s == 0:
        return x
    return ((x << s) | (x >> (N - s))) & full


def _unreached(N, S, D, full):
    """Pairs not within distance D in the cyclic bi-Cayley graph A_x ~ B_{x+s}, s in S.

    Translation is an automorphism, so checking eccentricities of A_0 and B_0 suffices.
    Returns 0 iff the graph has diameter <= D.
    """
    back = [(N - s) % N for s in S]
    total = 0
    for start_on_a in (True, False):
        if start_on_a:
            visA, visB = 1, 0
        else:
            visA, visB = 0, 1
        F = 1
        onA = start_on_a
        for _ in range(D):
            if onA:
                nb = 0
                for s in S:
                    nb |= _rot(F, s, N, full)
                nb &= full & ~visB
                visB |= nb
                F = nb
            else:
                na = 0
                for s in back:
                    na |= _rot(F, s, N, full)
                na &= full & ~visA
                visA |= na
                F = na
            onA = not onA
            if not F:
                break
        total += 2 * N - visA.bit_count() - visB.bit_count()
    return total


def _search(N, d, D, rng, deadline, iters):
    """Simulated annealing over connection sets S (0 fixed WLOG). Returns S or None."""
    full = (1 << N) - 1
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, S, D, full)
    T = 3.0
    for it in range(iters):
        if cur == 0:
            break
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, S2, D, full)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S, cur = S2, v
        T = max(0.3, T * 0.9995)
    return S if cur == 0 else None


def _cyclic_graph(N, S):
    """Bi-Cayley graph over Z_N: A_x joined to B_{x+s} for s in S."""
    edges = [(x, N + (x + s) % N) for x in range(N) for s in S]
    return 2 * N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        edges = [(i, (i + 1) % n) for i in range(n)]
        return n, edges

    # Safe fallback: K_{d,d} has diameter 2 and degree d.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    moore = lib.moore_bound(d, D)

    # Structured baseline for D = 3: incidence graph of PG(2, q), q + 1 <= d.
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n2, e2 = lib.projective_plane_incidence(q)
                consider(n2, e2)
                break

    # Cyclic bi-Cayley annealing: aim for orders strictly above the current best.
    N = max(d, best[0] // 2 + 1)
    while time.monotonic() < deadline:
        if 2 * N > moore:
            break
        slice_end = min(deadline, time.monotonic() + max(1.0, budget / 4.0))
        S = _search(N, d, D, rng, slice_end, 20000)
        if S is not None:
            n2, e2 = _cyclic_graph(N, S)
            if lib.is_valid(n2, e2, d, D):
                best = (n2, e2)
                N = max(N + 1, best[0] // 2 + 1)
                continue

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
