import random
import time
from math import gcd

import lib


def _fallback(d, D):
    """Always-valid small graph: K_{d,d} (diameter 2), or a single edge / single vertex for tiny cases."""
    if d <= 0 or D <= 0:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    return lib.haar_graph(d, range(d))


def _direct(a, b):
    """Direct product Z_a x Z_b, element (i, j) coded as i*b + j, identity 0."""
    def mul(x, y):
        i, j = divmod(x, b)
        i2, j2 = divmod(y, b)
        return ((i + i2) % a) * b + (j + j2) % b

    def inv(x):
        i, j = divmod(x, b)
        return ((-i) % a) * b + (-j) % b

    return mul, inv


def _cyclic(N):
    """Cyclic group Z_N, identity 0."""
    return (lambda x, y: (x + y) % N), (lambda x: (-x) % N)


_SEMI_CACHE = {}


def _semi_options(N):
    """All (m, k, r) with m*k = N, k >= 2, m >= 2, r != 1, gcd(r, m) = 1, r^k = 1 mod m."""
    if N not in _SEMI_CACHE:
        opts = []
        for k in range(2, N + 1):
            if N % k:
                continue
            m = N // k
            if m < 2:
                continue
            for r in range(2, m):
                if gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    opts.append((m, k, r))
        _SEMI_CACHE[N] = opts
    return _SEMI_CACHE[N]


def _pick_group(N, rng):
    """Pick a random group of order N among cyclic, direct-product and semidirect-product options."""
    choices = [("c",)]
    for a in range(2, N):
        if N % a == 0 and N // a >= 2:
            choices.append(("d", a, N // a))
    choices += [("s",) + t for t in _semi_options(N)]
    ch = rng.choice(choices)
    if ch[0] == "c":
        return _cyclic(N)
    if ch[0] == "d":
        return _direct(ch[1], ch[2])
    _, m, k, r = ch
    _, mul, inv = lib.semidirect_group(m, k, r)
    return mul, inv


def _cost(N, S, mul, inv, D):
    """
    Bi-Cayley graph: A-vertex a ~ B-vertex b iff a^{-1} b in S (vertices a in 0..N-1, b as N+b).
    The group acts regularly on each side, so the diameter is <= D iff BFS from A-identity and
    from B-identity reaches everything within D steps. Returns the total number of unreached vertices.
    """
    invS = [inv(s) for s in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < N:
                    for s in S:
                        w = N + mul(v, s)
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    b = v - N
                    for t in invS:
                        w = mul(b, t)
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += 2 * N - cnt
    return total


def _search_group(N, d, D, rng, steps, deadline):
    """Random restart + hill climbing on the connection set S of size d in a random group of order N."""
    mul, inv = _pick_group(N, rng)
    S = rng.sample(range(N), d)
    c = _cost(N, S, mul, inv, D)
    for _ in range(steps):
        if c == 0 or time.monotonic() >= deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        T = S[:]
        T[i] = x
        c2 = _cost(N, T, mul, inv, D)
        if c2 <= c:
            S, c = T, c2
    if c == 0:
        return S, mul
    return None


def _edges(N, S, mul):
    return [(a, N + mul(a, s)) for a in range(N) for s in S]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit

    # Calibration: exact projective-plane incidence graph when D = 3 and d-1 is a prime power.
    try:
        if D == 3 and d >= 2 and lib.is_prime_power(d - 1):
            n, e = lib.projective_plane_incidence(d - 1)
            if lib.is_valid(n, e, d, D):
                return n, e
    except Exception:
        pass

    best = _fallback(d, D)
    try:
        if not lib.is_valid(best[0], best[1], d, D):
            best = (1, [])
    except Exception:
        best = (1, [])

    if d < 2 or D < 2:
        return best

    # Bold construction: bipartite Cayley (bi-Cayley) graphs over non-cyclic and cyclic groups,
    # searched by hill climbing on the connection set, ascending in group order N.
    # Graph has 2N vertices, degree d, and is bipartite by construction.
    rng = random.Random(seed)
    best_N = best[0] // 2
    N = max(d, best_N + 1)
    try:
        while time.monotonic() < deadline:
            res = None
            for _ in range(3):
                if time.monotonic() >= deadline:
                    break
                res = _search_group(N, d, D, rng, 150, deadline)
                if res:
                    break
            if res:
                S, mul = res
                n, e = 2 * N, _edges(N, S, mul)
                if lib.is_valid(n, e, d, D) and n > best[0]:
                    best = (n, e)
                    best_N = N
            N += 1
    except Exception:
        pass

    return best
