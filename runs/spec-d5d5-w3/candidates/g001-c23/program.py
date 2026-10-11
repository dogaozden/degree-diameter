import math
import random
import time

import lib


def _make_group(m, k, r):
    """Semidirect product Z_m x|_r Z_k on codes a*k+b. Requires r^k = 1 mod m and gcd(r, m) = 1."""
    powers = [pow(r, b, m) for b in range(k)]

    def mul(x, y):
        a, b = divmod(x, k)
        c, e = divmod(y, k)
        return ((a + powers[b] * c) % m) * k + (b + e) % k

    def inv(x):
        a, b = divmod(x, k)
        nb = (-b) % k
        return ((-powers[nb] * a) % m) * k + nb

    return mul, inv


def _groups_of_order(N):
    """All (m, k, r) with m*k = N that give a valid semidirect product (cyclic when r = 1, k = 1)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) != 1:
                continue
            if pow(r, k, m) != 1 % m:
                continue
            out.append((m, k, r))
    return out


def _arrays(N, mul, inv, cache, s):
    """For connection element s: ra[x] = x*s (B-index), rb[y] = y*s^-1 (A-index). Cached per group."""
    t = cache.get(s)
    if t is None:
        si = inv(s)
        t = ([mul(x, s) for x in range(N)], [mul(y, si) for y in range(N)])
        cache[s] = t
    return t


def _score(S, N, D, arr):
    """Number of unreached vertices from a_e and b_e within distance D (0 iff valid).

    The bi-Cayley graph a_x ~ b_{x s}, s in S, is invariant under left multiplication,
    so it is vertex-transitive on each side; BFS from one A and one B vertex suffices.
    """
    pairs = [arr(s) for s in S]
    total = 0
    for start in (0, N):
        seen = {start}
        frontier = [start]
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < N:
                    cand = [N + p[0][v] for p in pairs]
                else:
                    y = v - N
                    cand = [p[1][y] for p in pairs]
                for w in cand:
                    if w not in seen:
                        seen.add(w)
                        nxt.append(w)
            if not nxt:
                break
            frontier = nxt
        total += 2 * N - len(seen)
    return total


def _climb(N, d, D, arr, rng, steps, deadline):
    """Hill-climb a connection set S of size d in Z-group of order N to zero score."""
    S = rng.sample(range(N), d)
    f = _score(S, N, D, arr)
    for _ in range(steps):
        if f == 0:
            return S
        if time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        new = rng.randrange(N)
        if new in S:
            continue
        S2 = S[:]
        S2[i] = new
        f2 = _score(S2, N, D, arr)
        if f2 <= f:
            S, f = S2, f2
    return S if f == 0 else None


def _construct(N, S, mul):
    edges = [(x, N + mul(x, s)) for x in range(N) for s in S]
    return 2 * N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 4.0)

    # Exact optimum for the D = 3 projective-plane case.
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    rng = random.Random(seed)

    nmax = lib.moore_bound(d, D) // 2   # group order N gives 2N vertices
    N = max(d, nmax // 4)
    fails = 0

    while N <= nmax and fails < 4 and time.monotonic() < deadline:
        found = None
        group_deadline = min(deadline, time.monotonic() + 2.5)
        groups = _groups_of_order(N)
        rng.shuffle(groups)
        if not groups:
            fails += 1
            N += 1
            continue
        tries = 0
        while found is None and time.monotonic() < group_deadline:
            m, k, r = groups[tries % len(groups)]
            tries += 1
            mul, inv = _make_group(m, k, r)
            cache = {}
            arr = lambda s, N=N, mul=mul, inv=inv, cache=cache: _arrays(N, mul, inv, cache, s)
            S = _climb(N, d, D, arr, rng, 600, group_deadline)
            if S is not None:
                n, edges = _construct(N, S, mul)
                if lib.is_valid(n, edges, d, D):
                    found = (n, edges)
        if found is not None:
            best = found
            fails = 0
        else:
            fails += 1
        N += 1

    n, edges = best
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return lib.haar_graph(d, range(d))
