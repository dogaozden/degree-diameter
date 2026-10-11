import math
import random
import time

import lib


def _options(N):
    """Return (m, k, r) descriptions of groups of order N: Z_m x|_r Z_k with m*k = N (k = 1 is cyclic)."""
    opts = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    return opts


def _group(N, opt):
    """Multiplication table T and inverse list for the group described by opt (identity is element 0)."""
    m, k, r = opt
    if k == 1:
        _, mul, _ = lib.cyclic_group(N)
    else:
        _, mul, _ = lib.semidirect_group(m, k, r)
    T = [[mul(x, y) for y in range(N)] for x in range(N)]
    inv = [0] * N
    for x in range(N):
        row = T[x]
        for y in range(N):
            if row[y] == 0:
                inv[x] = y
                break
    return T, inv


def _bad(S, T, inv, N, D, src):
    """Number of vertices of the bi-Cayley graph not within distance D of src.

    Vertices: A_x = x (0..N-1), B_y = N + y. A_x ~ B_{x s} for s in S.
    """
    invS = [inv[s] for s in S]
    seen = bytearray(2 * N)
    seen[src] = 1
    frontier = [src]
    cnt = 1
    for _ in range(D):
        nxt = []
        for v in frontier:
            if v < N:
                row = T[v]
                for s in S:
                    w = N + row[s]
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            else:
                row = T[v - N]
                for si in invS:
                    w = row[si]
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
        cnt += len(nxt)
        if not nxt:
            break
        frontier = nxt
    return 2 * N - cnt


def _attempt(N, d, D, deadline, rng):
    """Search connection sets S (|S| = d) in random groups of order N by simulated annealing.

    Left translations are automorphisms, so checking the eccentricities of A_e and B_e
    suffices for diameter <= D. Returns (S, T, inv) on success, else None.
    """
    opts = _options(N)
    if not opts:
        return None
    while time.monotonic() < deadline:
        opt = rng.choice(opts)
        T, inv = _group(N, opt)

        def cost_fn(S):
            return _bad(S, T, inv, N, D, 0) + _bad(S, T, inv, N, D, N)

        sub_deadline = min(deadline, time.monotonic() + 4.0)
        S = rng.sample(range(N), d)
        cost = cost_fn(S)
        while cost > 0 and time.monotonic() < sub_deadline:
            i = rng.randrange(d)
            new = rng.randrange(N)
            if new in S:
                continue
            old = S[i]
            S[i] = new
            c2 = cost_fn(S)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / 0.6):
                cost = c2
            else:
                S[i] = old
        if cost == 0:
            return S, T, inv
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.8 * time_limit - 0.5)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # D = 3 with d - 1 a prime power: projective plane incidence graph (Moore optimal).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    # Bi-Cayley graphs: N group elements per side, degree d, so 2N vertices.
    # Bisection on N, where a successful N raises lo and a failure lowers hi.
    lo = d
    hi = lib._moore_bound(d, D) // 2
    while lo < hi and time.monotonic() < deadline:
        mid = (lo + hi + 1) // 2
        rem = deadline - time.monotonic()
        att_deadline = time.monotonic() + max(2.0, rem * 0.35)
        att_deadline = min(att_deadline, deadline)
        res = _attempt(mid, d, D, att_deadline, rng)
        ok = False
        if res is not None:
            S, T, inv = res
            edges = [(x, mid + T[x][s]) for x in range(mid) for s in S]
            n = 2 * mid
            if lib.is_valid(n, edges, d, D):
                consider(n, edges)
                ok = True
        if ok:
            lo = mid
        else:
            hi = mid - 1

    return best
