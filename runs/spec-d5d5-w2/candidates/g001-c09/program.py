import math
import random
import time

import numpy as np

import lib


def _build_group(m, k, r):
    """Multiplication and inverse tables of Z_m x|_r Z_k, element (a, b) coded as a*k+b."""
    N = m * k
    idx = np.arange(N, dtype=np.int64)
    a = idx // k
    b = idx % k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    tab = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    inv = np.argmax(tab == 0, axis=1)
    return tab.tolist(), inv.tolist()


def _group_specs(N, rng):
    """Candidate (m, k, r) semidirect products of total order N (k=1 gives the cyclic group)."""
    specs = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if k == 1:
            specs.append((N, 1, 1))
            continue
        if m == 1:
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
        rng.shuffle(rs)
        specs.extend((m, k, r) for r in rs[:6])
    return specs


def _local_search(tab, inv, N, d, D, rng, end):
    """Bi-Cayley graph: A_x ~ B_{x*s} for s in S. Vertex-transitive on each side, so the
    diameter is <= D iff both BFS balls from A_e and B_e cover everything within D."""

    def cost(S):
        invS = [inv[s] for s in S]
        total = 0
        for src in (0, N):
            seen = bytearray(2 * N)
            seen[src] = 1
            frontier = [src]
            cnt = 1
            for _ in range(D):
                nxt = []
                for u in frontier:
                    if u < N:
                        row = tab[u]
                        for s in S:
                            v = N + row[s]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
                    else:
                        row = tab[u - N]
                        for si in invS:
                            v = row[si]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
                if not nxt:
                    break
                cnt += len(nxt)
                frontier = nxt
            total += 2 * N - cnt
        return total

    S = [0] + rng.sample(range(1, N), d - 1)   # identity in S is WLOG
    cur = cost(S)
    stall = 0
    while cur:
        if stall >= 150 or time.monotonic() >= end:
            return None
        i = rng.randrange(1, d)
        t = rng.randrange(1, N)
        while t in S:
            t = rng.randrange(1, N)
        S2 = S[:]
        S2[i] = t
        c2 = cost(S2)
        if c2 <= cur:
            stall = stall + 1 if c2 == cur else 0
            S, cur = S2, c2
        else:
            stall += 1
    return S


def _try_order(N, d, D, rng, end, specs_cache):
    if N not in specs_cache:
        specs_cache[N] = _group_specs(N, rng)
    specs = specs_cache[N]
    while time.monotonic() < end:
        m, k, r = rng.choice(specs)
        tab, inv = _build_group(m, k, r)
        S = _local_search(tab, inv, N, d, D, rng, end)
        if S is not None:
            return S, tab
    return None


def _edges(N, S, tab):
    edges = []
    for x in range(N):
        row = tab[x]
        for s in S:
            edges.append((x, N + row[s]))
    return 2 * N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.8 * time_limit, time_limit - 5))

    if d <= 0 or D <= 0:
        return 1, []

    # Optimal D = 3 construction when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    # Safe fallback chain: K_{d,d} (diameter 2), else K_{1,1}.
    best = None
    if D >= 2:
        n, e = lib.haar_graph(d, range(d))
        if lib.is_valid(n, e, d, D):
            best = (n, e)
    if best is None:
        if lib.is_valid(2, [(0, 1)], d, D):
            best = (2, [(0, 1)])
        else:
            return 1, []

    if d < 2:
        return best

    rng = random.Random(seed)
    hi = lib.moore_bound(d, D) // 2      # bipartite: n = 2N <= Moore bound
    lo = d + 1
    if hi < lo:
        return best

    specs_cache = {}

    def attempt(N, end):
        res = _try_order(N, d, D, rng, end, specs_cache)
        if res is None:
            return None
        S, tab = res
        n, e = _edges(N, S, tab)
        if lib.is_valid(n, e, d, D):
            return (n, e)
        return None

    # Stage 1: descend from the Moore-type ceiling until something valid appears.
    Ns = list(range(hi, lo - 1, -1))
    found = None
    for idx, N in enumerate(Ns):
        now = time.monotonic()
        if now >= deadline:
            break
        left = len(Ns) - idx
        budget = min(0.5, 0.5 * (deadline - now) / left)
        res = attempt(N, now + max(0.02, budget))
        if res is not None:
            best = res
            found = N
            break

    # Stage 2: push upward from the first success with the remaining time.
    if found is not None:
        N = found + 1
        while N <= hi and time.monotonic() < deadline:
            res = attempt(N, min(deadline, time.monotonic() + 3.0))
            if res is not None and res[0] > best[0]:
                best = res
            N += 1

    return best
