import math
import random
import time

import lib

MAX_GROUPS = 6
T_START = 1.5
T_END = 0.05


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


def _largest_pg_q(d):
    """Largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _cost(nb, E, N, T, D, volts):
    """Unreached (source, vertex) pairs over the nb fibre-identity sources.

    Left translation is an automorphism of a voltage lift, so sources at
    the identity of each fibre suffice. Zero means diameter <= D.
    """
    V = nb * N
    adj = [[] for _ in range(V)]
    for (u, v), g in zip(E, volts):
        ub = u * N
        vb = v * N
        for x in range(N):
            a = ub + x
            b = vb + T[x][g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    for u in range(nb):
        src = u * N
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for a in frontier:
                for b in adj[a]:
                    if not seen[b]:
                        seen[b] = 1
                        nxt.append(b)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += V - count
    return total


def _anneal(nb, E, N, T, D, rng, deadline):
    """Time-scheduled annealing over the voltage of each base dart."""
    ne = len(E)
    volts = [rng.randrange(N) for _ in range(ne)]
    cost = _cost(nb, E, N, T, D, volts)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        temp = T_START * (T_END / T_START) ** min(1.0, (now - t0) / span)
        i = rng.randrange(ne)
        new = rng.randrange(N)
        old = volts[i]
        if new == old:
            continue
        volts[i] = new
        c2 = _cost(nb, E, N, T, D, volts)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            volts[i] = old
    return volts


def _try_order(nb, E, D, N, rng, deadline):
    """Try a few groups of order N; return (volts, order, mul) or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() >= deadline:
            break
        order, mul, _ = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(order)] for x in range(order)]
        volts = _anneal(nb, E, order, T, D, rng, deadline)
        if volts is not None:
            return volts, order, mul
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    q = _largest_pg_q(d)
    if q is None or D < 3:
        return best

    # Base: PG(2, q) incidence graph, (q+1)-regular, diameter 3.
    nb, E = lib.projective_plane_incidence(q)
    consider(nb, E)

    moore = lib._moore_bound(d, D)
    Nmax = moore // nb
    N = max(2, best[0] // nb + 1)

    # Ratchet: each success raises the target order; failures move on.
    while time.monotonic() < deadline and N <= Nmax:
        slice_end = min(deadline, time.monotonic() + max(1.0, 0.12 * budget))
        res = _try_order(nb, E, D, N, rng, slice_end)
        if res is not None:
            volts, order, mul = res
            darts = [(u, v, g) for (u, v), g in zip(E, volts)]
            n2, e2 = lib.group_lift(nb, darts, order, mul)
            consider(n2, e2)
            N = max(N + 1, best[0] // nb + 1)
        else:
            N += 1
            if N > Nmax:
                N = max(2, best[0] // nb + 1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
