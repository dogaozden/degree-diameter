import math
import random
import time

import lib


# ------------------------------------------------ Cayley-type bipartite search (D = 3)
#
# Graph on A = {a_g} and B = {b_g}, g in a group G of order N, with
#   a_g ~ b_{g s} for s in S, |S| = d (distinct).
# Left multiplication by G is an automorphism, and the graph is d-regular and bipartite.
# Diameter <= 3 holds iff (checked from a_e and b_e, using transitivity):
#   S S^-1 = G     (a-a distances up to 2)
#   S^-1 S = G     (b-b distances up to 2)
#   S ∪ S S^-1 S = G   (a-b distances 1 or 3)
# Any leftover mismatch is caught by lib.is_valid, so a wrong group table is only wasted time.


def _tables(N, mul, inv):
    """Multiplication table and inverse list for a group on elements 0..N-1."""
    T = [[mul(x, y) for y in range(N)] for x in range(N)]
    iv = [inv(x) for x in range(N)]
    return T, iv


def _cost(S, T, iv, N):
    """Number of group elements missed by the three covering conditions."""
    A = {T[s][iv[t]] for s in S for t in S}          # S S^-1
    B = {T[iv[s]][t] for s in S for t in S}          # S^-1 S
    C = {T[a][u] for a in A for u in S}              # S S^-1 S
    C.update(S)
    return (N - len(A)) + (N - len(B)) + (N - len(C))


def _anneal(d, N, T, iv, rng, deadline):
    """Find a d-subset S of G satisfying the covering conditions, or return None at the deadline."""
    S = rng.sample(range(N), d)
    cost = _cost(S, T, iv, N)
    steps = 0
    while cost > 0:
        if steps % 32 == 0 and time.monotonic() >= deadline:
            return None
        steps += 1
        idx = rng.randrange(d)
        new = rng.randrange(N)
        if new in S:
            continue
        S2 = S[:]
        S2[idx] = new
        c2 = _cost(S2, T, iv, N)
        if c2 <= cost or rng.random() < math.exp((cost - c2) / 0.5):
            S, cost = S2, c2
    return S


def _groups(N, rng):
    """Multiplication tables for several groups of order N: cyclic, and some Z_m x| Z_k."""
    out = []
    _, mul, inv = lib.cyclic_group(N)
    out.append(_tables(N, mul, inv))
    for k in range(2, N):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:2]:
            _, mul, inv = lib.semidirect_group(m, k, r)
            out.append(_tables(N, mul, inv))
    rng.shuffle(out)
    return out


def _group_phase(d, best, rng, deadline):
    """Sweep group orders N upward from just above the current best half-order.

    Each N gets an equal share of the remaining time, and within N each group gets a share.
    Returns the best valid (n, edges) found, or the input best.
    """
    best_n, best_edges = best
    cap = d * d - d + 1                 # |S S^-1| <= d^2 - d + 1
    floor = max(d, best_n // 2 + 1)     # need 2N > best_n
    for N in range(floor, cap + 1):
        now = time.monotonic()
        if now >= deadline:
            break
        share_end = now + (deadline - now) / (cap - N + 1)
        groups = _groups(N, rng)
        for gi, (T, iv) in enumerate(groups):
            now = time.monotonic()
            if now >= share_end:
                break
            g_end = now + (share_end - now) / (len(groups) - gi)
            S = _anneal(d, N, T, iv, rng, g_end)
            if S is None:
                continue
            edges = [(g, N + T[g][s]) for g in range(N) for s in S]
            n = 2 * N
            if n > best_n and lib.is_valid(n, edges, d, 3):
                best_n, best_edges = n, edges
            break  # success at this N; move on to the next order
    return best_n, best_edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 <= D.
    kdd = lib.haar_graph(d, range(d))
    if not lib.is_valid(kdd[0], kdd[1], d, D):
        kdd = (1, [])
    best = kdd

    if D == 3:
        # Structured floor: projective plane incidence or Araujo-Pardo-Lopez graph.
        base = None
        q = d - 1
        if q >= 2 and lib.is_prime_power(q):
            base = lib.projective_plane_incidence(q)
        elif d - 2 >= 3 and lib.is_prime_power(d - 2):
            base = lib.araujo_lopez_graph(d - 2)
        if base is not None and base[0] > best[0] and lib.is_valid(base[0], base[1], d, D):
            best = base

        # Main attempt: bipartite Cayley graphs over non-cyclic and cyclic groups.
        if d >= 3:
            best = _group_phase(d, best, rng, deadline)
    else:
        # Random Haar fallback for other diameters.
        m, misses = d + 1, 0
        while time.monotonic() < deadline and misses < 10:
            found = None
            for _ in range(30):
                if time.monotonic() >= deadline:
                    break
                S = [0] + rng.sample(range(1, m), d - 1)
                n, edges = lib.haar_graph(m, S)
                if lib.within_diameter(n, edges, D):
                    found = (n, edges)
                    break
            if found:
                if found[0] > best[0] and lib.is_valid(found[0], found[1], d, D):
                    best = found
                misses = 0
            else:
                misses += 1
            m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        return kdd
    return best
