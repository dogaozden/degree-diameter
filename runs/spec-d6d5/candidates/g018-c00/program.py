import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New family: abelian cyclic k-block bi-lifts with bitset reachability.
#
# Vertices: A_{i,g} = i*m + g and B_{j,h} = k*m + j*m + h, with g, h in Z_m.
# The base has d layers. Layer L is a permutation sig[L] of range(k), and the
# dart (i, sig[L][i], volt[L][i]) joins A_{i,g} to B_{sig[L][i], g+volt}.
# Every A and B vertex has degree d. The graph is invariant under translating
# Z_m, so checking BFS from A_{i,0} and B_{j,0} for all i, j is enough.
# Reachability uses Python big-int bitsets with cyclic shifts.
# ----------------------------------------------------------------------------


def _moore(d, D):
    """Moore-type bound used only as an early-exit target."""
    if D <= 0:
        return 1
    if d <= 1:
        return 2
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _consider(best, cand, d, D):
    """Keep cand if it is valid and larger than best."""
    n, e = cand
    if n > best[0] and lib.is_valid(n, e, d, D):
        return (n, e)
    return best


def _bfs_bad(k, m, D, byA, byB, full, side, idx):
    """Number of vertices not within D hops of the source block vertex (block idx, g = 0)."""
    RA = [0] * k
    RB = [0] * k
    F = [0] * k
    F[idx] = 1
    if side == 0:
        RA[idx] = 1
    else:
        RB[idx] = 1
    cur = side
    for _ in range(D):
        N = [0] * k
        if cur == 0:
            for i in range(k):
                f = F[i]
                if f:
                    for j, s in byA[i]:
                        N[j] |= ((f << s) | (f >> (m - s))) & full
            for j in range(k):
                x = N[j] & ~RB[j]
                RB[j] |= x
                N[j] = x
        else:
            for j in range(k):
                f = F[j]
                if f:
                    for i, ns in byB[j]:
                        N[i] |= ((f << ns) | (f >> (m - ns))) & full
            for i in range(k):
                x = N[i] & ~RA[i]
                RA[i] |= x
                N[i] = x
        F = N
        cur ^= 1
        if not any(F):
            break
    reached = 0
    for x in RA:
        reached += x.bit_count()
    for x in RB:
        reached += x.bit_count()
    return 2 * k * m - reached


def _cost(k, m, d, D, sig, volt, full):
    """Total unreached (source, vertex) pairs plus a penalty per duplicate dart. Zero means valid."""
    byA = [[] for _ in range(k)]
    byB = [[] for _ in range(k)]
    seen = set()
    dup = 0
    for L in range(d):
        sL = sig[L]
        vL = volt[L]
        for i in range(k):
            j = sL[i]
            s = vL[i]
            key = (i, j, s)
            if key in seen:
                dup += 1
            else:
                seen.add(key)
            byA[i].append((j, s))
            byB[j].append((i, (m - s) % m))
    total = dup * m
    for side in (0, 1):
        for idx in range(k):
            total += _bfs_bad(k, m, D, byA, byB, full, side, idx)
    return total


def _anneal(k, m, d, D, rng, deadline, iters):
    """Simulated annealing over voltages and layer permutations. Returns (sig, volt, cost)."""
    full = (1 << m) - 1
    sig = [rng.sample(range(k), k) for _ in range(d)]
    volt = [[rng.randrange(m) for _ in range(k)] for _ in range(d)]
    cost = _cost(k, m, d, D, sig, volt, full)
    T0 = 2.0
    for it in range(iters):
        if cost == 0:
            break
        if (it & 63) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (1.0 - it / iters) + 0.02
        L = rng.randrange(d)
        if k == 1 or rng.random() < 0.6:
            i = rng.randrange(k)
            old = volt[L][i]
            new = rng.randrange(m)
            if new == old:
                continue
            volt[L][i] = new
            c2 = _cost(k, m, d, D, sig, volt, full)
            if c2 <= cost or rng.random() < math.exp((cost - c2) / T):
                cost = c2
            else:
                volt[L][i] = old
        else:
            i, i2 = rng.sample(range(k), 2)
            sL = sig[L]
            sL[i], sL[i2] = sL[i2], sL[i]
            c2 = _cost(k, m, d, D, sig, volt, full)
            if c2 <= cost or rng.random() < math.exp((cost - c2) / T):
                cost = c2
            else:
                sL[i], sL[i2] = sL[i2], sL[i]
    return sig, volt, cost


def _lift_graph(k, m, d, sig, volt):
    """Materialise the bi-lift as (n, edges)."""
    E = set()
    for L in range(d):
        for i in range(k):
            j = sig[L][i]
            s = volt[L][i]
            for g in range(m):
                E.add((i * m + g, k * m + j * m + (g + s) % m))
    return 2 * k * m, sorted(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    kn, ke = lib.haar_graph(d, range(d))
    best = (kn, ke)
    target = _moore(d, D)
    if best[0] >= target:
        return best

    if d == 2:
        n = 2 * D
        best = _consider(best, (n, [(i, (i + 1) % n) for i in range(n)]), d, D)
        return best

    # Diameter-3 algebraic candidates (valid for any D >= 3).
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                best = _consider(best, lib.projective_plane_incidence(q), d, D)
                break
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                best = _consider(best, lib.araujo_lopez_graph(d - 2), d, D)
            except Exception:
                pass
    if best[0] >= target:
        return best

    # Bi-lift search with bitset reachability.
    budget = max(0.5, min(0.8 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)
    ks = [1, 1, 2, 2, 3, 3, 4, 5, 6]
    m_target = {}
    try:
        while time.monotonic() < deadline and best[0] < target:
            k = rng.choice(ks)
            if k not in m_target:
                m_target[k] = max(2, best[0] // (2 * k))
            m = max(m_target[k], best[0] // (2 * k) + 1, 2)
            slice_end = min(deadline, time.monotonic() + max(1.5, 0.08 * budget))
            sig, volt, c = _anneal(k, m, d, D, rng, slice_end, 20000)
            if c == 0:
                n, e = _lift_graph(k, m, d, sig, volt)
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
                m_target[k] = m + max(1, m // 50)
            else:
                if rng.random() < 0.5:
                    m_target[k] = max(2, m - max(1, m // 100))
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
