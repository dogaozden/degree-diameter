import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline: projective plane incidence graphs (optimal for D = 3 when
# d - 1 is a prime power). Haar graph K_{d,d} is the universal fallback.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if q > 60:
            continue
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New construction: bi-Cayley lifts over semidirect products Z_m x| Z_k2,
# optimised by exhaustive coordinate descent with iterated local search.
#
# Vertices: A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h, for i, j < k.
# For each layer l (d of them) there is a permutation pi_l of the k blocks and
# a voltage s_{l,i}: A_{i,g} ~ B_{pi_l(i), g*s}. Each layer is a perfect
# matching-like map, so every vertex has degree exactly d (before duplicate
# checks). Left multiplication is an automorphism, so only the k block
# representatives (group identity, index 0) need BFS.
#
# Unlike simulated annealing, every move scans all G voltages of one dart and
# takes the best one (random tie-breaks), and the search restarts from the best
# state with a small kick.
# ----------------------------------------------------------------------------

_POP = np.array([bin(x).count("1") for x in range(64)], dtype=np.int64)
_K2_CHOICES = [1, 2, 2, 3, 4, 4, 6, 6, 7, 8, 9, 10, 12]
_MAX_G = 1400
_DUP_PENALTY = 10 ** 6


def _sample_group(target, rng):
    """Return (m, k2, r) describing Z_m x| Z_k2 of order >= target, or None."""
    for _ in range(100):
        k2 = rng.choice(_K2_CHOICES)
        m = max(2, -(-target // k2) + rng.randrange(0, 2))
        if m * k2 > _MAX_G:
            continue
        if k2 == 1:
            return m, 1, 1
        if k2 == 2:
            return m, 2, m - 1  # dihedral group, always valid
        for _ in range(200):
            r = rng.randrange(1, m)
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                return m, k2, r
    return None


def _tables(m, k2, r):
    """Return (G, Tm, Inv): Tm[s, g] = g*s and Inv[s, h] = g with g*s = h."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    pw = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    mul = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Tm = np.ascontiguousarray(mul.T)
    Inv = np.empty((G, G), dtype=np.int64)
    for s in range(G):
        Inv[s, Tm[s]] = x
    return G, Tm, Inv


def _attempt(d, D, k, G, Tm, Inv, rng, deadline):
    """Coordinate-descent + iterated local search over voltages and block layers.
    Returns (n, edges) on success (diameter D, degree d, no duplicates), else None."""
    N = 2 * k * G
    nbr = np.empty((d, N), dtype=np.int64)
    pi = [rng.sample(range(k), k) for _ in range(d)]
    sv = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]

    def fill(l, i):
        j = pi[l][i]
        s = sv[l][i]
        nbr[l, i * G:(i + 1) * G] = (k + j) * G + Tm[s]
        nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Inv[s]

    def fill_all():
        for l in range(d):
            for i in range(k):
                fill(l, i)

    def cost():
        R = np.zeros(N, dtype=np.int64)
        for b in range(2 * k):
            R[b * G] = 1 << b
        for _ in range(D):
            new = R.copy()
            for l in range(d):
                new |= R[nbr[l]]
            if np.array_equal(new, R):
                break
            R = new
        unreached = 2 * k * N - int(_POP[R].sum())
        keys = {(i, pi[l][i], sv[l][i]) for l in range(d) for i in range(k)}
        dups = d * k - len(keys)
        return unreached + _DUP_PENALTY * dups

    fill_all()
    cur = cost()
    best_cost = cur
    best_pi = [list(p) for p in pi]
    best_sv = [list(s) for s in sv]

    while cur > 0 and time.monotonic() < deadline:
        improved = True
        while improved and cur > 0 and time.monotonic() < deadline:
            improved = False
            darts = [(l, i) for l in range(d) for i in range(k)]
            rng.shuffle(darts)
            for l, i in darts:
                if cur == 0 or time.monotonic() > deadline:
                    break
                before = cur
                old = sv[l][i]
                bs, bc = old, cur
                for s in range(G):
                    if s == old:
                        continue
                    sv[l][i] = s
                    fill(l, i)
                    c = cost()
                    if c < bc:
                        bc, bs = c, s
                    elif c == bc and rng.random() < 0.2:
                        bs = s
                sv[l][i] = bs
                fill(l, i)
                cur = bc
                if cur < before:
                    improved = True

        if cur < best_cost:
            best_cost = cur
            best_pi = [list(p) for p in pi]
            best_sv = [list(s) for s in sv]
        if cur == 0 or time.monotonic() > deadline:
            break

        # Iterated local search: restore the best state and kick it.
        for l in range(d):
            pi[l][:] = best_pi[l]
            sv[l][:] = best_sv[l]
        fill_all()
        for _ in range(rng.randint(1, 3)):
            l = rng.randrange(d)
            i = rng.randrange(k)
            sv[l][i] = rng.randrange(G)
            fill(l, i)
        cur = cost()

    if cur != 0:
        return None
    edges = set()
    for u in range(N):
        for v in nbr[:, u].tolist():
            edges.add((u, v) if u < v else (v, u))
    return N, sorted(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Universal fallback: K_{d,d} has degree d and diameter 2 <= D.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if lib.is_prime_power(d - 1):
            return best

    try:
        kchoices = [1, 2, 2, 3, 3]
        while time.monotonic() < deadline - 1.0:
            k = rng.choice(kchoices)
            base = best_n // (2 * k)
            target = max(2, base + 1 + rng.randrange(0, base // 25 + 2))
            g = _sample_group(target, rng)
            if g is None:
                continue
            m, k2, r = g
            G, Tm, Inv = _tables(m, k2, r)
            if 2 * k * G <= best_n:
                continue
            slice_end = min(deadline, time.monotonic() + 10.0)
            res = _attempt(d, D, k, G, Tm, Inv, rng, slice_end)
            if res is not None:
                consider(res[0], res[1])
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
