import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over metacyclic groups Z_m x| Z_k.
#
# Vertices A_g and B_h (g, h in G). Connection set S of size d, with identity
# in S (WLOG by relabelling B). Edge A_g -- B_{g*s} for each s in S.
# Left translations are automorphisms, so the graph has diameter <= D iff
# every vertex is within D of A_0 and of B_0. The cost is the number of
# unreached vertices from those two sources, computed by numpy BFS.
# ----------------------------------------------------------------------------

def _groups_of_order(G):
    """All metacyclic groups Z_m x| Z_k of order G, as (m, k, r) with r^k = 1 mod m, gcd(r, m) = 1."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        if k == 1:
            out.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _mul_table(m, k, r):
    """Multiplication table T[x, y] of Z_m x| Z_k, element (a, b) coded as a*k + b (identity is 0)."""
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = (x // k)[:, None]
    b = (x % k)[:, None]
    a2 = (x // k)[None, :]
    b2 = (x % k)[None, :]
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    A = (a + pw[b] * a2) % m
    B = (b + b2) % k
    return A * k + B


def _bad(G, D, RS, RI):
    """Unreached (vertex, source) pairs from A_0 and B_0 within distance D.

    RS[j, g] = index of B-neighbour of A_g through dart j.
    RI[j, h] = index of A-neighbour of B_h through dart j.
    """
    total = 0
    for side in (0, 1):
        visA = np.zeros(G, dtype=bool)
        visB = np.zeros(G, dtype=bool)
        if side == 0:
            visA[0] = True
        else:
            visB[0] = True
        frontier = np.array([0], dtype=np.int64)
        cur = side  # 0: frontier lies in A; 1: frontier lies in B
        for _ in range(D):
            if frontier.size == 0:
                break
            hit = np.zeros(G, dtype=bool)
            if cur == 0:
                hit[RS[:, frontier]] = True
                new = hit & ~visB
                visB |= new
            else:
                hit[RI[:, frontier]] = True
                new = hit & ~visA
                visA |= new
            frontier = np.flatnonzero(new)
            cur ^= 1
        total += 2 * G - int(visA.sum()) - int(visB.sum())
    return total


def _search_group(G, d, D, T, rng, deadline):
    """Anneal a connection set S (identity plus d-1 others) so the bi-Cayley graph has diameter <= D.

    Returns S (list of ints) or None if the deadline passes first.
    """
    inv = np.argmax(T == 0, axis=1)

    def cost(S):
        Sa = np.array(S, dtype=np.int64)
        RS = T[:, Sa].T
        RI = T[:, inv[Sa]].T
        return _bad(G, D, RS, RI)

    S = [0] + rng.sample(range(1, G), d - 1)
    c = cost(S)
    best_c = c
    temp = 2.0
    since = 0
    while c > 0:
        if time.monotonic() >= deadline:
            return None
        i = rng.randrange(1, d)
        new = rng.randrange(1, G)
        if new in S:
            continue
        T2 = S.copy()
        T2[i] = new
        c2 = cost(T2)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / max(temp, 1e-6)):
            S, c = T2, c2
        if c < best_c:
            best_c = c
            since = 0
        else:
            since += 1
        if since > 3000:
            S = [0] + rng.sample(range(1, G), d - 1)
            c = cost(S)
            best_c = c
            temp = 2.0
            since = 0
        temp = max(0.05, temp * 0.9995)
    return S


def _edges_from(G, T, S):
    """Edge list of the bi-Cayley graph with connection set S: A_g = g, B_h = G + h."""
    E = []
    for s in S:
        col = T[:, s]
        for g in range(G):
            E.append((g, G + int(col[g])))
    return 2 * G, E


def _pick(groups, rng):
    """Pick a group, favouring non-cyclic ones (r != 1)."""
    nonab = [g for g in groups if g[2] != 1]
    if nonab and rng.random() < 0.75:
        return rng.choice(nonab)
    return rng.choice(groups)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 2.5))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2 or d == 1:
        return best_n, best_e

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e
            return True
        return False

    if D == 3:
        for q in range(min(d - 1, 30), 1, -1):
            if lib.is_prime_power(q) and q + 1 <= d:
                n, e = lib.projective_plane_incidence(q)
                consider(n, e)
                break
        if not lib.is_valid(best_n, best_e, d, D):
            return lib.haar_graph(d, range(d))
        return best_n, best_e

    # D >= 4: climb the group order G with bi-Cayley annealing.
    bound = 2 * sum((d - 1) ** i for i in range(D))
    best_G = best_n // 2
    step = 8
    slice_t = max(1.0, 0.06 * budget)
    rng = random.Random(seed * 1000003 + d * 101 + D)

    while time.monotonic() < deadline:
        G = max(d, best_G + step)
        if 2 * G > bound:
            if step <= 1:
                break
            step = max(1, step // 2)
            continue

        groups = _groups_of_order(G)
        if not groups:
            step = max(1, step // 2)
            continue

        found = None
        for _ in range(3):
            if time.monotonic() >= deadline:
                break
            m, k, r = _pick(groups, rng)
            T = _mul_table(m, k, r)
            t_end = min(deadline, time.monotonic() + slice_t)
            S = _search_group(G, d, D, T, rng, t_end)
            if S is not None:
                found = (T, S)
                break

        if found is None:
            step = max(1, step // 2)
        else:
            T, S = found
            n, e = _edges_from(G, T, S)
            if consider(n, e):
                best_G = n // 2
            step = min(16, step * 2)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
