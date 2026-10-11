import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over semidirect products Z_m x| Z_k, with k = 1 on each side.
#
# Vertices A_g and B_h (g, h in G). Connection set S of size d (distinct elements).
# Edge A_g -- B_{g*s} for s in S. Left multiplication is an automorphism, so
# checking eccentricities of A_e and B_e (each within D) certifies diameter <= D.
# Search over S by simulated annealing with a fast numpy BFS.
# ----------------------------------------------------------------------------

def _table(m, k, r):
    """Multiplication table of Z_m x|_r Z_k, element (a, b) coded as a*k + b."""
    x = np.arange(m * k, dtype=np.int64)
    a, b = x // k, x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    A = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    Bm = (b[:, None] + b[None, :]) % k
    return A * k + Bm


def _inverse(table):
    """inv[x] = y with table[x, y] == identity (code 0)."""
    return np.argmax(table == 0, axis=1)


def _group_candidates(G, rng, limit):
    """Semidirect products Z_m x| Z_k of order G; non-abelian ones are preferred."""
    nonab, ab = [], []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        if k == 1:
            ab.append((m, 1, 1))
            continue
        pool = [r for r in range(2, m)
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if pool:
            for r in rng.sample(pool, min(len(pool), 2)):
                nonab.append((m, k, r))
        ab.append((m, k, 1))
    rng.shuffle(nonab)
    rng.shuffle(ab)
    return (nonab + ab)[:limit]


def _cost(G, D, P, Q):
    """Total number of unreached vertices from A_e and from B_e within distance D."""
    total = 0
    for start_side in (0, 1):
        visA = np.zeros(G, dtype=bool)
        visB = np.zeros(G, dtype=bool)
        front = np.array([0], dtype=np.int64)
        if start_side == 0:
            visA[0] = True
            side = 0
        else:
            visB[0] = True
            side = 1
        for _ in range(D):
            mat = P if side == 0 else Q
            new = np.zeros(G, dtype=bool)
            new[mat[:, front].ravel()] = True
            if side == 0:
                new &= ~visB
                visB |= new
            else:
                new &= ~visA
                visA |= new
            side ^= 1
            front = np.flatnonzero(new)
            if front.size == 0:
                break
        total += 2 * G - int(visA.sum()) - int(visB.sum())
    return total


def _anneal(d, G, D, table, inv, rng, deadline):
    """Anneal a connection set S of size d in G; return S with zero cost, or None."""
    S = rng.sample(range(G), d)
    P = np.stack([table[:, s] for s in S])
    Q = np.stack([table[:, inv[s]] for s in S])
    cur = _cost(G, D, P, Q)
    if cur == 0:
        return S
    t0 = max(1.0, 0.02 * cur)
    t1 = 0.3
    start = time.monotonic()
    span = max(1e-3, deadline - start)
    inS = set(S)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = min(1.0, (now - start) / span)
        T = t0 * (t1 / t0) ** frac
        j = rng.randrange(d)
        new = rng.randrange(G)
        if new in inS:
            continue
        old = S[j]
        oldP, oldQ = P[j].copy(), Q[j].copy()
        P[j] = table[:, new]
        Q[j] = table[:, inv[new]]
        c2 = _cost(G, D, P, Q)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            cur = c2
            inS.discard(old)
            inS.add(new)
            S[j] = new
        else:
            P[j] = oldP
            Q[j] = oldQ
    return S if cur == 0 else None


def _edges(G, table, S):
    """Edge list of the bi-Cayley graph: A_g = g, B_h = G + h, A_g ~ B_{g*s}."""
    E = []
    for s in S:
        col = table[:, s].tolist()
        for g in range(G):
            E.append((g, G + int(col[g])))
    return 2 * G, E


def _moore_half(d, D):
    """Moore bound on one side of a bipartite (d, D) graph (d >= 3)."""
    return sum((d - 1) ** i for i in range(D))


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.3, min(0.85 * time_limit, time_limit - 2.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = [1, []]
    n0, e0 = lib.haar_graph(d, range(d))
    if lib.is_valid(n0, e0, d, D):
        best = [n0, e0]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e
            return True
        return False

    # Projective plane incidence (diameter 3) for D >= 3.
    if D >= 3 and d >= 3:
        q = d - 1
        while q >= 2 and not lib.is_prime_power(q):
            q -= 1
        if q >= 2 and time.monotonic() < deadline:
            n1, e1 = lib.projective_plane_incidence(q)
            consider(n1, e1)

    # Bi-Cayley annealing over semidirect products.
    if d >= 3 and D >= 2:
        cap_G = _moore_half(d, D)
        best_G = best[0] // 2
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0.2:
                break
            G = best_G + 1 + rng.randrange(max(1, best_G // 25))
            if G > cap_G:
                G = best_G + 1
                if G > cap_G:
                    break
            if G < d:
                continue
            groups = _group_candidates(G, rng, 4)
            ok = False
            for m, k, r in groups:
                now = time.monotonic()
                if now >= deadline:
                    break
                slice_end = min(deadline,
                                now + max(0.5, min(10.0, 0.25 * (deadline - now))))
                table = _table(m, k, r)
                inv = _inverse(table)
                S = _anneal(d, G, D, table, inv, rng, slice_end)
                if S is not None:
                    n2, e2 = _edges(G, table, S)
                    if consider(n2, e2):
                        ok = True
                    break
            if ok:
                best_G = best[0] // 2

    return best[0], best[1]
