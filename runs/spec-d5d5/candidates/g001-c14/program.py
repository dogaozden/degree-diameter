import math
import random
import time

import numpy as np
import lib

# Idea: bi-Cayley graphs over semidirect products Z_m x| Z_k.
# Vertices A_x and B_y (x, y in G, |G| = o), with edge A_x -- B_{x*s} for s in S, |S| = d.
# Left multiplication is an automorphism, so the graph is transitive on each side. Its
# diameter is at most D iff the eccentricities of A_e and B_e are at most D, which needs
# only two vectorized BFS runs per candidate. Right-translating S lets us assume the
# identity is in S. Orders are searched descending with iterative deepening. Every
# result is checked with lib.is_valid before it is returned.

_GROUPS = {}


def _groups(o):
    """Semidirect products Z_m x| Z_k with m*k = o, r^k = 1 mod m, gcd(r, m) = 1 (cached)."""
    if o in _GROUPS:
        return _GROUPS[o]
    out = []
    for k in range(1, o + 1):
        if o % k:
            continue
        m = o // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    _GROUPS[o] = out
    return out


def _table(m, k, r):
    """Multiplication table T[i, j] = i*j for the group Z_m x| Z_k; element (a, b) is coded a*k+b."""
    o = m * k
    idx = np.arange(o, dtype=np.int64)
    A = idx // k
    B = idx % k
    P = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    return ((A[:, None] + P[B][:, None] * A[None, :]) % m) * k + (B[:, None] + B[None, :]) % k


def _ok(ADJ, src, D):
    """True if BFS from src reaches every node of the graph within D steps."""
    N = ADJ.shape[0]
    vis = np.zeros(N, dtype=bool)
    vis[src] = True
    front = np.array([src], dtype=np.int64)
    for _ in range(D):
        nb = ADJ[front].ravel()
        nb = nb[~vis[nb]]
        if nb.size == 0:
            break
        nb = np.unique(nb)
        vis[nb] = True
        front = nb
    return bool(vis.all())


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.75 * time_limit - 1.0)

    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Exact projective-plane record for D = 3 when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    # Baseline K_{d,d}: diameter 2, valid for D >= 2.
    best_n = 2 * d
    best_e = [(x, d + y) for x in range(d) for y in range(d)]
    best_o = d

    rng = random.Random(seed)
    Ub = lib._moore_bound(d, D) // 2   # each side has at most Moore/2 vertices
    budget = 8

    while time.monotonic() < deadline:
        for o in range(Ub, best_o, -1):
            if time.monotonic() >= deadline:
                break
            grps = _groups(o)
            if not grps:
                continue
            found = None
            for _ in range(budget):
                if time.monotonic() >= deadline:
                    break
                m, k, r = rng.choice(grps)
                T = _table(m, k, r)
                inv = np.argmax(T == 0, axis=1)
                for _ in range(4):
                    S = np.array([0] + rng.sample(range(1, o), d - 1), dtype=np.int64)
                    ADJ = np.empty((2 * o, d), dtype=np.int64)
                    ADJ[:o] = o + T[:, S]
                    ADJ[o:] = T[:, inv[S]]
                    if _ok(ADJ, 0, D) and _ok(ADJ, o, D):
                        found = (S, T)
                        break
                if found:
                    break
            if found:
                S, T = found
                n = 2 * o
                edges = [(x, o + int(T[x, s])) for x in range(o) for s in S.tolist()]
                if lib.is_valid(n, edges, d, D):
                    best_n, best_e, best_o = n, edges, o
                    break
        budget *= 2

    if lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    return 2 * d, [(x, d + y) for x in range(d) for y in range(d)]
