import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# New family: bi-Cayley graphs over small groups (one orbit per side).
#
# Vertices a_g = g and b_h = G + h, for g, h in a group of order G.
# Edges a_g -- b_{g*s} for s in S, where S is a set of d distinct group
# elements containing the identity (WLOG, by relabelling B).
#
# Left translations act transitively on each side, so the diameter is at most
# D iff every vertex is within distance D of a_e and of b_e. That makes the
# search cost two BFS runs on 2G vertices.
# ----------------------------------------------------------------------------

def _table(m, k, r):
    """Multiplication table of Z_m x|_r Z_k (element (a, b) coded as a*k + b), with inverse indices."""
    G = m * k
    g = np.arange(G, dtype=np.int64)
    A = g // k
    B = g % k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    T = ((A[:, None] + pw[B][:, None] * A[None, :]) % m) * k + (B[:, None] + B[None, :]) % k
    INV = np.argmax(T == 0, axis=1).astype(np.int64)
    return G, T, INV


def _groups_for(G, rng):
    """Candidate groups of order G as (m, k, r), with Z_m x|_r Z_k and r^k = 1 mod m."""
    out = []
    for k in range(1, 13):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        if k == 1:
            out.append((m, 1, 1))
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if rs:
            out.append((m, k, rng.choice(rs)))
    rng.shuffle(out)
    return out


def _cost(T, G, INV, S, D):
    """Number of (source, vertex) pairs at distance > D from a_e and from b_e. Zero iff diameter <= D."""
    S_arr = np.array(S, dtype=np.int64)
    Si = INV[S_arr]
    total = 0
    for side in (0, 1):
        seen = [np.zeros(G, dtype=bool), np.zeros(G, dtype=bool)]
        seen[side][0] = True
        fr = np.array([0], dtype=np.int64)
        s_ = side
        for _ in range(D):
            cols = S_arr if s_ == 0 else Si
            nb = T[fr[:, None], cols[None, :]].ravel()
            other = seen[1 - s_]
            new = np.unique(nb[~other[nb]])
            other[new] = True
            fr = new
            s_ = 1 - s_
            if fr.size == 0:
                break
        total += 2 * G - int(seen[0].sum() + seen[1].sum())
    return total


def _search(T, G, INV, d, D, rng, deadline):
    """Simulated annealing over S (identity plus d-1 other distinct elements). Returns S or None."""
    if G - 1 < d - 1:
        return None
    S = [0] + rng.sample(range(1, G), d - 1)
    c = _cost(T, G, INV, S, D)
    temp = 2.0
    while c > 0 and time.monotonic() < deadline:
        i = rng.randrange(1, d)
        x = rng.randrange(1, G)
        if x in S:
            continue
        S2 = list(S)
        S2[i] = x
        c2 = _cost(T, G, INV, S2, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
            S, c = S2, c2
        temp = max(0.15, temp * 0.9995)
    return S if c == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e
            return True
        return False

    # Projective plane incidence graph: (q+1)-regular with q = d-1, diameter 3.
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            n, e = lib.projective_plane_incidence(d - 1)
            consider(n, e)
        except Exception:
            pass

    # Main search: bi-Cayley graphs with random groups and annealed connection sets.
    try:
        while time.monotonic() < deadline:
            best_G = best_n // 2
            G = best_G + rng.randint(1, 3)
            groups = _groups_for(G, rng)
            for (m, k, r) in groups[:2]:
                now = time.monotonic()
                if now >= deadline:
                    break
                G_, T, INV = _table(m, k, r)
                S = _search(T, G_, INV, d, D, rng, min(deadline, now + 2.5))
                if S is not None:
                    e = [(g, G_ + int(T[g, s])) for g in range(G_) for s in S]
                    consider(2 * G_, e)
                    break
    except Exception:
        pass

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
