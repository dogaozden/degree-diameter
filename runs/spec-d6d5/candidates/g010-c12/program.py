import math
import random
import time

import numpy as np

import lib


def _moore_bipartite(d, D):
    return 2 * sum((d - 1) ** i for i in range(D))


def _groups_of_order(G):
    """All (m, k, r) giving semidirect products Z_m x| Z_k of order G."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _mul_table(m, k, r):
    """Full multiplication table of Z_m x| Z_k; element (a, b) is coded a*k + b, identity is 0."""
    G = m * k
    idx = np.arange(G, dtype=np.int64)
    A = idx // k
    B = idx % k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    first = (A[:, None] + pw[B][:, None] * A[None, :]) % m
    second = (B[:, None] + B[None, :]) % k
    return first * k + second


def _reach(G, fwd, bwd, side, D):
    """Number of vertices within distance D of A_0 (side 0) or B_0 (side 1) in a bi-Cayley graph.

    fwd[i][g] is the B-index adjacent to A_g through dart i.
    bwd[i][h] is the A-index adjacent to B_h through dart i.
    """
    RA = np.zeros(G, dtype=bool)
    RB = np.zeros(G, dtype=bool)
    if side == 0:
        RA[0] = True
    else:
        RB[0] = True
    for _ in range(D):
        nA = RA.copy()
        nB = RB.copy()
        ia = np.flatnonzero(RA)
        ib = np.flatnonzero(RB)
        if ia.size:
            nB[fwd[:, ia].ravel()] = True
        if ib.size:
            nA[bwd[:, ib].ravel()] = True
        RA, RB = nA, nB
    return int(np.count_nonzero(RA)) + int(np.count_nonzero(RB))


def _cost(G, D, MUL_T, INV, S):
    """Unreached (vertex, representative) pairs; zero iff the bi-Cayley graph has diameter <= D.

    Left multiplication is an automorphism, so A_0 and B_0 represent both orbits.
    """
    Sa = np.asarray(S, dtype=np.int64)
    fwd = MUL_T[Sa]
    bwd = MUL_T[INV[Sa]]
    return 4 * G - _reach(G, fwd, bwd, 0, D) - _reach(G, fwd, bwd, 1, D)


def _anneal(G, d, D, MUL_T, INV, rng, deadline, iters):
    """Search a d-element connection set S in the group with cost zero. Returns S or None."""
    S = rng.sample(range(G), d)
    cur = _cost(G, D, MUL_T, INV, S)
    T = 2.0
    for it in range(iters):
        if cur == 0:
            return S
        if (it & 127) == 0 and time.monotonic() >= deadline:
            break
        i = rng.randrange(d)
        t = rng.randrange(G)
        if t in S:
            continue
        old = S[i]
        S[i] = t
        c2 = _cost(G, D, MUL_T, INV, S)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            cur = c2
        else:
            S[i] = old
        T = max(0.1, T * 0.9995)
    return S if cur == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if not lib.is_valid(best_n, best_e, d, D):
        return 1, []

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if d < 2:
        return best_n, best_e

    # Projective plane incidence graph when d - 1 is a prime power (diameter 3).
    if D >= 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)

    # Bi-Cayley search over semidirect products, targeting an order that ratchets upward.
    g0 = max(d, int(0.42 * _moore_bipartite(d, D) / 2))
    while time.monotonic() < deadline:
        lo = max(g0, best_n // 2 + 1)
        G = lo + rng.randrange(5)
        if G < d:
            G = d
        cands = _groups_of_order(G)
        if not cands:
            continue
        rng.shuffle(cands)
        for m, k, r in cands[:12]:
            if time.monotonic() >= deadline:
                break
            MUL = _mul_table(m, k, r)
            MUL_T = np.ascontiguousarray(MUL.T)
            INV = np.argmax(MUL == 0, axis=1)
            S = _anneal(G, d, D, MUL_T, INV, rng, deadline, 2500)
            if S is not None:
                e = [(g, G + int(MUL[g, s])) for s in S for g in range(G)]
                consider(2 * G, e)
                g0 = max(g0, G + 1)
                break

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
