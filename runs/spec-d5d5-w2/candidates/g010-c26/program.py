import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Baseline for D = 3: projective plane incidence graph when d-1 is a prime power.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x|_r Z_k, searched by simulated
# annealing. Vertices A_x (x in G) and B_y (y in G); A_x ~ B_{x*s} for s in S,
# |S| = d. Left translation is an automorphism, so the diameter is checked from
# A_0 and B_0 only. Each evaluation is a vectorized level-synchronous BFS.
# ----------------------------------------------------------------------------

MAX_GROUPS = 6        # groups tried per round for a fixed order N
ANNEAL_ITERS = 3000   # annealing steps per (group, N) attempt


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N and r^k = 1 mod m, gcd(r, m) = 1."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(m, k, r):
    """Return (M, invs): M[x, s] = x*s and invs[s] = s^-1, as numpy int arrays."""
    G = m * k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    A = a[:, None]
    Bb = b[:, None]
    C = a[None, :]
    Dd = b[None, :]
    M = ((A + pw[Bb] * C) % m) * k + (Bb + Dd) % k
    nb = (-b) % k
    invs = ((-pw[nb] * a) % m) * k + nb
    return M, invs


def _unreached(M, invs, Sarr, G, D):
    """Number of (source, vertex) pairs not within distance D, sources A_0 and B_0."""
    fwd = M[:, invs[Sarr]]   # fwd[y, i] = y * s_i^-1  (B_y is reached from A_{y s_i^-1})
    bwd = M[:, Sarr]         # bwd[x, i] = x * s_i     (A_x reaches B_{x s_i})
    total = 0
    for side in (0, 1):
        RA = np.zeros(G, dtype=bool)
        RB = np.zeros(G, dtype=bool)
        FA = np.zeros(G, dtype=bool)
        FB = np.zeros(G, dtype=bool)
        if side == 0:
            RA[0] = True
            FA[0] = True
        else:
            RB[0] = True
            FB[0] = True
        for _ in range(D):
            nA = FB[bwd].any(axis=1) & ~RA
            nB = FA[fwd].any(axis=1) & ~RB
            RA |= nA
            RB |= nB
            FA, FB = nA, nB
            if not (nA.any() or nB.any()):
                break
        total += 2 * G - int(RA.sum()) - int(RB.sum())
    return total


def _anneal(M, invs, G, d, D, rng, iters, deadline):
    """Simulated annealing over connection sets S of size d; returns S with zero cost or None."""
    S = rng.sample(range(G), d)
    cur = _unreached(M, invs, np.array(S, dtype=np.int64), G, D)
    T0, T1 = 3.0, 0.15
    for it in range(iters):
        if cur == 0:
            break
        if (it & 63) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / max(1, iters))
        i = rng.randrange(d)
        c = rng.randrange(G)
        if c in S:
            continue
        S2 = list(S)
        S2[i] = c
        v = _unreached(M, invs, np.array(S2, dtype=np.int64), G, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / T):
            S, cur = S2, v
    return S if cur == 0 else None


def _search(d, D, moore, best_n, rng, deadline, consider):
    """Climb the order N of bi-Cayley lifts; each success raises N by one."""
    N = max(d, best_n // 2 + 1)
    while time.monotonic() < deadline and 2 * N <= moore:
        groups = _groups(N)
        rng.shuffle(groups)
        found = None
        for m, k, r in groups[:MAX_GROUPS]:
            if time.monotonic() > deadline:
                break
            M, invs = _tables(m, k, r)
            S = _anneal(M, invs, N, d, D, rng, ANNEAL_ITERS, deadline)
            if S is not None:
                found = (M, S)
                break
        if found is None:
            continue  # retry this order with fresh groups and starting sets
        M, S = found
        Ml = M.tolist()
        edges = [(x, N + Ml[x][s]) for x in range(N) for s in S]
        consider(2 * N, edges)
        N += 1


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if best[0] < moore:
        try:
            _search(d, D, moore, best[0], rng, deadline, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
