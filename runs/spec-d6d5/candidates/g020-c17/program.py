import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Known safe baselines: K_{d,d}, PG(2,q) incidence, Araujo-Pardo-Lopez.
# ----------------------------------------------------------------------------

def _baselines(d, D):
    out = [lib.haar_graph(d, range(d))]  # K_{d,d}, diameter 2
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                out.append(lib.projective_plane_incidence(q))
                break
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                out.append(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
    return out


def _moore_bipartite(d, D):
    if D <= 0 or d <= 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


# ----------------------------------------------------------------------------
# Group tables for semidirect products Z_m x| Z_z, element (a, b) coded a*z+b,
# product (a, b)(c, e) = (a + r^b c, b + e).
# ----------------------------------------------------------------------------

def _group_table(m, z, r):
    """Return (T, inv) with T[x, y] = x*y (identity code 0) and inv[x] = x^{-1}."""
    N = m * z
    pw = np.array([pow(r, b, m) for b in range(z)], dtype=np.int64)
    X = np.arange(N, dtype=np.int64)
    a = X // z
    b = X % z
    A = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    B = (b[:, None] + b[None, :]) % z
    T = A * z + B
    inv = np.argmax(T == 0, axis=1)
    return T, inv


def _sample_group(N, rng):
    """Random semidirect product of order N, as (T, inv), or None."""
    zs = [z for z in range(1, N + 1) if N % z == 0 and N // z >= 2]
    rng.shuffle(zs)
    for z in zs[:6]:
        m = N // z
        if z == 1:
            return _group_table(m, 1, 1)
        for _ in range(40):
            r = rng.randrange(1, m)
            if math.gcd(r, m) == 1 and pow(r, z, m) == 1 % m:
                return _group_table(m, z, r)
    return None


# ----------------------------------------------------------------------------
# Bi-regular voltage lifts with K base A-orbits and K base B-orbits over a group
# of order N. Layer L is a permutation P[L] pairing A_i with B_{P[L][i]} and a
# voltage S[L][i]; A_{i,g} ~ B_{P[L][i], g*S[L][i]}. Every vertex has degree d.
# Left multiplication is an automorphism, so BFS from one representative per
# orbit decides the diameter exactly.
# ----------------------------------------------------------------------------

def _nb(K, N, d, T, inv, P, S):
    """Neighbour table of the lift, shape (2KN, d)."""
    KN = K * N
    NB = np.empty((2 * KN, d), dtype=np.int64)
    for L in range(d):
        pl = P[L]
        sl = S[L]
        pinv = np.argsort(pl)
        for i in range(K):
            NB[i * N:(i + 1) * N, L] = KN + int(pl[i]) * N + T[:, sl[i]]
        for j in range(K):
            i = int(pinv[j])
            NB[KN + j * N: KN + (j + 1) * N, L] = i * N + T[:, inv[sl[i]]]
    return NB


def _reps(K, N):
    return np.array([i * N for i in range(K)] + [K * N + j * N for j in range(K)],
                    dtype=np.int64)


def _cost(D, NB, reps):
    """Number of (representative, vertex) pairs at distance > D, plus duplicate penalty."""
    V = NB.shape[0]
    R = reps.shape[0]
    srt = np.sort(NB, axis=1)
    dup = int(np.count_nonzero(srt[:, 1:] == srt[:, :-1]))
    reach = np.zeros((R, V), dtype=bool)
    reach[np.arange(R), reps] = True
    for _ in range(D):
        reach = reach | reach[:, NB].any(axis=2)
    return R * V - int(np.count_nonzero(reach)) + 20 * dup


def _anneal(d, D, K, N, T, inv, rng, end, iters=20000):
    """Annealing over layer permutations and voltages. Returns NB with zero cost, or None."""
    P = np.zeros((d, K), dtype=np.int64)
    S = np.zeros((d, K), dtype=np.int64)
    for L in range(d):
        P[L] = rng.sample(range(K), K)
        S[L] = [rng.randrange(N) for _ in range(K)]
    reps = _reps(K, N)
    NB = _nb(K, N, d, T, inv, P, S)
    cur = _cost(D, NB, reps)
    for it in range(iters):
        if cur == 0 or time.monotonic() > end:
            break
        temp = max(0.3, 3.0 * 0.9995 ** it)
        L = rng.randrange(d)
        kind = 0
        a = b = i = old = 0
        if K > 1 and rng.random() < 0.3:
            a, b = rng.sample(range(K), 2)
            P[L, a], P[L, b] = P[L, b], P[L, a]
            kind = 1
        else:
            i = rng.randrange(K)
            old = int(S[L, i])
            S[L, i] = rng.randrange(N)
        nNB = _nb(K, N, d, T, inv, P, S)
        new = _cost(D, nNB, reps)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur, NB = new, nNB
        else:
            if kind:
                P[L, a], P[L, b] = P[L, b], P[L, a]
            else:
                S[L, i] = old
    return NB if cur == 0 else None


def _edges_from(NB, K, N):
    """Edge list of the lift: each A-vertex to its d neighbours."""
    KN = K * N
    E = []
    for v in range(KN):
        for w in NB[v]:
            E.append((v, int(w)))
    return 2 * KN, E


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best_n, best_e = None, None
    for n, e in _baselines(d, D):
        if (best_n is None or n > best_n) and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e
    if best_n is None:
        best_n, best_e = 2, [(0, 1)]

    if d < 2 or best_n >= _moore_bipartite(d, D):
        return best_n, best_e

    rng = random.Random(seed)
    while time.monotonic() < deadline:
        try:
            K = rng.choice([1, 1, 1, 2, 2, 3])
            lo = best_n // (2 * K) + 1
            N = rng.randint(lo, lo + max(2, lo // 15))
            N = max(N, 2)
            grp = _sample_group(N, rng)
            if grp is None:
                continue
            T, inv = grp
            end = min(deadline, time.monotonic() + rng.uniform(1.5, 5.0))
            NB = _anneal(d, D, K, N, T, inv, rng, end)
            if NB is None:
                continue
            n, e = _edges_from(NB, K, N)
            if n > best_n and lib.is_valid(n, e, d, D):
                best_n, best_e = n, e
        except Exception:
            continue

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
