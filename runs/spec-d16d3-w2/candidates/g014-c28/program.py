import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bold construction for D >= 3: bi-Cayley graphs over non-abelian groups.
#
# Let G be a finite group of order N and S a subset of G with |S| = d and
# identity in S. The bipartite graph with parts A = G, B = G and edges
#     x (in A) ~ x*s (in B),  s in S,
# is d-regular and has 2N vertices. It has diameter <= 3 exactly when
#     S S^{-1} = G   (A-A distances <= 2)
#     S^{-1} S = G   (B-B distances <= 2)
# because mixed A-B distances <= 3 then follow from S S^{-1} S = G.
# Left translations are automorphisms, so checking distances from the
# identity of each side suffices.
#
# Groups are semidirect products Z_m x| Z_f (lib.semidirect_group coding),
# so non-cyclic groups are included. The cyclic Haar construction is the
# special case m = N, f = 1. The search is simulated annealing over S with
# the identity fixed (S can be translated by a group element without
# changing the covering properties).
# ----------------------------------------------------------------------------


def _table(m, f, r):
    """Return (N, MUL, INV) numpy tables for Z_m x|_r Z_f, element a*f+b."""
    N = m * f
    pw = np.array([pow(r, b, m) for b in range(f)], dtype=np.int64)
    el = np.arange(N, dtype=np.int64)
    a = el // f
    b = el % f
    MUL = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * f + (b[:, None] + b[None, :]) % f
    nb = (-b) % f
    INV = ((-pw[nb] * a) % m) * f + nb
    return N, MUL, INV


def _groups(N, rng):
    """Candidate semidirect factorizations (m, f, r) of order N, shuffled and capped."""
    out = []
    for f in range(1, N + 1):
        if N % f:
            continue
        m = N // f
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, f, m) == 1 % m:
                out.append((m, f, r))
    rng.shuffle(out)
    return out[:10]


def _bump(cnt, g, sgn):
    """Add (sgn > 0) or remove one count at g; return the change in the number of zero entries."""
    if sgn > 0:
        cnt[g] += 1
        return -1 if cnt[g] == 1 else 0
    cnt[g] -= 1
    return 1 if cnt[g] == 0 else 0


def _mv(x, O, sgn, P, Q, cp, cq):
    """Add/remove the ordered pairs involving element x against the set O (plus (x, x))."""
    z = 0
    px, qx = P[x], Q[x]
    for s in O:
        z += _bump(cp, px[s], sgn) + _bump(cp, P[s][x], sgn)
        z += _bump(cq, qx[s], sgn) + _bump(cq, Q[s][x], sgn)
    z += _bump(cp, px[x], sgn) + _bump(cq, qx[x], sgn)
    return z


def _anneal(N, k, P, Q, rng, deadline):
    """Find S (identity at index 0, |S| = k) with P-set and Q-set both covering G, or None."""
    cp = [0] * N
    cq = [0] * N
    S = [0] + rng.sample(range(1, N), k - 1)
    inS = set(S)
    for s in S:
        for t in S:
            cp[P[s][t]] += 1
            cq[Q[s][t]] += 1
    zeros = sum(1 for c in cp if c == 0) + sum(1 for c in cq if c == 0)
    T = 0.35
    it = 0
    while zeros > 0:
        it += 1
        if not (it & 255) and time.monotonic() > deadline:
            return None
        i = rng.randrange(1, k)
        x = S[i]
        y = rng.randrange(1, N)
        if y in inS:
            continue
        O = [S[j] for j in range(k) if j != i]
        dz = _mv(x, O, -1, P, Q, cp, cq) + _mv(y, O, 1, P, Q, cp, cq)
        if dz <= 0 or rng.random() < math.exp(-dz / T):
            zeros += dz
            S[i] = y
            inS.discard(x)
            inS.add(y)
        else:
            _mv(y, O, -1, P, Q, cp, cq)
            _mv(x, O, 1, P, Q, cp, cq)
    return sorted(S)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + min(0.7 * float(time_limit), 40.0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, list(E)
            return True
        return False

    if D == 2:
        return best_n, list(best_E)

    # Projective plane incidence when d - 1 is a prime power (diameter 3, degree d).
    if lib.is_prime_power(d - 1):
        n, E = lib.projective_plane_incidence(d - 1)
        consider(n, E)

    # Bold search: bi-Cayley graphs over semidirect products, ascending in order N.
    if d >= 2:
        rng = random.Random(seed * 1000003 + 131 * d + 7 * D + 1)
        hi = d * (d - 1) + 1
        lo = max(d, (6 * hi) // 10)
        for N in range(lo, hi + 1):
            if time.monotonic() > deadline:
                break
            for (m, f, r) in _groups(N, rng):
                now = time.monotonic()
                if now > deadline:
                    break
                cap = min(deadline, now + 1.0)
                _, MUL, INV = _table(m, f, r)
                P = MUL[:, INV].tolist()
                Q = MUL[INV, :].tolist()
                S = _anneal(N, d, P, Q, rng, cap)
                if S is None:
                    continue
                E = [(x, N + int(MUL[x, s])) for x in range(N) for s in S]
                consider(2 * N, E)
                break

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
