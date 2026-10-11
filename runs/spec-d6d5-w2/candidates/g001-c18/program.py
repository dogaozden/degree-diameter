import math
import random
import time

import numpy as np

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Semidirect products Z_m x| Z_k2 with vectorised right translations.
# Element (a, b) is coded a*k2 + b, identity is 0, and
# (a, b)*(c, d) = (a + r^b c, b + d). The right translation by s is a
# permutation array, so the whole group never needs a multiplication table.
# ----------------------------------------------------------------------------

class _Group:
    def __init__(self, m, k2, r):
        self.m, self.k2, self.r = m, k2, r
        self.G = m * k2
        g = np.arange(self.G, dtype=np.int64)
        self.A = g // k2
        self.B = g % k2
        pw = np.array([pow(r, b, m) for b in range(k2)], dtype=np.int64)
        self.PW = pw[self.B]

    def perm(self, s):
        """Array P with P[g] = g * s."""
        c, d = divmod(s, self.k2)
        return ((self.A + self.PW * c) % self.m) * self.k2 + (self.B + d) % self.k2


def _sample_group(G, rng):
    """Random semidirect product of order G, or None."""
    cands = [k2 for k2 in range(1, 13) if G % k2 == 0 and G // k2 >= 2]
    if not cands:
        return None
    rng.shuffle(cands)
    for k2 in cands[:4]:
        m = G // k2
        if k2 == 1:
            return _Group(m, 1, 1)
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if rs:
            return _Group(m, k2, rng.choice(rs))
    return None


# ----------------------------------------------------------------------------
# Vectorised bi-Cayley (voltage-lift) diameter evaluator.
#
# Vertices: A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h. A dart (i, j, s)
# joins A_{i,g} to B_{j, g*s} for every g. Left multiplication by a group
# element is an automorphism, so only one representative per base vertex
# needs a BFS. All reps and all base vertices are handled as numpy boolean
# arrays, so one BFS layer is a single integer matrix product.
# Returns the number of (rep, vertex) pairs left beyond distance D.
# ----------------------------------------------------------------------------

def _cost(k, grp, darts, D, limit):
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    T = len(darts)
    G = grp.G
    N = 2 * k * G
    I = np.array([t[0] for t in darts], dtype=np.int64)
    J = np.array([t[1] for t in darts], dtype=np.int64)
    P = np.stack([grp.perm(t[2]) for t in darts])          # (T, G): g -> g*s
    Pi = np.empty_like(P)
    Pi[np.arange(T)[:, None], P] = np.arange(G, dtype=np.int64)[None, :]
    ks = np.arange(k, dtype=np.int64)[:, None]
    Mi = (I[None, :] == ks).astype(np.int64)                # (k, T)
    Mj = (J[None, :] == ks).astype(np.int64)
    I_col = I[:, None]
    J_col = J[:, None]

    total = 0
    reps = [(0, i) for i in range(k)] + [(1, j) for j in range(k)]
    for side, idx in reps:
        FA = np.zeros((k, G), dtype=bool)
        FB = np.zeros((k, G), dtype=bool)
        if side == 0:
            FA[idx, 0] = True
        else:
            FB[idx, 0] = True
        VA = FA.copy()
        VB = FB.copy()
        seen = 1
        for _ in range(D):
            # B_{j,h} reached from A_{i,g} with h = g*s: h-entry reads FA[i, Pi[h]].
            NB = (Mj @ FA[I_col, Pi].astype(np.int64)) > 0
            # A_{i,g} reached from B_{j,g*s}: g-entry reads FB[j, P[g]].
            NA = (Mi @ FB[J_col, P].astype(np.int64)) > 0
            NB &= ~VB
            NA &= ~VA
            VA |= NA
            VB |= NB
            FA, FB = NA, NB
            seen += int(NA.sum()) + int(NB.sum())
            if not (NA.any() or NB.any()):
                break
        total += N - seen
        if total > limit:
            return total
    return total


def _lift(k, grp, darts):
    G = grp.G
    E = set()
    for i, j, s in darts:
        P = grp.perm(s).tolist()
        for g in range(G):
            E.add((i * G + g, (k + j) * G + P[g]))
    return 2 * k * G, sorted(E)


# ----------------------------------------------------------------------------
# Layered annealing. Each layer is one permutation of the k base vertices
# on each side, so every lifted vertex has degree exactly d (before dedup).
# Moves: re-roll one voltage, or swap the B-targets of two base vertices
# inside one layer. Metropolis acceptance is drawn up front.
# ----------------------------------------------------------------------------

def _anneal(d, D, k, grp, rng, deadline, iters):
    G = grp.G
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    cost = _cost(k, grp, darts, D, float("inf"))
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)
        limit = cost - T * math.log(1.0 - rng.random())
        if k == 1 or rng.random() < 0.6:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _cost(k, grp, darts, D, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, grp, darts, D, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    return cost == 0, darts, cost


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    n0, e0 = lib.haar_graph(d, range(d))
    best = {"n": n0, "e": e0}

    def consider(n, e):
        if n > best["n"] and lib.is_valid(n, e, d, D):
            best["n"], best["e"] = n, e

    if D >= 3:
        # Projective plane incidence graph with q = largest prime power <= d - 1.
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n, e = lib.projective_plane_incidence(q)
                consider(n, e)
                break

    if D >= 3 and best["n"] < lib.moore_bound(d, D):
        try:
            ks = [1, 1, 1, 2, 2, 3]
            while time.monotonic() < deadline and best["n"] < lib.moore_bound(d, D):
                k = rng.choice(ks)
                lo = best["n"] // (2 * k) + 1
                # Bias toward the smallest unseen order, with some room above it.
                G = lo + int(rng.random() ** 2 * max(4, lo // 6))
                grp = _sample_group(G, rng)
                if grp is None:
                    continue
                iters = 1200 if k == 1 else 400
                ok, darts, _ = _anneal(d, D, k, grp, rng, deadline, iters)
                if ok:
                    n, e = _lift(k, grp, darts)
                    consider(n, e)
        except Exception:
            pass

    best_n, best_e = best["n"], best["e"]
    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = n0, e0
    return best_n, [(int(u), int(v)) for u, v in best_e]
