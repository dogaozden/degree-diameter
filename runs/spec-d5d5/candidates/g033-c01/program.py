import math
import random
import time

import numpy as np

import lib

# NEW CONSTRUCTION: multi-orbit voltage lifts over semidirect groups.
# The parent searches bi-Cayley graphs (2 base vertices). Here the base graph has
# k vertices on each side, and the graph is the lift of d perfect matchings
# sig_i between the sides with group voltages g_{i,a}:
#     A_{a,x} -- B_{sig_i(a), x * g_{i,a}}   for i in 0..d-1, x in G.
# Every vertex has degree exactly d (before dedup), so the order is 2*k*|G|.
# Left multiplication by G is an automorphism, so only the 2k sources (base
# vertex, identity) need BFS. All sources are run together in one batched
# numpy BFS over boolean arrays. A simulated-annealing search then looks for
# zero unreached pairs.

MAX_GROUPS_TRY = 12   # groups tried per attempt call
ITERS = 1500          # annealing steps per (group, base size) try
KMAX = 8              # largest number of base vertices per side


# ----------------------------------------------------------------------------
# Baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Group helpers.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, kk, r) with m*kk = N, giving Z_m x|_r Z_kk."""
    out = []
    for kk in range(1, N + 1):
        if N % kk:
            continue
        m = N // kk
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, kk, m) == 1 % m:
                out.append((m, kk, r))
    return out


def _tables(m, kk, r):
    """Multiplication and inverse tables for the group Z_m x|_r Z_kk (identity is 0)."""
    N, mul, inv = lib.semidirect_group(m, kk, r)
    M = np.array([[mul(x, g) for g in range(N)] for x in range(N)], dtype=np.int64)
    I = np.array([inv(g) for g in range(N)], dtype=np.int64)
    return N, M, I


# ----------------------------------------------------------------------------
# Multi-orbit lift evaluator.
# ----------------------------------------------------------------------------

class _Lift:
    def __init__(self, k, d, D, N, M, I):
        self.k, self.d, self.D, self.N = k, d, D, N
        self.M, self.I = M, I
        self.HA = k * N
        self.xs = np.tile(np.arange(N, dtype=np.int64), k)
        self.as_ = np.repeat(np.arange(k, dtype=np.int64), N)
        self.src = np.array([a * N for a in range(k)]
                            + [self.HA + b * N for b in range(k)], dtype=np.int64)

    def targets(self, sig, volt):
        """Per slot i: local B target of each A vertex, and local A target of each B vertex."""
        sigInv = np.argsort(sig, axis=1)
        tA, tB = [], []
        for i in range(self.d):
            g = volt[i]
            tA.append(sig[i][self.as_] * self.N + self.M[self.xs, g[self.as_]])
            aa = sigInv[i][self.as_]
            tB.append(aa * self.N + self.M[self.xs, self.I[g[aa]]])
        return tA, tB

    def cost(self, sig, volt):
        """Total number of (source, vertex) pairs at distance > D over the 2k base sources."""
        HA = self.HA
        S = 2 * self.k
        V = 2 * HA
        tA, tB = self.targets(sig, volt)
        vis = np.zeros((S, V), dtype=bool)
        vis[np.arange(S), self.src] = True
        front = vis.copy()
        for _ in range(self.D):
            fA = front[:, :HA]
            fB = front[:, HA:]
            nA = np.zeros((S, HA), dtype=bool)
            nB = np.zeros((S, HA), dtype=bool)
            for i in range(self.d):
                # Each target map is a bijection, so fancy |= is exact.
                nB[:, tA[i]] |= fA
                nA[:, tB[i]] |= fB
            new = np.concatenate((nA, nB), axis=1)
            new &= ~vis
            if not new.any():
                break
            vis |= new
            front = new
        return S * V - int(vis.sum())

    def edges(self, sig, volt):
        tA, _ = self.targets(sig, volt)
        HA = self.HA
        E = set()
        for i in range(self.d):
            for v, t in enumerate(tA[i].tolist()):
                E.add((v, HA + t))
        return 2 * HA, sorted(E)


def _anneal(lift, d, k, N, rng, iters, deadline):
    """Anneal over matchings sig (sig[0] fixed to identity) and voltages to zero the cost."""
    sig = np.zeros((d, k), dtype=np.int64)
    sig[0] = np.arange(k)
    for i in range(1, d):
        sig[i] = rng.sample(range(k), k)
    volt = np.array([[rng.randrange(N) for _ in range(k)] for _ in range(d)], dtype=np.int64)
    cur = lift.cost(sig, volt)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 0.3 + 2.0 * (1.0 - it / iters)
        if k > 1 and d > 1 and rng.random() < 0.25:
            i = rng.randrange(1, d)
            a, b = rng.sample(range(k), 2)
            sig2 = sig.copy()
            sig2[i, a], sig2[i, b] = sig[i, b], sig[i, a]
            volt2 = volt
        else:
            i = rng.randrange(d)
            a = rng.randrange(k)
            volt2 = volt.copy()
            volt2[i, a] = rng.randrange(N)
            sig2 = sig
        v = lift.cost(sig2, volt2)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            sig, volt, cur = sig2, volt2, v
    return (sig, volt) if cur == 0 else None


def _attempt(k, N, d, D, rng, deadline):
    """Try groups of order N for base size k until one yields a valid lift."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, kk, r in groups[:MAX_GROUPS_TRY]:
        if time.monotonic() > deadline:
            return None
        Nn, M, I = _tables(m, kk, r)
        lift = _Lift(k, d, D, Nn, M, I)
        res = _anneal(lift, d, k, Nn, rng, ITERS, deadline)
        if res is not None:
            return lift, res
    return None


def _cands(target, cap):
    """Lift sizes 2*k*N >= target (and <= cap), smallest first."""
    out = []
    for k in range(1, KMAX + 1):
        step = 2 * k
        N0 = max(2, -(-target // step))
        for N in range(N0, N0 + 3):
            nt = step * N
            if nt <= cap:
                out.append((nt, k, N))
    out.sort()
    return out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.85 * time_limit, time_limit - 4.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = [1, []]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    # Calibration / record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best[0], best[1]

    if d == 1:
        consider(2, [(0, 1)])
        return best[0], best[1]

    try:
        consider(*lib.haar_graph(d, range(d)))
    except Exception:
        pass
    if D == 3:
        try:
            if lib.is_prime_power(d - 2) and d - 2 >= 3:
                consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
        except Exception:
            pass

    cap = lib._moore_bound(d, D)
    budget = 1.5
    attempts = 0
    while time.monotonic() < deadline:
        cands = _cands(best[0] + 1, cap)
        if not cands:
            break
        pool = cands[:6]
        idx = min(len(pool) - 1, int(rng.random() ** 2 * len(pool)))
        nt, k, N = pool[idx]
        att_deadline = min(deadline, time.monotonic() + budget)
        res = _attempt(k, N, d, D, rng, att_deadline)
        attempts += 1
        if res is None:
            budget = min(1.5 * (1.08 ** attempts), 10.0)
            continue
        lift, (sig, volt) = res
        n, e = lift.edges(sig, volt)
        consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best[0], best[1]
