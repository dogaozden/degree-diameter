import itertools
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Baseline families: projective plane incidence (D >= 3) and Araujo-Pardo-Lopez.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New family: bi-Cayley (Haar-type) graphs over arbitrary finite ABELIAN groups.
#
# Vertices A_x and B_y for x, y in G. Connection set S of d distinct group
# elements; A_x is joined to B_{x+s} for each s in S. Each side has degree d.
#
# The graph is vertex-transitive under translation and has an automorphism
# swapping sides (A_x <-> B_{-x}), so its diameter is at most D exactly when a
# BFS from A_0 reaches every vertex within D steps. This is checked with numpy
# on group indices. The previous search used only cyclic groups (and
# semidirect products of two cyclic factors); here every abelian group of a
# given order is tried, including elementary abelian ones like Z_7^3, which
# have no cyclic counterpart. The search is hill-climbing over S.
# ----------------------------------------------------------------------------

def _partitions(n, maxpart=None):
    """Integer partitions of n as non-increasing lists."""
    if maxpart is None:
        maxpart = n
    if n == 0:
        yield []
        return
    for k in range(min(n, maxpart), 0, -1):
        for rest in _partitions(n - k, k):
            yield [k] + rest


def _abelian_moduli(G):
    """All moduli lists [m1, ..., mt] (prime powers) with prod = G, one per abelian group of order G."""
    fac = {}
    x, p = G, 2
    while p * p <= x:
        while x % p == 0:
            fac[p] = fac.get(p, 0) + 1
            x //= p
        p += 1
    if x > 1:
        fac[x] = fac.get(x, 0) + 1
    per = []
    for p, e in fac.items():
        per.append([[p ** k for k in part] for part in _partitions(e)])
    out = []
    for combo in itertools.product(*per):
        out.append(sorted([m for part in combo for m in part], reverse=True))
    return out


def _tables(mods):
    """Return (G, addt, neg) for the abelian group Z_m1 x ... x Z_mt, elements coded in mixed radix."""
    ns = np.array(mods, dtype=np.int64)
    G = int(np.prod(ns))
    t = len(mods)
    w = np.ones(t, dtype=np.int64)
    for i in range(1, t):
        w[i] = w[i - 1] * ns[i - 1]
    idx = np.arange(G, dtype=np.int64)
    dig = (idx[:, None] // w[None, :]) % ns[None, :]          # G x t digits
    dsum = (dig[:, None, :] + dig[None, :, :]) % ns           # G x G x t
    addt = (dsum * w).sum(axis=2)                              # addt[a, b] = a + b
    neg = (((-dig) % ns) * w).sum(axis=1)                      # neg[a] = -a
    return G, addt, neg


def _cost(S, G, D, addt, neg):
    """Number of vertices NOT within distance D of A_0 (zero iff the Haar graph has diameter <= D)."""
    Sa = np.array(S, dtype=np.int64)
    Na = neg[Sa]
    visA = np.zeros(G, dtype=bool)
    visB = np.zeros(G, dtype=bool)
    visA[0] = True
    f = np.array([0], dtype=np.int64)
    side = 0
    for _ in range(D):
        ops = Sa if side == 0 else Na
        tgt = visB if side == 0 else visA
        img = addt[np.ix_(f, ops)].ravel()
        m = np.zeros(G, dtype=bool)
        m[img] = True
        m &= ~tgt
        tgt |= m
        f = np.flatnonzero(m)
        side ^= 1
        if f.size == 0:
            break
    return 2 * G - int(visA.sum()) - int(visB.sum())


def _search(G, d, D, addt, neg, rng, deadline):
    """Hill-climb a d-element connection set S containing 0 with cost zero, or return None."""
    if G < d + 1:
        return None
    while time.monotonic() < deadline:
        S = [0] + rng.sample(range(1, G), d - 1)
        c = _cost(S, G, D, addt, neg)
        stag = 0
        while c > 0 and stag < 3000 and time.monotonic() < deadline:
            i = rng.randrange(1, d)
            x = rng.randrange(1, G)
            if x in S:
                stag += 1
                continue
            T = S[:]
            T[i] = x
            ct = _cost(T, G, D, addt, neg)
            if ct < c:
                c, S, stag = ct, T, 0
            elif ct == c:
                S = T
                stag += 1
            else:
                stag += 1
        if c == 0:
            return S
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    target = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Calibration shortcut: a graph already at the Moore bound cannot be beaten.
    if best_n >= target:
        return best

    # Sweep upward over orders G of abelian groups; each success gives a
    # bi-Cayley graph on 2G vertices. Every abelian group of order G gets a
    # share of the per-order budget.
    if d >= 2:
        lo = max(best_n // 2 + 1, 2)
        if (d, D) == (6, 5):
            lo = max(lo, 343)  # 2*343 = 686 beats the record 684
        hi = target // 2
        for G in range(lo, hi + 1):
            if time.monotonic() >= deadline:
                break
            if G < d + 1:
                continue
            groups = _abelian_moduli(G)
            rng.shuffle(groups)
            order_deadline = min(deadline, time.monotonic() + 10.0)
            found = None
            for mods in groups:
                now = time.monotonic()
                if now >= order_deadline:
                    break
                gd = min(order_deadline, now + 10.0 / len(groups))
                Gm, addt, neg = _tables(mods)
                S = _search(Gm, d, D, addt, neg, rng, gd)
                if S is not None:
                    found = (Gm, addt, S)
                    break
            if found is not None:
                Gm, addt, S = found
                edges = [(x, Gm + int(addt[x, s])) for x in range(Gm) for s in S]
                consider(2 * Gm, edges)
            if best_n >= target:
                break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
