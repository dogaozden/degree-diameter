import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over small groups: A_x ~ B_{x*s} for s in S, |S| = d.
# The group acts regularly on each side, so diameter <= D holds iff a BFS from
# A_e and from B_e reaches everything within D steps. Groups are semidirect
# products Z_m x| Z_k, coded as a*k + b. The search is a simulated annealing
# over the connection set S with a fast numpy cost.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (m, k, r) for a random semidirect product Z_m x| Z_k of order G, or None."""
    ks = [k for k in range(1, 13) if G % k == 0 and G // k >= 2]
    rng.shuffle(ks)
    for k in ks:
        m = G // k
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if cands:
            return m, k, rng.choice(cands)
    return None


def _table(m, k, r):
    """Multiplication table (G x G) of Z_m x| Z_k with (a,b)*(c,e) = (a + r^b c, b + e)."""
    G = m * k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    x = np.arange(G, dtype=np.int64)
    a, b = x // k, x % k
    prod_a = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    prod_b = (b[:, None] + b[None, :]) % k
    return prod_a * k + prod_b


def _cost(mul, Sa, Sinv, G, D):
    """Number of (source, vertex) pairs at distance > D, sources A_e and B_e."""
    total = 0
    for src in (0, 1):
        seen = [np.zeros(G, dtype=bool), np.zeros(G, dtype=bool)]
        seen[src][0] = True
        front = np.array([0], dtype=np.int64)
        side = src
        for _ in range(D):
            tab = Sa if side == 0 else Sinv
            vals = mul[front][:, tab].ravel()
            nxt = np.zeros(G, dtype=bool)
            nxt[vals] = True
            nxt &= ~seen[1 - side]
            if not nxt.any():
                break
            seen[1 - side] |= nxt
            front = np.flatnonzero(nxt)
            side = 1 - side
        total += 2 * G - int(seen[0].sum()) - int(seen[1].sum())
    return total


def _anneal(mul, inv, G, d, D, rng, end, max_iters):
    """Anneal a connection set S of d distinct group elements. Returns (S or None, cost)."""
    S = rng.sample(range(G), d)
    Sa = np.array(S, dtype=np.int64)
    Sinv = inv[Sa]
    cur = _cost(mul, Sa, Sinv, G, D)
    T = 2.0
    for _ in range(max_iters):
        if cur == 0 or time.monotonic() >= end:
            break
        T = max(0.1, T * 0.9993)
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        S2 = list(S)
        S2[i] = x
        Sa2 = np.array(S2, dtype=np.int64)
        Sinv2 = inv[Sa2]
        c = _cost(mul, Sa2, Sinv2, G, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            S, cur = S2, c
    return (S if cur == 0 else None), cur


def _edges(G, mul, S):
    """Edge list of the bi-Cayley graph: A_a = a, B_h = G + h, edges A_a ~ B_{a*s}."""
    out = []
    for a in range(G):
        for s in S:
            out.append((a, G + int(mul[a, s])))
    return 2 * G, out


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.80 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if D == 2 or d < 2:
        return best_n, best_e

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    # Projective plane (diameter 3) and Araujo-Pardo-Lopez for d = q + 2.
    try:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            consider(*lib.araujo_lopez_graph(d - 2))
    except Exception:
        pass

    if best_n >= lib.moore_bound(d, D):
        return best_n, best_e

    # Main search: bi-Cayley graphs over semidirect products, growing the order.
    rng = random.Random(seed * 7919 + 31 * d + D)
    try:
        while time.monotonic() < deadline:
            lo = best_n // 2 + 1
            G = rng.randint(lo, lo + 3)
            grp = _sample_group(G, rng)
            if grp is None:
                continue
            m, k, r = grp
            mul = _table(m, k, r)
            inv = np.argmax(mul == 0, axis=1)
            end = min(deadline, time.monotonic() + 5.0)
            S, _ = _anneal(mul, inv, G, d, D, rng, end, 6000)
            if S is not None:
                n, e = _edges(G, mul, S)
                consider(n, e)
    except Exception:
        pass

    return best_n, best_e
