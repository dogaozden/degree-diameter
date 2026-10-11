import math
import random
import time

import numpy as np

import lib


def _is_prime(p):
    if p < 2:
        return False
    i = 2
    while i * i <= p:
        if p % i == 0:
            return False
        i += 1
    return True


def _mult_order(r, m):
    """Multiplicative order of r modulo m (assumes gcd(r, m) = 1)."""
    one = 1 % m
    x = r % m
    o = 1
    while x != one:
        x = x * r % m
        o += 1
    return o


def _semidirect_table(m, k, r):
    """Cayley table M[x, y] = x*y of Z_m x|_r Z_k; element (a, b) is coded a*k + b.

    Product: (a, b)(c, d) = (a + r^b c, b + d). Needs r^k = 1 mod m.
    Identity is code 0.
    """
    G = m * k
    codes = np.arange(G, dtype=np.int64)
    A = codes // k
    B = codes % k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    Ax = A[:, None]
    Bx = B[:, None]
    Ay = A[None, :]
    By = B[None, :]
    return ((Ax + pw[Bx] * Ay) % m) * k + (Bx + By) % k


def _group_specs(G, rng):
    """Up to 3 semidirect-product specs (priority, m, k, r) of order G.

    Priority 0: Frobenius-type Z_p x| Z_k with p prime (affine-like groups).
    Priority 1: other semidirect products. Priority 2: cyclic.
    """
    specs = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        if k == 1:
            specs.append((2, m, 1, 1))
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not rs:
            continue
        exact = [r for r in rs if _mult_order(r, m) == k]
        pool = exact if exact else rs
        if len(pool) > 2:
            pool = rng.sample(pool, 2)
        pri = 0 if _is_prime(m) else 1
        for r in pool:
            specs.append((pri, m, k, r))
    specs.sort(key=lambda t: t[0])
    return specs[:3]


def _cost(M, inv, S, G, D):
    """Unreached (source, vertex) pairs from A_1 and B_1 within D steps. Zero iff diameter <= D.

    Bi-Cayley graph: A_x ~ B_{x s}. Left multiplication is an automorphism with
    two vertex orbits (A side and B side), so checking the two sources suffices.
    """
    Sa = np.asarray(S, dtype=np.int64)
    adj = np.vstack([G + M[:, Sa], M[:, inv[Sa]]])
    N = 2 * G
    total = 0
    for src in (0, G):
        seen = np.zeros(N, dtype=bool)
        seen[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            mark = np.zeros(N, dtype=bool)
            mark[adj[frontier].ravel()] = True
            new = mark & ~seen
            if not new.any():
                break
            seen |= new
            frontier = np.flatnonzero(new)
        total += N - int(seen.sum())
    return total


def _anneal(M, inv, G, d, D, rng, deadline, iters):
    """Simulated annealing over connection sets S (|S| = d, distinct). Returns S or None."""
    S = rng.sample(range(G), d)
    c = _cost(M, inv, S, G, D)
    T = 1.0
    for it in range(iters):
        if c == 0:
            break
        if (it & 31) == 0 and time.monotonic() >= deadline:
            break
        i = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        S2 = S[:]
        S2[i] = x
        c2 = _cost(M, inv, S2, G, D)
        if c2 <= c or rng.random() < math.exp((c - c2) / T):
            S, c = S2, c2
        T = max(0.05, T * 0.995)
    return S if c == 0 else None


def _edges_from(M, S, G):
    """Bi-Cayley graph edges: A_x = x, B_w = G + w, A_x ~ B_{x*s}."""
    d = len(S)
    Sa = np.asarray(S, dtype=np.int64)
    xs = np.repeat(np.arange(G, dtype=np.int64), d)
    ys = G + M[:, Sa].ravel()
    return 2 * G, list(zip(xs.tolist(), ys.tolist()))


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    # D = 3: projective-plane incidence and the Araujo-Pardo-Lopez graph.
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    # Main family: bi-Cayley graphs over semidirect products Z_m x| Z_k.
    # Order G gives 2G vertices and d-regularity. Orders are scanned upward,
    # and only orders that would beat the current best are tried.
    mh = lib.moore_bound(d, D) // 2
    lo = max(d, int(0.4 * mh))
    hi = min(mh, max(lo + 8, int(0.8 * mh) + 1))
    if lo <= hi:
        rng = random.Random(seed * 1000003 + d * 131 + D)
        cache = {}
        sched = [150, 500, 2000, 8000]
        rnd = 0
        while time.monotonic() < deadline:
            base_iters = sched[min(rnd, len(sched) - 1)]
            rnd += 1
            did = False
            for G in range(lo, hi + 1):
                if time.monotonic() >= deadline:
                    break
                if 2 * G <= best_n:
                    continue
                if G not in cache:
                    cache[G] = _group_specs(G, random.Random(seed * 7919 + G * 31 + d))
                for pri, m, k, r in cache[G]:
                    if time.monotonic() >= deadline or 2 * G <= best_n:
                        break
                    M = _semidirect_table(m, k, r)
                    inv = np.argmax(M == 0, axis=1)
                    iters = base_iters * (4 if pri == 0 else 1)
                    did = True
                    S = _anneal(M, inv, G, d, D, rng, deadline, iters)
                    if S is not None:
                        consider(*_edges_from(M, S, G))
            if not did:
                break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
