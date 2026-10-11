import math
import random
import time

import numpy as np

import lib


def _fallback(d, D):
    """Safe, verified-by-construction graphs used whenever the search fails."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:
        return lib.haar_graph(d, range(d))
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)
        except Exception:
            pass
    return lib.haar_graph(d, range(d))


# ----------------------------------------------------------------- groups

def _group_list(N, rng):
    """Candidate groups of order N: cyclic, plus semidirect Z_m x| Z_k."""
    groups = [lib.cyclic_group(N)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:6]:
            try:
                groups.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return groups


# ------------------------------------------- multi-orbit regular base search
#
# NEW ROUTINE: k-orbit group lifts. Take k "A" orbits and k "B" orbits of a
# group G (2k base vertices, order 2kN in total). Base darts (u, w, g) with
# u in A, w in B join a_{u,x} to b_{w, x*g}. Each A orbit and each B orbit
# carries exactly d darts, so the lift is d-regular and bipartite.
#
# Left translation is an automorphism, so every pair of vertices is at distance
# <= 3 iff every orbit representative (orbit o, identity element) reaches
# everything within 3 steps. The cost of a base is the number of unreached
# (representative, vertex) pairs, computed with a numpy ball expansion. The
# search is simulated annealing over darts, using moves that either change one
# dart's group label or swap the B-endpoints of two darts. Both moves keep the
# degrees exact.

def _tables(N, mul, inv):
    """fwd[g][x] = x*g and bwd[g][y] = y*g^{-1} as numpy arrays."""
    mtn = np.array([[mul(x, g) for g in range(N)] for x in range(N)], dtype=np.int64)
    ivs = [inv(g) for g in range(N)]
    fwd = [mtn[:, g].copy() for g in range(N)]
    bwd = [mtn[:, ivs[g]].copy() for g in range(N)]
    return fwd, bwd


def _cost(darts, V, N, fwd, bwd):
    """Number of (representative, vertex) pairs NOT within distance 3."""
    reach = np.zeros((V, V, N), dtype=bool)
    idx = np.arange(V)
    reach[idx, idx, 0] = True
    for _ in range(3):
        new = reach.copy()
        for u, w, g in darts:
            new[:, w, fwd[g]] |= reach[:, u, :]
            new[:, u, bwd[g]] |= reach[:, w, :]
        reach = new
    return V * V * N - int(reach.sum())


def _random_darts(k, d, N, rng):
    """A random d-regular bipartite base on k+k orbits, with distinct (u, w, g)."""
    A = [u for u in range(k) for _ in range(d)]
    B = [k + w for w in range(k) for _ in range(d)]
    rng.shuffle(B)
    darts, keys = [], set()
    for u, w in zip(A, B):
        g = rng.randrange(N)
        while (u, w, g) in keys:
            g = rng.randrange(N)
        t = (u, w, g)
        darts.append(t)
        keys.add(t)
    return darts, keys


def _anneal(k, N, fwd, bwd, d, rng):
    """Generator: yields None periodically; yields a valid dart list when found."""
    V = 2 * k
    steps = 40000
    while True:
        darts, keys = _random_darts(k, d, N, rng)
        cost = _cost(darts, V, N, fwd, bwd)
        for step in range(steps):
            if cost == 0:
                break
            if step % 200 == 0:
                yield None
            T = 0.1 + 0.8 * (1 - step / steps)
            i = rng.randrange(len(darts))
            if rng.random() < 0.5:
                u, w, g = darts[i]
                g2 = rng.randrange(N)
                if g2 == g or (u, w, g2) in keys:
                    continue
                changes = {i: (u, w, g2)}
            else:
                j = rng.randrange(len(darts))
                ui, wi, gi = darts[i]
                uj, wj, gj = darts[j]
                if wi == wj:
                    continue
                a = (ui, wj, gi)
                b = (uj, wi, gj)
                if a in keys or b in keys:
                    continue
                changes = {i: a, j: b}
            old = {x: darts[x] for x in changes}
            for t in old.values():
                keys.discard(t)
            for x, t in changes.items():
                darts[x] = t
                keys.add(t)
            new_cost = _cost(darts, V, N, fwd, bwd)
            delta = new_cost - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = new_cost
            else:
                for t in changes.values():
                    keys.discard(t)
                for x, t in old.items():
                    darts[x] = t
                    keys.add(t)
        if cost == 0:
            yield list(darts)
            return


def _gen(k, N, mul, inv, d, rng):
    fwd, bwd = _tables(N, mul, inv)
    yield from _anneal(k, N, fwd, bwd, d, rng)


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 2.0)
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    M = lib.moore_bound(d, D)

    # Candidates: (order n = 2kN, k, N, mul, inv), restricted to n > base_n.
    cands = []
    for k in range(1, min(d, 4) + 1):
        for N in range(M // (2 * k), d - 1, -1):
            n = 2 * k * N
            if n <= base_n:
                break
            for _order, mul, inv in _group_list(N, rng):
                cands.append((n, k, N, mul, inv))
    # Smallest order above the current best first: these are the easiest.
    cands.sort(key=lambda c: c[0])
    cands = cands[:60]

    active = [[n, k, N, mul, _gen(k, N, mul, inv, d, rng)]
              for n, k, N, mul, inv in cands]

    best_n, best = base_n, (base_n, base_e)
    while active and time.monotonic() < deadline:
        for entry in list(active):
            if time.monotonic() >= deadline:
                break
            n, k, N, mul, gen = entry
            if n <= best_n:
                active.remove(entry)
                continue
            try:
                res = next(gen)
            except StopIteration:
                active.remove(entry)
                continue
            if res is None:
                continue
            active.remove(entry)
            nn, edges = lib.group_lift(2 * k, res, N, mul)
            if nn > best_n and lib.is_valid(nn, edges, d, D):
                best_n, best = nn, (nn, edges)
                active = [e for e in active if e[0] > best_n]
                break
        active = [e for e in active if e[0] > best_n]

    return best
