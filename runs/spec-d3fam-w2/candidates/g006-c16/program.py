import math
import random
import time

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
        return lib.haar_graph(d, range(d))          # K_{d,d}, diameter 2
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)  # Moore-extremal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)    # record construction
        except Exception:
            pass
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------
# New construction: group-invariant bipartite lifts with k base vertices
# per side. A lift over a group G of order N has 2kN vertices. Every
# vertex orbit is a base vertex, so the diameter is <= 3 iff the radius-3
# ball around each of the 2k base vertices (at the identity) covers the
# whole lift. That needs only 2k BFS runs, so the search cost is cheap.
# Moves: change a voltage, or swap B-endpoints of two darts (keeps degrees).
# ------------------------------------------------------------------

def _groups(N, rng, limit):
    """(mul, inv) pairs for cyclic Z_N and a few semidirect Z_m x| Z_k of order N."""
    out = [lib.cyclic_group(N)[1:]]
    for k2 in range(2, N + 1):
        if N % k2:
            continue
        m = N // k2
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:limit]:
            try:
                _, mul, inv = lib.semidirect_group(m, k2, r)
                out.append((mul, inv))
            except ValueError:
                pass
    return out


def _cost(k, N, M, INV, darts):
    """Number of (source, vertex) pairs NOT within distance 3 of a base vertex.

    Zero iff the lift has diameter <= 3. Node index = side*N + x, where
    sides 0..k-1 are A vertices and k..2k-1 are B vertices.
    """
    adjA = [[] for _ in range(k)]
    adjB = [[] for _ in range(k)]
    for i, j, g in darts:
        adjA[i].append((j, g))
        adjB[j].append((i, INV[g]))
    total = 2 * k * N
    unreached = 0
    for s in range(2 * k):
        seen = bytearray(total)
        seen[s * N] = 1  # identity element is 0 in every group used
        frontier = [s * N]
        count = 1
        for _ in range(3):
            new = []
            for v in frontier:
                node, x = divmod(v, N)
                row = M[x]
                if node < k:
                    for j, g in adjA[node]:
                        w = (k + j) * N + row[g]
                        if not seen[w]:
                            seen[w] = 1
                            new.append(w)
                else:
                    for i, gi in adjB[node - k]:
                        w = i * N + row[gi]
                        if not seen[w]:
                            seen[w] = 1
                            new.append(w)
            frontier = new
            count += len(new)
            if not new:
                break
        unreached += total - count
    return unreached


def _anneal(k, N, mul, inv, d, rng):
    """Generator: anneal darts for a k-vertex-per-side lift. Yields None each step;
    yields the dart list once cost reaches 0."""
    M = [[mul(x, g) for g in range(N)] for x in range(N)]
    INV = [inv(g) for g in range(N)]
    while True:
        A = [i for i in range(k) for _ in range(d)]
        B = [j for j in range(k) for _ in range(d)]
        rng.shuffle(B)
        darts = [[A[t], B[t], rng.randrange(N)] for t in range(len(A))]
        cost = _cost(k, N, M, INV, darts)
        T = 2.0
        for _step in range(40000):
            if cost == 0:
                break
            yield None
            t = rng.randrange(len(darts))
            if rng.random() < 0.5:
                old = darts[t][2]
                darts[t][2] = rng.randrange(N)
                new = _cost(k, N, M, INV, darts)
                if new <= cost or rng.random() < math.exp(-(new - cost) / T):
                    cost = new
                else:
                    darts[t][2] = old
            else:
                u = rng.randrange(len(darts))
                if u == t:
                    continue
                darts[t][1], darts[u][1] = darts[u][1], darts[t][1]
                new = _cost(k, N, M, INV, darts)
                if new <= cost or rng.random() < math.exp(-(new - cost) / T):
                    cost = new
                else:
                    darts[t][1], darts[u][1] = darts[u][1], darts[t][1]
            T = max(0.05, T * 0.9995)
        if cost == 0:
            yield [tuple(x) for x in darts]
            return


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 3.0)
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    moore = lib.moore_bound(d, D)

    # Tasks: (k, N, generator). Each must give 2kN > current best order.
    active = []
    for k in (2, 3, 4, 1):
        lo = base_n // (2 * k) + 1
        hi = moore // (2 * k)
        for N in range(hi, lo - 1, -1):
            if N < 2:
                continue
            for mul, inv in _groups(N, rng, 3):
                active.append([k, N, _anneal(k, N, mul, inv, d, rng)])

    best = None
    best_n = base_n
    while active and time.monotonic() < deadline:
        for entry in list(active):
            if time.monotonic() >= deadline:
                break
            k, N, gen = entry
            if 2 * k * N <= best_n:
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
            n, edges = lib.group_lift(2 * k, [(i, k + j, g) for i, j, g in res], N,
                                      _mul_for(entry, res, N, k, d, rng))
            if n > best_n and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_n = n
        active = [e for e in active if 2 * e[0] * e[1] > best_n]

    if best is not None:
        return best
    return base_n, base_e


def _mul_for(entry, res, N, k, d, rng):
    """Recover the multiplication used by a task (stored on the generator's group)."""
    return entry[3]
