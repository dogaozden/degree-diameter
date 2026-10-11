import math
import random
import time

import lib

ITERS = 1500          # annealing steps per attempt
TEMP0 = 1.5           # starting annealing temperature (in unreached-pair units)
_TABLE_CACHE = {}


def _groups(N, d):
    """Semidirect parameters (m, k, r) giving groups Z_m x| Z_k of order N (cyclic included)."""
    out = []
    if N < d:
        return out
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _table(N, m, k, r):
    """Multiplication table T[x][g] and inverse list Ti[g] for the group (identity is element 0)."""
    key = (N, m, k, r)
    if key in _TABLE_CACHE:
        return _TABLE_CACHE[key]
    if len(_TABLE_CACHE) > 64:
        _TABLE_CACHE.clear()
    _, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    Ti = [inv(g) for g in range(N)]
    _TABLE_CACHE[key] = (T, Ti)
    return T, Ti


def _connected(p, M):
    """Is the base bipartite multigraph (p A-vertices, p B-vertices, multiplicities M) connected?"""
    seenA, seenB = {0}, set()
    stack = [(0, 0)]
    while stack:
        side, idx = stack.pop()
        if side == 0:
            for j in range(p):
                if M[idx][j] and j not in seenB:
                    seenB.add(j)
                    stack.append((1, j))
        else:
            for i in range(p):
                if M[i][idx] and i not in seenA:
                    seenA.add(i)
                    stack.append((0, i))
    return len(seenA) == p and len(seenB) == p


def _base_matrix(p, d, rng):
    """Random p x p nonnegative integer matrix with all row and column sums d, connected."""
    for _ in range(50):
        M = [[0] * p for _ in range(p)]
        for _ in range(d):
            perm = list(range(p))
            rng.shuffle(perm)
            for i in range(p):
                M[i][perm[i]] += 1
        if _connected(p, M):
            return M
    return None


def _cost(p, N, T, Ti, cells, D):
    """Total (source, vertex) pairs at distance > D over the 2p base sources.

    Left multiplication by the group is an automorphism of the lift, so checking one
    representative per base vertex decides the diameter.
    """
    nbrA = [[] for _ in range(p)]
    nbrB = [[] for _ in range(p)]
    for i in range(p):
        for j in range(p):
            for g in cells[i][j]:
                nbrA[i].append((j, g))
                nbrB[j].append((i, Ti[g]))
    Bo = p * N
    total_v = 2 * p * N
    sources = [i * N for i in range(p)] + [Bo + j * N for j in range(p)]
    cost = 0
    for s in sources:
        seen = bytearray(total_v)
        seen[s] = 1
        reached = 1
        frontier = [s]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < Bo:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in nbrA[i]:
                        v = Bo + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - Bo, N)
                    row = T[y]
                    for i, h in nbrB[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            reached += len(nxt)
            frontier = nxt
            if not frontier:
                break
        cost += total_v - reached
    return cost


def _anneal(p, N, T, Ti, M, D, rng, iters, deadline):
    """Anneal the group elements on the darts (each A_i-B_j cell gets M[i][j] distinct elements)."""
    slots = [(i, j) for i in range(p) for j in range(p) if M[i][j]]
    cells = [[[] for _ in range(p)] for _ in range(p)]
    for i, j in slots:
        cells[i][j] = rng.sample(range(N), M[i][j])
    cur = _cost(p, N, T, Ti, cells, D)
    for it in range(iters):
        if cur == 0:
            return cells
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        temp = max(0.05, TEMP0 * (1.0 - it / iters))
        i, j = slots[rng.randrange(len(slots))]
        lst = cells[i][j]
        t = rng.randrange(len(lst))
        c = rng.randrange(N)
        if c in lst:
            continue
        old = lst[t]
        lst[t] = c
        v = _cost(p, N, T, Ti, cells, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            lst[t] = old
    return cells if cur == 0 else None


def _edges(p, N, T, cells):
    """Lift to a bipartite graph: A_(i,x) joined to B_(j, x*g) for each dart (i, j, g)."""
    Bo = p * N
    e = []
    for i in range(p):
        for j in range(p):
            for g in cells[i][j]:
                for x in range(N):
                    e.append((i * N + x, Bo + j * N + T[x][g]))
    return 2 * p * N, e


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.3, min(0.8 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = {"n": 1, "e": []}

    def consider(n, e):
        if n > best["n"] and lib.is_valid(n, e, d, D):
            best["n"] = n
            best["e"] = e

    if D == 1:
        consider(2, [(0, 1)])
        return best["n"], best["e"]

    # Safe fallback: K_{d,d} has diameter 2.
    consider(2 * d, [(i, d + j) for i in range(d) for j in range(d)])
    if D == 2:
        return best["n"], best["e"]

    if d == 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])
        return best["n"], best["e"]

    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except (ValueError, RuntimeError):
                pass
        if lib.is_prime_power(d - 1):
            return best["n"], best["e"]

    Moore = lib._moore_bound(d, D)
    Nmax = {p: Moore // (2 * p) for p in (1, 2, 3)}

    # Bold search: lifts of small base bipartite multigraphs (p x p, degree d) over
    # semidirect products. Larger p means more base vertices, so the group order is smaller.
    while time.monotonic() < deadline:
        p = rng.choices((1, 2, 3), weights=(1, 3, 1))[0]
        lo = best["n"] // (2 * p) + 1
        hi = Nmax[p]
        if lo > hi:
            if all(best["n"] // (2 * q) + 1 > Nmax[q] for q in (1, 2, 3)):
                break
            continue
        N = lo + int((hi - lo) * rng.random() ** 2)
        groups = _groups(N, d)
        if not groups:
            continue
        m, k, r = rng.choice(groups)
        M = _base_matrix(p, d, rng)
        if M is None:
            continue
        T, Ti = _table(N, m, k, r)
        cells = _anneal(p, N, T, Ti, M, D, rng, ITERS, deadline)
        if cells is not None:
            n, e = _edges(p, N, T, cells)
            consider(n, e)

    return best["n"], best["e"]
