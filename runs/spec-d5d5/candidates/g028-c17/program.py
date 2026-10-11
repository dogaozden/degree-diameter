import itertools
import math
import random
import time

import lib

MAX_GROUPS = 12    # groups tried per (p, N) attempt
ITERS = 400        # annealing steps per (group, base layout) try
T_HOT = 1.5
T_COLD = 0.1


# ----------------------------------------------------------------------------
# Baseline families (always validated before use).
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p_ in L:
                for r_ in L:
                    if p_ < r_:
                        covered.add((p_, r_))
    edges = []
    for j, L in enumerate(lines):
        for p_ in L:
            edges.append((p_, P + j))
    return 2 * P, edges


def _best_gq(d):
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Lift search over base multigraphs with p vertices per side (p = 1 or 2).
#
# Base: A_0..A_{p-1}, B_0..B_{p-1}; each dart (i, j) carries a voltage h in G,
# joining (A_i, x) to (B_j, x*h). Every vertex has degree d. Voltages on the
# same (i, j) cell are distinct, so the lift is simple. Left multiplication by G
# is an automorphism, so distances are determined by BFS from the 2p
# representatives (A_i, e) and (B_j, e).
# ----------------------------------------------------------------------------

def _groups(N):
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _layout(p, d, a):
    if p == 1:
        spec = [(0, 0, d)]
    else:
        spec = [(0, 0, a), (0, 1, d - a), (1, 0, d - a), (1, 1, a)]
    darts, cell_of, cells = [], [], []
    for i, j, cnt in spec:
        if cnt <= 0:
            continue
        members = []
        for _ in range(cnt):
            members.append(len(darts))
            darts.append((i, j))
            cell_of.append(len(cells))
        cells.append(members)
    return darts, cell_of, cells


def _unreached(p, N, T, invs, darts, V, D):
    NA = p * N
    tot = 2 * NA
    outA = [[] for _ in range(p)]
    inB = [[] for _ in range(p)]
    for t, (i, j) in enumerate(darts):
        h = V[t]
        outA[i].append((j, h))
        inB[j].append((i, invs[h]))
    total = 0
    for s in range(2 * p):
        src = s * N if s < p else NA + (s - p) * N
        seen = bytearray(tot)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < NA:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, h in outA[i]:
                        v = NA + j * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - NA, N)
                    row = T[y]
                    for i, hi in inB[j]:
                        v = i * N + row[hi]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += tot - count
    return total


def _anneal(p, N, T, invs, darts, cell_of, cells, d, D, rng, iters, deadline):
    V = [0] * len(darts)
    for cell in cells:
        for t, v in zip(cell, rng.sample(range(N), len(cell))):
            V[t] = v
    cur = _unreached(p, N, T, invs, darts, V, D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        t = rng.randrange(len(darts))
        cell = cells[cell_of[t]]
        c = rng.randrange(N)
        if any(V[u] == c for u in cell if u != t):
            continue
        old = V[t]
        V[t] = c
        v = _unreached(p, N, T, invs, darts, V, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            V[t] = old
    return V if cur == 0 else None


def _attempt(p, N, d, D, rng, deadline):
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        a = rng.randint(1, d - 1) if p == 2 else d
        darts, cell_of, cells = _layout(p, d, a)
        V = _anneal(p, N, T, invs, darts, cell_of, cells, d, D, rng, ITERS, deadline)
        if V is not None:
            return T, darts, V
    return None


def _lift_edges(p, N, T, darts, V):
    NA = p * N
    edges = []
    for t, (i, j) in enumerate(darts):
        h = V[t]
        for x in range(N):
            edges.append((i * N + x, NA + j * N + T[x][h]))
    return 2 * NA, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])
    best_n = 1

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    moore = lib._moore_bound(d, D)
    caps = {2: moore // 4, 1: min(moore // 2, moore // 4 + 8)}
    lo = d + 1
    failed = {}          # (p, N) -> budget at which it last failed
    budget = 0.5

    while time.monotonic() < deadline:
        cands = []
        for p in (2, 1):
            for N in range(lo, caps[p] + 1):
                v = 2 * p * N
                if best_n < v <= moore:
                    cands.append((v, p, N))
        if not cands:
            break
        cands.sort(reverse=True)

        for v, p, N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            if failed.get((p, N), 0) >= budget:
                continue
            att_deadline = min(deadline, now + budget)
            res = _attempt(p, N, d, D, rng, att_deadline)
            if res is None:
                failed[(p, N)] = budget
                continue
            T, darts, V = res
            n, e = _lift_edges(p, N, T, darts, V)
            consider(n, e)
            break

        budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
