import itertools
import math
import random
import time

import lib

ITERS = 1200            # annealing steps per (group, base-graph) attempt
T_HOT = 1.5             # initial annealing temperature (in unreached-pair units)
T_COLD = 0.1            # final annealing temperature
GROUPS_PER_ATTEMPT = 10  # groups tried per attempt at a given (t, N)
T_LIST = (2, 3, 4, 1, 5)  # number of orbits per side of the lifted base graph


# ----------------------------------------------------------------------------
# Fallback families (always checked with lib.is_valid before use).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Multi-orbit bi-Cayley lifts.
#
# A base bipartite multigraph with t A-orbits and t B-orbits, d-regular on
# both sides, is lifted over a finite group G of order N. Dart p = (i, j, s)
# with p // d == i and target orbit Js[p] = j joins A_{i,x} to B_{j, x*s}.
# Left multiplication is an automorphism, so the diameter is decided by BFS
# from one source per orbit (A_{i,e} and B_{j,e}).
#
# The search anneals over both the voltages (Ss) and the base wiring (Js,
# by swapping target orbits between darts, which preserves B-degrees).
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _unreached(t, N, T, invs, Ss, Js, d, D):
    """Total count of (source, vertex) pairs not within distance D, over one source per orbit."""
    M = t * N
    V = 2 * M
    out_adj = [[] for _ in range(t)]
    in_adj = [[] for _ in range(t)]
    for p in range(t * d):
        i = p // d
        out_adj[i].append((Js[p], Ss[p]))
        in_adj[Js[p]].append((i, invs[Ss[p]]))
    srcs = [i * N for i in range(t)] + [M + j * N for j in range(t)]
    total = 0
    for src in srcs:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < M:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, s in out_adj[i]:
                        v = M + j * N + row[s]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - M, N)
                    row = T[y]
                    for i, si in in_adj[j]:
                        v = i * N + row[si]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += V - cnt
    return total


def _ok(Ss, Js, d, p, j, s):
    """True if no other dart in p's A-group already uses the pair (j, s)."""
    i0 = (p // d) * d
    for q in range(i0, i0 + d):
        if q != p and Js[q] == j and Ss[q] == s:
            return False
    return True


def _anneal(t, N, T, invs, d, D, rng, iters, deadline):
    """Anneal voltages and base wiring to reach diameter <= D. Returns (Ss, Js) or None."""
    P = t * d
    Js = [j for j in range(t) for _ in range(d)]
    rng.shuffle(Js)
    Ss = [0] * P
    for p in range(P):
        i0 = (p // d) * d
        taken = {(Js[q], Ss[q]) for q in range(i0, p)}
        s = rng.randrange(N)
        while (Js[p], s) in taken:
            s = rng.randrange(N)
        Ss[p] = s

    cur = _unreached(t, N, T, invs, Ss, Js, d, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        if rng.random() < 0.5:
            # Voltage move: change one shift.
            p = rng.randrange(P)
            c = rng.randrange(N)
            if c == Ss[p] or not _ok(Ss, Js, d, p, Js[p], c):
                continue
            old = Ss[p]
            Ss[p] = c
            v = _unreached(t, N, T, invs, Ss, Js, d, D)
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                Ss[p] = old
        else:
            # Wiring move: swap target orbits of two darts in different A-groups.
            p = rng.randrange(P)
            q = rng.randrange(P)
            if p // d == q // d or Js[p] == Js[q]:
                continue
            if not (_ok(Ss, Js, d, p, Js[q], Ss[p]) and _ok(Ss, Js, d, q, Js[p], Ss[q])):
                continue
            Js[p], Js[q] = Js[q], Js[p]
            v = _unreached(t, N, T, invs, Ss, Js, d, D)
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                Js[p], Js[q] = Js[q], Js[p]
    if cur == 0:
        return Ss, Js
    return None


def _lift_edges(t, N, T, Ss, Js, d):
    """Expand the base description into an explicit (n, edges) graph."""
    M = t * N
    edges = []
    for p in range(t * d):
        i = p // d
        j = Js[p]
        s = Ss[p]
        for x in range(N):
            edges.append((i * N + x, M + j * N + T[x][s]))
    return 2 * M, edges


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.85 * time_limit, time_limit - 5.0)
    if d < 1 or D < 1:
        return 1, []

    rng = random.Random(seed)
    best = [1, []]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0] = n
            best[1] = e

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best[0], best[1]

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
        return best[0], best[1]

    # Search over multi-orbit lifts. Total vertices is 2*t*N; per-side tN <= Moore/2.
    M_bound = lib._moore_bound(d, D)
    half = M_bound // 2

    def need_N(t, bn):
        # Smallest N with 2*t*N > bn.
        return max(d + 1, bn // (2 * t) + 1)

    cur_N = {t: d + 1 for t in T_LIST}
    budget = 1.0
    while time.monotonic() < deadline:
        progressed = False
        active = False
        for t in T_LIST:
            if time.monotonic() >= deadline:
                break
            N = max(cur_N[t], need_N(t, best[0]))
            if N > half // t:
                continue
            active = True
            att_deadline = min(deadline, time.monotonic() + budget)
            groups = _groups(N)
            rng.shuffle(groups)
            found = None
            for m, k, r in groups[:GROUPS_PER_ATTEMPT]:
                if time.monotonic() >= att_deadline:
                    break
                order, mul, inv = lib.semidirect_group(m, k, r)
                T = [[mul(x, g) for g in range(N)] for x in range(N)]
                invs = [inv(g) for g in range(N)]
                res = _anneal(t, N, T, invs, d, D, rng, ITERS, att_deadline)
                if res is not None:
                    found = (T, res[0], res[1])
                    break
            if found is not None:
                T, Ss, Js = found
                n, e = _lift_edges(t, N, T, Ss, Js, d)
                consider(n, e)
                cur_N[t] = N + 1
                progressed = True
            else:
                cur_N[t] = N
        if not active:
            break
        if not progressed:
            budget *= 1.8

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best[0], best[1]
