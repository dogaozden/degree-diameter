import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bases (from parent).
# ----------------------------------------------------------------------------

def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq(q):
    """Point-line incidence graph of the symplectic generalized quadrangle W(q)."""
    F = lib.GF(q)
    A = F.add_table.tolist()
    M = F.mul_table.tolist()
    NEG = [F.neg(a) for a in range(q)]
    INV = [0] + [F.inv(a) for a in range(1, q)]
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    P = len(pts)
    index = {v: i for i, v in enumerate(pts)}

    def norm(v):
        c = next(x for x in v if x)
        ic = INV[c]
        return tuple(M[ic][x] for x in v)

    covered = [bytearray(P) for _ in range(P)]
    lines = []
    for i in range(P):
        x = pts[i]
        ci = covered[i]
        for j in range(i + 1, P):
            if ci[j]:
                continue
            y = pts[j]
            t = A[M[x[0]][y[1]]][NEG[M[x[1]][y[0]]]]
            s = A[M[x[2]][y[3]]][NEG[M[x[3]][y[2]]]]
            if A[t][s] != 0:
                continue
            L = set()
            for a in range(q):
                ax = [M[a][x[k]] for k in range(4)]
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(A[ax[k]][M[b][y[k]]] for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                cp = covered[p]
                for r in L:
                    cp[r] = 1
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return P + len(lines), edges


# ----------------------------------------------------------------------------
# Twin blow-up (from parent).
# ----------------------------------------------------------------------------

def _independent_set(N, nb, rng, nprng, deadline):
    """Iterated local search for a large set of vertices with no conflicting pair."""
    nbn = [np.asarray(x, dtype=np.int64) for x in nb]
    cnt = np.zeros(N, dtype=np.int64)
    inS = np.zeros(N, dtype=bool)
    tabu = np.zeros(N, dtype=np.int64)
    S = []
    conf = 0
    best = []
    best_size = 0
    it = 0
    last_best_it = 0

    def add(v):
        nonlocal conf
        conf += int(cnt[v])
        cnt[nbn[v]] += 1
        inS[v] = True
        S.append(v)

    def remove(u):
        nonlocal conf
        conf -= int(cnt[u])
        cnt[nbn[u]] -= 1
        inS[u] = False
        S.remove(u)

    def pick():
        score = cnt + nprng.random(N)
        score[inS] = np.inf
        score[tabu > it] = np.inf
        return int(np.argmin(score))

    while True:
        it += 1
        if (it & 63) == 0 and time.monotonic() >= deadline:
            break
        if conf == 0:
            if len(S) > best_size:
                best = list(S)
                best_size = len(S)
                last_best_it = it
            add(pick())
        else:
            conflicting = [u for u in S if cnt[u] > 0]
            u = conflicting[rng.randrange(len(conflicting))]
            remove(u)
            tabu[u] = it + 5 + rng.randrange(8)
            add(pick())
        if S and it - last_best_it > 15000:
            u = S[rng.randrange(len(S))]
            remove(u)
            tabu[u] = it + 5
            last_best_it = it
    if conf == 0 and len(S) > best_size:
        best = list(S)
    return best


def _blow(n0, edges0, S):
    """Blow up each vertex of S into two twin copies (same neighbourhood)."""
    extra = {}
    for v in S:
        extra[v] = n0 + len(extra)
    copies = [[v] + ([extra[v]] if v in extra else []) for v in range(n0)]
    edges = []
    for u, v in edges0:
        for a in copies[u]:
            for b in copies[v]:
                edges.append((a, b))
    return n0 + len(extra), edges


def _blowup(n0, edges0, d, deadline, rng, nprng):
    """Twin blow-up of a base graph of degree d-1 by a large distance-2-free set."""
    adj = [[] for _ in range(n0)]
    for u, v in edges0:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != d - 1 for a in adj):
        return None
    cs = [set() for _ in range(n0)]
    for w in range(n0):
        a = adj[w]
        for i in range(len(a)):
            for j in range(i + 1, len(a)):
                x, y = a[i], a[j]
                cs[x].add(y)
                cs[y].add(x)
    nb = [sorted(s) for s in cs]
    if n0 <= 60:
        deadline = min(deadline, time.monotonic() + 2.0)
    S = _independent_set(n0, nb, rng, nprng, deadline)
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------
# NEW ROUTE: bipartite Cayley lifts over a group, found by annealing.
#
# Base graph: two vertices A, B joined by d parallel darts with distinct
# voltages S (a subset of the group). The lift has vertices A_x, B_y (2|G|
# total), with A_x ~ B_{x*g} for g in S. Every vertex has degree d. Left
# multiplication is an automorphism, so the diameter is at most 4 iff the
# balls of radius 4 around A_e and B_e cover the graph.
# ----------------------------------------------------------------------------

def _table(m, k, r):
    """Multiplication and inverse tables for the group Z_m x| Z_k."""
    order, mul, inv = lib.semidirect_group(m, k, r)
    mt = [[mul(x, y) for y in range(order)] for x in range(order)]
    it = [inv(x) for x in range(order)]
    return order, mt, it


def _bad(G, mt, S, invS):
    """Number of vertices not within distance 4 of A_e or of B_e."""
    total = 0
    for start in (0, G):
        seen = bytearray(2 * G)
        seen[start] = 1
        frontier = [start]
        for _ in range(4):
            nxt = []
            for v in frontier:
                if v < G:
                    row = mt[v]
                    for g in S:
                        w = G + row[g]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    row = mt[v - G]
                    for h in invS:
                        w = row[h]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            frontier = nxt
            if not frontier:
                break
        total += 2 * G - sum(seen)
    return total


def _anneal(G, mt, it, d, rng, iters, deadline):
    """Simulated annealing over d-element generating sets; returns S with zero bad count or None."""
    S = rng.sample(range(G), d)
    invS = [it[g] for g in S]
    cur = _bad(G, mt, S, invS)
    for step in range(iters):
        if cur == 0:
            return S
        if (step & 15) == 0 and time.monotonic() >= deadline:
            break
        i = rng.randrange(d)
        c = rng.randrange(G)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        inv2 = invS[:]
        inv2[i] = it[c]
        s2 = _bad(G, mt, S2, inv2)
        if s2 <= cur or rng.random() < 0.01:
            S, invS, cur = S2, inv2, s2
    return S if cur == 0 else None


def _group_candidates(G_lo, G_hi):
    """Semidirect parameters (m, k, r) with m*k in [G_lo, G_hi]."""
    out = []
    for G in range(G_lo, G_hi + 1):
        for k in range(1, 13):
            if G % k:
                continue
            m = G // k
            if k == 1:
                out.append((m, 1, 1))
                continue
            for r in range(1, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    out.append((m, k, r))
    return out


def _cayley_route(d, D, best_n, rng, deadline, consider):
    """Search for a bipartite Cayley lift with 2|G| > best_n and diameter <= 4."""
    moore = 2 * (1 + (d - 1) + (d - 1) ** 2 + (d - 1) ** 3)
    G_lo = best_n // 2 + 1
    G_hi = moore // 2
    if G_lo > G_hi or G_lo < d:
        return
    cands = _group_candidates(G_lo, G_hi)
    rng.shuffle(cands)
    for (m, k, r) in cands:
        if time.monotonic() >= deadline:
            break
        order, mt, it = _table(m, k, r)
        S = _anneal(order, mt, it, d, rng, 150, deadline)
        if S is None:
            continue
        n, e = lib.group_lift(2, [(0, 1, g) for g in S], order, lambda x, g: mt[x][g])
        if lib.is_valid(n, e, d, D):
            consider(n, e)
            return


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)
    nprng = np.random.default_rng(abs(int(seed)) % (2 ** 32))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    pg = _pg(d)
    if pg is not None:
        consider(pg[0], pg[1])

    # Blow-up route gets the first ~40% of the budget.
    blow_deadline = start + max(0.5, 0.4 * time_limit - 1.0)
    q = d - 2
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < blow_deadline - 2.0:
        if D >= 4:
            n0, e0 = _gq(q)
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
        else:
            n0, e0 = 0, []
        if n0 > 0:
            consider(n0, e0)
            res = _blowup(n0, e0, d, blow_deadline, rng, nprng)
            if res is not None:
                consider(res[0], res[1])

    # New Cayley-lift route for D = 4 gets the rest.
    cayley_deadline = start + max(0.5, 0.85 * time_limit - 3.0)
    if D == 4 and time.monotonic() < cayley_deadline - 1.0:
        try:
            _cayley_route(d, D, best_n, rng, cayley_deadline, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
