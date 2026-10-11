import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Group-based Haar graphs for D = 3.
#
# For a finite group G of order N and a set S of size d, the bipartite graph with
# parts A = G, B = G and edges a_g ~ b_{g s} (s in S) is d-regular on 2N vertices.
# Two A-vertices (or two B-vertices) share a neighbour iff every non-identity
# element of G is t s^{-1} for some s != t in S. Then mixed pairs are within
# distance 3 automatically, so diameter 3 holds exactly when S S^{-1} = G.
# |G| <= d(d-1)+1, so the cap is 2(d^2-d+1).
#
# Unlike the cyclic difference-cover search, we search over several groups of
# each order N, including non-abelian semidirect products Z_m x| Z_k. Each
# group is given by a multiplication table built with numpy.
# ----------------------------------------------------------------------------

def _group_tables(m, k, r):
    """Multiplication and inverse tables for Z_m x|_r Z_k (element a*k+b, identity 0)."""
    N = m * k
    P = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    els = np.arange(N, dtype=np.int64)
    a = els // k
    b = els % k
    A = a[:, None]
    B = b[:, None]
    C = a[None, :]
    E = b[None, :]
    M = ((A + P[B] * C) % m) * k + (B + E) % k
    nb = (-b) % k
    inv = ((-P[nb] * a) % m) * k + nb
    return N, M.tolist(), inv.tolist()


def _group_options(N, rng):
    """Cyclic group first, then a random sample of non-cyclic semidirect products of order N."""
    cyc, others = [], []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if k == 1:
            cyc.append((m, 1, 1))
            continue
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                others.append((m, k, r))
    rng.shuffle(others)
    return cyc + others[:5]


def _rem(x, others, cnt, mulT, invT):
    """Remove the quotient pairs involving x; return the change in number of uncovered elements."""
    dlt = 0
    mx = mulT[x]
    ix = invT[x]
    for s in others:
        g = mx[invT[s]]
        cnt[g] -= 1
        if cnt[g] == 0:
            dlt += 1
        g = mulT[s][ix]
        cnt[g] -= 1
        if cnt[g] == 0:
            dlt += 1
    return dlt


def _add(y, others, cnt, mulT, invT):
    """Add the quotient pairs involving y; return the change in number of uncovered elements."""
    dlt = 0
    my = mulT[y]
    iy = invT[y]
    for s in others:
        g = my[invT[s]]
        if cnt[g] == 0:
            dlt -= 1
        cnt[g] += 1
        g = mulT[s][iy]
        if cnt[g] == 0:
            dlt -= 1
        cnt[g] += 1
    return dlt


def _anneal(N, d, mulT, invT, rng, deadline):
    """Find S of size d in the group with S S^{-1} = G (every non-identity element covered)."""
    if d * (d - 1) < N - 1:
        return None
    S = rng.sample(range(N), d)
    inS = [False] * N
    for s in S:
        inS[s] = True
    cnt = [0] * N
    for a in S:
        for b in S:
            if a != b:
                cnt[mulT[a][invT[b]]] += 1
    unc = sum(1 for g in range(1, N) if cnt[g] == 0)
    it = 0
    while unc > 0:
        it += 1
        if (it & 127) == 0 and time.monotonic() > deadline:
            return None
        T = 0.1 + 0.5 * (1.0 - (it % 50000) / 50000.0)
        if rng.random() < 0.6:
            # Focused move: make a currently uncovered element g equal to y * s^{-1}.
            zeros = [g for g in range(1, N) if cnt[g] == 0]
            g = zeros[rng.randrange(len(zeros))]
            s = S[rng.randrange(d)]
            y = mulT[g][s]
            i = rng.randrange(d)
        else:
            i = rng.randrange(d)
            y = rng.randrange(N)
        if inS[y]:
            continue
        x = S[i]
        others = S[:i] + S[i + 1:]
        dlt = _rem(x, others, cnt, mulT, invT)
        dlt += _add(y, others, cnt, mulT, invT)
        if dlt <= 0 or rng.random() < math.exp(-dlt / T):
            S[i] = y
            inS[x] = False
            inS[y] = True
            unc += dlt
        else:
            _rem(y, others, cnt, mulT, invT)
            _add(x, others, cnt, mulT, invT)
    return sorted(S)


def _search_N(N, d, rng, deadline):
    """Try groups of order N in round-robin until one gives a covering S. Returns (mulT, S) or None."""
    opts = _group_options(N, rng)
    if not opts:
        return None
    tables = {}
    idx = 0
    while time.monotonic() < deadline:
        now = time.monotonic()
        chunk = max(2.0, (deadline - now) / len(opts))
        key = opts[idx % len(opts)]
        idx += 1
        if key not in tables:
            m, k, r = key
            _, mulT, invT = _group_tables(m, k, r)
            tables[key] = (mulT, invT)
        mulT, invT = tables[key]
        S = _anneal(N, d, mulT, invT, rng, min(deadline, now + chunk))
        if S is not None:
            return mulT, S
    return None


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4)
# ----------------------------------------------------------------------------

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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.7 * float(time_limit), 40.0)
    end = start + budget
    rng = random.Random(seed * 1000003 + 17 * d + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, list(E)

    if D >= 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Group-Haar search (diameter 3, also valid for D >= 3). Limited to moderate d
    # so that the group tables stay small.
    if d >= 2 and D >= 3 and d <= 25:
        hi = d * (d - 1) + 1
        lo = max(d, int(0.8 * hi))
        fails = 0
        for N in range(lo, hi + 1):
            now = time.monotonic()
            if now >= end:
                break
            slice_len = min(6.0, max(1.0, (end - now) / 3.0))
            res = _search_N(N, d, rng, min(end, now + slice_len))
            if res is None:
                fails += 1
                if fails >= 4:
                    break
                continue
            fails = 0
            mulT, S = res
            E = []
            for g in range(N):
                row = mulT[g]
                for s in S:
                    E.append((g, N + row[s]))
            consider(2 * N, E)

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
