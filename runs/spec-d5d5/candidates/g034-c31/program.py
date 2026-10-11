import itertools
import math
import random
import time

import numpy as np

import lib

# ----------------------------------------------------------------------------
# Tuning constants.
# ----------------------------------------------------------------------------
ITERS = 600               # bi-Cayley annealing steps (parent-style fallback phase)
T_HOT = 1.5               # initial annealing temperature (unreached-pair units)
T_COLD = 0.15             # final annealing temperature
MAX_GROUPS_PER_ATTEMPT = 12

LIFT_ITERS = 2500         # annealing steps per voltage-lift attempt
LIFT_BMAX = 6             # max base vertices per side in a voltage lift
LIFT_ATTEMPT_SECONDS = 3.0
GROUPS_PER_N = 8
PHASE1_FRACTION = 0.3     # share of the budget for the bi-Cayley fallback phase

# ----------------------------------------------------------------------------
# Baseline families (fast, validated before use).
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Group tables. Groups are Z_m x|_r Z_kk, element (a, b) coded as a*kk + b.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, kk, r) with m*kk = N, giving Z_m x|_r Z_kk."""
    out = []
    for kk in range(1, N + 1):
        if N % kk:
            continue
        m = N // kk
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, kk, m) == 1 % m:
                out.append((m, kk, r))
    return out


_TABLE_CACHE = {}


def _tables(m, kk, r):
    """Vectorised multiplication and inverse tables for Z_m x|_r Z_kk (matches lib.semidirect_group)."""
    key = (m, kk, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    N = m * kk
    X = np.arange(N, dtype=np.int64)
    a, b = X // kk, X % kk
    pw = np.array([pow(r, e, m) for e in range(kk)], dtype=np.int64)
    MUL = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * kk + (b[:, None] + b[None, :]) % kk
    nb_ = (-b) % kk
    INV = ((-pw[nb_] * a) % m) * kk + nb_
    if len(_TABLE_CACHE) > 300:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = (MUL, INV)
    return MUL, INV


# ----------------------------------------------------------------------------
# Phase 1 (fallback): parent-style bi-Cayley search, which reached the record.
# ----------------------------------------------------------------------------

def _bc_unreached(N, T, invs, S, D):
    """Count (source, vertex) pairs not within distance D, for sources A_0 and B_0."""
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _bc_anneal(N, T, invs, d, D, rng, iters, deadline):
    """Simulated annealing over S = {0, s_1, ..., s_{d-1}} to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _bc_unreached(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _bc_unreached(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _bc_attempt(N, d, D, rng, deadline):
    """Try groups of order N until one yields a connection set with diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, kk, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, kk, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        S = _bc_anneal(N, T, invs, d, D, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


def _bicayley_phase(d, D, rng, deadline, consider):
    """Parent-style search for bi-Cayley graphs (2N vertices), largest N first."""
    Nmax = lib._moore_bound(d, D) // 2
    top = min(Nmax, Nmax // 2 + 6)
    cands = set(range(d + 1, top + 1))
    budget = 0.4
    while time.monotonic() < deadline and cands:
        success = False
        for N in sorted(cands, reverse=True):
            now = time.monotonic()
            if now >= deadline:
                break
            res = _bc_attempt(N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            T, S = res
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            consider(2 * N, edges)
            cands = {M for M in cands if M > N}
            if N + 1 <= Nmax:
                cands.add(N + 1)
            success = True
            break
        if not success:
            budget *= 2


# ----------------------------------------------------------------------------
# Phase 2 (bold change): voltage lifts of a random d-regular bipartite base
# multigraph with b vertices per side, voltages in a (possibly non-cyclic) group.
#
# Vertices: A_{i,x} = i*N + x, B_{j,y} = b*N + j*N + y.
# Layer t joins A_{i,x} to B_{sig[t,i], x*G[t,i]}. Each side is a union of
# b fibres of size N, each vertex has exactly d neighbours (one per layer).
# Left multiplication by the group is an automorphism, so eccentricities are
# constant on fibres and the diameter check only needs the 2b identity vertices.
# Duplicate neighbours only lower degree, so they are harmless for validity.
# ----------------------------------------------------------------------------

def _nb_from(sig, G, b, N, MUL, INV):
    """Neighbour array (2bN, d) of the lift defined by permutations sig and voltages G (both d x b)."""
    isig = np.argsort(sig, axis=1)                       # isig[t, j] = i with sig[t, i] = j
    Mg = MUL[:, G]                                       # Mg[x, t, i] = x * G[t, i]
    A_part = b * N + sig.T[:, None, :] * N + Mg.transpose(2, 0, 1)   # (b, N, d)
    INVG = INV[G]                                        # (d, b)
    gB = np.take_along_axis(INVG, isig, axis=1)          # gB[t, j] = G[t, isig[t, j]]^{-1}
    Mb = MUL[:, gB]                                      # Mb[y, t, j] = y * gB[t, j]
    B_part = isig.T[:, None, :] * N + Mb.transpose(2, 0, 1)          # (b, N, d)
    d = sig.shape[0]
    return np.concatenate([A_part.reshape(b * N, d), B_part.reshape(b * N, d)])


def _unreached_lift(nb, b, N, D):
    """Count (source, vertex) pairs at distance > D, over the 2b identity vertices of the fibres."""
    V = nb.shape[0]
    srcs = np.array([i * N for i in range(b)] + [b * N + j * N for j in range(b)], dtype=np.int64)
    S = len(srcs)
    R = np.zeros((S, V), dtype=bool)
    R[np.arange(S), srcs] = True
    for _ in range(D):
        R = R | R[:, nb].any(axis=2)
    return int(V * S - R.sum())


def _anneal_lift(b, N, MUL, INV, d, D, rng, deadline):
    """Anneal layer permutations and voltages until the lift has diameter <= D."""
    sig = np.zeros((d, b), dtype=np.int64)
    for t in range(d):
        sig[t] = rng.sample(range(b), b)
    G = np.array([[rng.randrange(N) for _ in range(b)] for _ in range(d)], dtype=np.int64)
    nb = _nb_from(sig, G, b, N, MUL, INV)
    cur = _unreached_lift(nb, b, N, D)
    for it in range(LIFT_ITERS):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / LIFT_ITERS)
        if b > 1 and rng.random() < 0.25:
            t = rng.randrange(d)
            i1, i2 = rng.sample(range(b), 2)
            sig2 = sig.copy()
            sig2[t, i1], sig2[t, i2] = sig[t, i2], sig[t, i1]
            G2 = G
        else:
            t = rng.randrange(d)
            i = rng.randrange(b)
            sig2 = sig
            G2 = G.copy()
            G2[t, i] = rng.randrange(N)
        nb2 = _nb_from(sig2, G2, b, N, MUL, INV)
        v = _unreached_lift(nb2, b, N, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            sig, G, nb, cur = sig2, G2, nb2, v
    if cur == 0:
        return nb
    return None


def _lift_edges(nb, b, N):
    """Return (n, edges) of the simple graph underlying the lift; A-side vertices come first."""
    edges = set()
    for u in range(b * N):
        for v in set(nb[u].tolist()):
            edges.add((u, v))
    return 2 * b * N, sorted(edges)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(0.2, min(0.8 * time_limit, time_limit - 8.0))
    deadline = start + total
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

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    # Cheap baselines.
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

    M = lib._moore_bound(d, D)

    # Phase 1: safe fallback that already reproduces the bi-Cayley record family.
    _bicayley_phase(d, D, rng, start + PHASE1_FRACTION * total, consider)

    # Phase 2: voltage lifts over small non-cyclic groups with b base vertices per side.
    failures = 0
    while time.monotonic() < deadline and best_n < M:
        if rng.random() < 0.8:
            b = rng.randint(2, LIFT_BMAX)
        else:
            b = 1
        nlo = best_n // (2 * b) + 1          # smallest N with 2*b*N > best_n
        nhi = M // (2 * b)                   # Moore bound
        if nlo > nhi:
            failures += 1
            if failures > 200:
                break
            continue
        N = rng.randint(nlo, min(nhi, nlo + 10))
        groups = _groups(N)
        if not groups:
            failures += 1
            continue
        rng.shuffle(groups)
        found = False
        for m, kk, r in groups[:GROUPS_PER_N]:
            now = time.monotonic()
            if now >= deadline:
                break
            MUL, INV = _tables(m, kk, r)
            nb = _anneal_lift(b, N, MUL, INV, d, D, rng,
                              min(deadline, now + LIFT_ATTEMPT_SECONDS))
            if nb is not None:
                n, e = _lift_edges(nb, b, N)
                consider(n, e)
                found = True
                break
        if not found:
            failures += 1

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
