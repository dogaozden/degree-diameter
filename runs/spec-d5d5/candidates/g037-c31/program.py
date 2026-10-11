import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Tunables.
# ----------------------------------------------------------------------------

MAX_GROUPS = 10        # groups tried per order N in one bi-Cayley attempt
CLIMB_ITERS = 2000     # hill-climb steps per group
STALL_LIMIT = 400      # re-randomize the connection set after this many non-improving steps
ANNEAL_ITERS = 500     # annealing steps for multi-base lifts
N_WINDOW = 10          # bi-Cayley orders tried in a window just above the current record
MULTI_PROB = 0.2       # fraction of the search spent on multi-base lifts
_BIG = 10 ** 9
_TCACHE = {}


# ----------------------------------------------------------------------------
# Structured baselines (D = 3 and D = 4).
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 7 for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Group tables, vectorised. Elements of Z_m x|_r Z_k are coded a*k+b, matching
# lib.semidirect_group. TA[x, g] = x*g and invs[g] = g^-1.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _table(m, k, r):
    """Cached (G, TA, invs) for Z_m x|_r Z_k."""
    key = (m, k, r)
    hit = _TCACHE.get(key)
    if hit is not None:
        return hit
    G = m * k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    x = np.arange(G, dtype=np.int64)
    a, b = x // k, x % k
    A, B = a[:, None], b[:, None]
    C, E = a[None, :], b[None, :]
    TA = np.ascontiguousarray(((A + pw[B] * C) % m) * k + (B + E) % k, dtype=np.int64)
    invs = np.argmax(TA == 0, axis=1).astype(np.int64)
    val = (G, TA, invs)
    if len(_TCACHE) >= 64:
        _TCACHE.clear()
    _TCACHE[key] = val
    return val


def _unreached(G, TA, invs, S, D):
    """Number of (source, vertex) pairs not within distance D, for sources A_0 and B_0.

    Bi-Cayley graph: A_x ~ B_{x g} for g in S. Left multiplication is an automorphism,
    so checking eccentricities of A_0 and B_0 covers every pair.
    """
    S = np.asarray(S, dtype=np.int64)
    TS = TA[:, S]               # TS[x]  = B-neighbours of A_x
    TSi = TA[:, invs[S]]        # TSi[y] = A-neighbours of B_y
    total = 0
    for src_side in (0, 1):
        seen = [np.zeros(G, dtype=bool), np.zeros(G, dtype=bool)]
        seen[src_side][0] = True
        side = src_side
        frontier = np.zeros(1, dtype=np.int64)
        count = 1
        for _ in range(D):
            tgt = (TS if side == 0 else TSi)[frontier]
            tside = 1 - side
            mask = np.zeros(G, dtype=bool)
            mask[tgt.ravel()] = True
            mask &= ~seen[tside]
            seen[tside] |= mask
            frontier = np.flatnonzero(mask)
            count += frontier.size
            side = tside
            if frontier.size == 0:
                break
        total += 2 * G - count
    return total


def _climb(G, TA, invs, d, D, rng, iters, deadline):
    """Hill-climb S = {0, s_1, ..., s_{d-1}} to zero unreached pairs, with sideways moves
    and re-randomization after a long stall."""

    def fresh():
        S = [0] + rng.sample(range(1, G), d - 1)
        return S, _unreached(G, TA, invs, S, D)

    S, cur = fresh()
    stall = 0
    for it in range(iters):
        if cur == 0:
            break
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, G)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(G, TA, invs, S2, D)
        stall = 0 if v < cur else stall + 1
        if v <= cur:
            S, cur = S2, v
        if stall > STALL_LIMIT:
            S, cur = fresh()
            stall = 0
    return S if cur == 0 else None


def _search_bicayley(d, D, N, rng, deadline):
    """Try several groups of order N; return (TA, S) for the first valid bi-Cayley lift."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        G, TA, invs = _table(m, k, r)
        S = _climb(G, TA, invs, d, D, rng, CLIMB_ITERS, deadline)
        if S is not None:
            return TA, S
    return None


# ----------------------------------------------------------------------------
# Multi-base voltage lifts over semidirect products, annealed.
# ----------------------------------------------------------------------------

def _cost(k, G, D, darts, perms):
    """Pairs (representative, vertex) not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, TA, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer base assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [TA[:, s].tolist() for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = TA[:, new_s].tolist()
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


def _multi_try(d, D, lo, moore, rng, deadline):
    """Multi-base lift with k base vertices per side and total order above 2*(lo-1)."""
    k = rng.choice((2, 3))
    G = -(-lo // k) + rng.randrange(3)
    if G < 2 or 2 * k * G > moore:
        return None
    m, k2, r = rng.choice(_groups(G))
    Gc, TA, _ = _table(m, k2, r)
    return _anneal(d, D, k, Gc, TA, rng, deadline, ANNEAL_ITERS)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and meets the Moore bound for D = 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    elif D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
    if best[0] >= moore:
        return best

    # Main search: bi-Cayley lifts just above the current record, plus multi-base lifts.
    Nhalf = moore // 2
    while time.monotonic() < deadline and best[0] < moore:
        lo = best[0] // 2 + 1
        if lo > Nhalf:
            break
        if rng.random() >= MULTI_PROB:
            # Bias toward the smallest orders above the record.
            N = min(Nhalf, lo + int(N_WINDOW * rng.random() ** 2))
            res = _search_bicayley(d, D, N, rng, deadline)
            if res is not None:
                TA, S = res
                edges = [(x, N + int(TA[x, g])) for x in range(N) for g in S]
                consider(2 * N, edges)
        else:
            res = _multi_try(d, D, lo, moore, rng, deadline)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
