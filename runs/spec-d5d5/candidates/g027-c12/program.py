import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Tunables. Bi-Cayley search over semidirect products Z_m x|_r Z_k, with a
# vectorised numpy distance check. A secondary multi-base annealed lift is
# mixed in for diversity.
# ----------------------------------------------------------------------------

MAX_GROUPS = 6        # groups tried per order N
CLIMB_ITERS = 4000    # hill-climb steps per restart
STALL_LIMIT = 500     # re-randomise after this many non-improving steps
ANNEAL_ITERS = 600    # annealing steps for multi-base lifts
N_WINDOW = 8          # candidate orders just above the current lower bound
ANNEAL_PROB = 0.2     # fraction of rounds spent on multi-base annealing
_BIG = 10 ** 9
_CACHE = {}


def _safe(fn, *args):
    """Call fn; return None on any exception (fallbacks must never crash)."""
    try:
        return fn(*args)
    except Exception:
        return None


# ----------------------------------------------------------------------------
# Structured baselines for D = 3 and D = 4.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez graph of degree d = q + 2, diameter 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 7."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products.
# Vertices A_x and B_x for x in G (|G| = N); A_x ~ B_{x g} for g in S.
# Left translation is an automorphism preserving both sides, so checking
# eccentricity from A_e and B_e certifies the whole graph.
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


def _tables(m, k, r):
    """Cached (Tn, invs): Tn[x, g] = x*g as an int64 array, invs[g] = g^-1."""
    key = (m, k, r)
    hit = _CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    Tn = np.array([[mul(x, g) for g in range(order)] for x in range(order)],
                  dtype=np.int64)
    invs = np.array([inv(g) for g in range(order)], dtype=np.int64)
    val = (Tn, invs)
    if len(_CACHE) >= 64:
        _CACHE.clear()
    _CACHE[key] = val
    return val


def _unreached(Tn, invs, S, D):
    """Number of (source, target) pairs at distance > D from A_e and B_e, summed over both sources."""
    N = Tn.shape[0]
    S = np.asarray(S, dtype=np.int64)
    sub = Tn[:, S]            # sub[x, i] = x * S[i]: A -> B
    subinv = Tn[:, invs[S]]   # subinv[y, i] = y * S[i]^-1: B -> A
    total = 0
    for side in (0, 1):
        seenA = np.zeros(N, dtype=bool)
        seenB = np.zeros(N, dtype=bool)
        if side == 0:
            seenA[0] = True
            fA = np.array([0], dtype=np.int64)
            fB = np.zeros(0, dtype=np.int64)
        else:
            seenB[0] = True
            fB = np.array([0], dtype=np.int64)
            fA = np.zeros(0, dtype=np.int64)
        for _ in range(D):
            nB = np.zeros(N, dtype=bool)
            if fA.size:
                nB[sub[fA].ravel()] = True
            nB &= ~seenB
            nA = np.zeros(N, dtype=bool)
            if fB.size:
                nA[subinv[fB].ravel()] = True
            nA &= ~seenA
            seenB |= nB
            seenA |= nA
            fA = np.flatnonzero(nA)
            fB = np.flatnonzero(nB)
            if fA.size == 0 and fB.size == 0:
                break
        total += 2 * N - int(seenA.sum()) - int(seenB.sum())
    return total


def _climb(N, Tn, invs, d, D, rng, iters, stall_limit, deadline):
    """Hill-climb a connection set S (identity fixed in S, WLOG) to zero unreached pairs."""
    def fresh():
        S = [0] + rng.sample(range(1, N), d - 1)
        return S, _unreached(Tn, invs, S, D)

    S, cur = fresh()
    stall = 0
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(Tn, invs, S2, D)
        if v < cur:
            stall = 0
        else:
            stall += 1
        if v <= cur:
            S, cur = S2, v
        if stall > stall_limit:
            S, cur = fresh()
            stall = 0
    return S if cur == 0 else None


def _search_bicayley(d, D, N, rng, deadline):
    """Try several groups of order N; return (Tn, S) for the first valid lift, else None."""
    if N < d + 1:
        return None
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        Tn, invs = _tables(m, k, r)
        S = _climb(N, Tn, invs, d, D, rng, CLIMB_ITERS, STALL_LIMIT, deadline)
        if S is not None:
            return Tn, S
    return None


# ----------------------------------------------------------------------------
# Multi-base voltage lifts over semidirect products, annealed.
# ----------------------------------------------------------------------------

def _right_perm(mul, G, s):
    """Permutation g -> g*s of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within D. Zero means valid."""
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


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
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
            perms[idx] = _right_perm(mul, G, new_s)
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

    # Safe fallback: K_{d,d} has diameter 2 (and is valid for every d >= 1).
    best = lib.haar_graph(d, range(d))
    if D == 2 or d == 1:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Structured baselines (each is validated before use).
    if D >= 3:
        for cand in (_safe(_best_pg, d), _safe(_araujo, d)):
            if cand is not None:
                consider(*cand)
    if D >= 4:
        cand = _safe(_best_gq, d)
        if cand is not None:
            consider(*cand)

    # Main search: aim above the current best order.
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        lo = n_best // 2 + 1
        if lo > moore // 2:
            break

        if rng.random() >= ANNEAL_PROB:
            # Bi-Cayley lift on a group of order N; the lift has 2N vertices.
            N = lo + rng.randrange(N_WINDOW)
            res = _search_bicayley(d, D, N, rng, deadline)
            if res is not None:
                Tn, S = res
                sub = Tn[:, np.array(S, dtype=np.int64)]
                edges = [(x, N + int(sub[x, i]))
                         for x in range(N) for i in range(len(S))]
                consider(2 * N, edges)
        else:
            # Multi-base lift with k base vertices per side over a group of order G.
            k = rng.choice((2, 3))
            lo_k = n_best // (2 * k) + 1
            if 2 * k * lo_k > moore:
                continue
            G = lo_k + rng.randrange(max(2, lo_k // 10))
            if G < 2:
                continue
            m, k2, r = rng.choice(_groups(G))
            order, mul, _ = lib.semidirect_group(m, k2, r)
            res = _anneal(d, D, k, order, mul, rng, deadline, ANNEAL_ITERS)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
