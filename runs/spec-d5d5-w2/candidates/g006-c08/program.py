import itertools
import math
import random
import time

import lib

MAX_GROUPS = 12        # groups tried per order within one attempt
BC_ITERS = 600         # annealing steps per (group, connection set) try
ML_ITERS = 800         # annealing steps for multi-base lifts
T_HOT = 1.5            # initial annealing temperature (unreached-pair units)
T_COLD = 0.15          # final annealing temperature
P_BICAYLEY = 0.7       # probability of a bi-Cayley attempt (else multi-base)
_BIG = 10 ** 9
_TABLE_CACHE = {}
_GROUPS_CACHE = {}


# ----------------------------------------------------------------------------
# Structured baselines.
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


# ----------------------------------------------------------------------------
# Group helpers.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k (cached)."""
    hit = _GROUPS_CACHE.get(N)
    if hit is not None:
        return list(hit)
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    if len(_GROUPS_CACHE) >= 256:
        _GROUPS_CACHE.clear()
    _GROUPS_CACHE[N] = tuple(out)
    return out


def _tables(m, k, r):
    """Cached (order, T, invs) with T[x][g] = x*g and invs[g] = g^-1."""
    key = (m, k, r)
    hit = _TABLE_CACHE.get(key)
    if hit is not None:
        return hit
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    val = (order, T, invs)
    if len(_TABLE_CACHE) >= 64:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = val
    return val


# ----------------------------------------------------------------------------
# Bi-Cayley search: A_x ~ B_{x s} for s in S, |S| = d, group of order N.
# Left multiplication is an automorphism, so eccentricities from A_0 and B_0
# decide the diameter. Identity is WLOG in S.
# ----------------------------------------------------------------------------

def _unreached(N, T, invs, S, D):
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


def _anneal_bc(N, T, invs, d, D, rng, iters, deadline):
    """Annealing over S = {0, s_1, ..., s_{d-1}} to zero unreached pairs; S or None."""
    if N < d:
        return None
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _attempt_bc(N, d, D, rng, deadline):
    """Try groups of order N until one gives a connection set of diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, T, invs = _tables(m, k, r)
        S = _anneal_bc(N, T, invs, d, D, rng, BC_ITERS, deadline)
        if S is not None:
            return T, S
    return None


# ----------------------------------------------------------------------------
# Multi-base voltage lifts with k base vertices per side over a group of order G.
# Dart (i, j, s): A_{i,g} ~ B_{j, g s}. Each layer is preserved by left mult.
# ----------------------------------------------------------------------------

def _cost_ml(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges_ml(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal_ml(k, G, T, d, D, rng, iters, deadline):
    """Annealing over voltages and per-layer B-assignments; returns (n, edges) or None."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [[T[g][s] for g in range(G)] for _, _, s in darts]
    cost = _cost_ml(k, G, D, darts, perms)

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
    T_end = 0.3
    temp = T0
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0

    for it in range(iters):
        if cost == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        temp = max(T_end, temp * decay)
        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_p = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = [T[g][new_s] for g in range(G)]
            c2 = _cost_ml(k, G, D, darts, perms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_p
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost_ml(k, G, D, darts, perms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges_ml(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.87 * time_limit, time_limit - 4.0))
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))  # K_{d,d}, meets the Moore bound 2d

    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    moore = lib.moore_bound(d, D)

    # Exact record family for D = 3: projective plane of order d-1.
    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best

    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break
    if D >= 4:
        for q in range(min(d - 1, 5), 1, -1):
            if lib.is_prime_power(q):
                consider(*_gq_w(q))
                break

    if best_n >= moore:
        return best

    Nmax = moore // 2
    bestN = max(best_n // 2, int(0.4 * Nmax))
    tried = {}

    while time.monotonic() < deadline:
        lo = bestN + 1
        if lo > Nmax:
            break

        if rng.random() < P_BICAYLEY:
            W = max(3, lo // 25)
            hi = min(Nmax, lo + W - 1)
            N = min(range(lo, hi + 1),
                    key=lambda x: (tried.get(x, 0), rng.random()))
            tried[N] = tried.get(N, 0) + 1
            att_budget = min(6.0, 0.6 * (1.0 + 0.5 * tried[N]))
            att_deadline = min(deadline, time.monotonic() + att_budget)
            res = _attempt_bc(N, d, D, rng, att_deadline)
            if res is not None:
                T, S = res
                edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                consider(2 * N, edges)
                bestN = max(bestN, best_n // 2)
        else:
            k = rng.choice((2, 3))
            loG = best_n // (2 * k) + 1
            G = loG + rng.randrange(max(2, loG // 25))
            if 2 * k * G > moore:
                continue
            m, kk, r = rng.choice(_groups(G))
            _, T, _ = _tables(m, kk, r)
            att_deadline = min(deadline, time.monotonic() + 2.0)
            res = _anneal_ml(k, G, T, d, D, rng, ML_ITERS, att_deadline)
            if res is not None:
                consider(res[0], res[1])
                bestN = max(bestN, best_n // 2)

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
