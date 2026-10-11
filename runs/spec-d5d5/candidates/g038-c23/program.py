import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Group catalogue: semidirect products Z_m x|_r Z_k and matrix groups
# SL(2,p), PGL(2,p), PSL(2,p) over prime fields. Each group is given as a
# multiplication table T (T[x][y] = x*y) with identity index e.
# ----------------------------------------------------------------------------

CLIMB_ITERS = 200
RESTARTS = 2
ANNEAL_ITERS = 250
MAX_GROUPS = 4
BIG = 10 ** 9

MAT_KEYS = [(p, kind) for p in (3, 5, 7) for kind in ("SL", "PGL", "PSL")]
# (group, share of the budget for the bi-Cayley attempt on that group)
SPECIALS = [((7, "PSL"), 0.30), ((7, "PGL"), 0.25), ((7, "SL"), 0.15),
            ((5, "PGL"), 0.05), ((5, "SL"), 0.05)]

_TABLES = {}


def _mat_order(p, kind):
    base = p * (p * p - 1)
    return base // 2 if kind == "PSL" else base


MAT_ORDERS = sorted({_mat_order(p, k) for p, k in MAT_KEYS})


def _mat_canon(M, p, kind):
    a, b, c, d = M
    if kind == "PGL":
        return min(((lam * a) % p, (lam * b) % p, (lam * c) % p, (lam * d) % p)
                   for lam in range(1, p))
    if kind == "PSL":
        return min(M, ((-a) % p, (-b) % p, (-c) % p, (-d) % p))
    return M


def _mat_build(p, kind):
    elems = set()
    for M in itertools.product(range(p), repeat=4):
        a, b, c, d = M
        det = (a * d - b * c) % p
        if kind in ("SL", "PSL"):
            if det != 1:
                continue
        elif det == 0:
            continue
        elems.add(_mat_canon(M, p, kind))
    elems = sorted(elems)
    index = {M: i for i, M in enumerate(elems)}
    G = len(elems)

    def mul(X, Y):
        a, b, c, d = X
        e, f, g, h = Y
        return _mat_canon(((a * e + b * g) % p, (a * f + b * h) % p,
                           (c * e + d * g) % p, (c * f + d * h) % p), p, kind)

    T = [[index[mul(X, Y)] for Y in elems] for X in elems]
    e = index[_mat_canon((1, 0, 0, 1), p, kind)]
    return G, T, e


def _table(key):
    hit = _TABLES.get(key)
    if hit is not None:
        return hit
    if key[0] == "mat":
        G, T, e = _mat_build(key[1], key[2])
    else:
        _, m, k, r = key
        G, mul, _inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, y) for y in range(G)] for x in range(G)]
        e = 0
    if len(_TABLES) >= 12:
        _TABLES.clear()
    val = (G, T, e)
    _TABLES[key] = val
    return val


def _catalog(N, rng, cap):
    """Candidate group keys of order N: matrix groups first, then shuffled semidirect products."""
    keys = [("mat", p, kind) for p, kind in MAT_KEYS if _mat_order(p, kind) == N]
    semi = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                semi.append(("semi", m, k, r))
    rng.shuffle(semi)
    return keys + semi[:cap]


# ----------------------------------------------------------------------------
# Bi-Cayley graphs: A_x ~ B_{x g} for g in S, |S| = d, so the graph is d-regular
# on 2G vertices. Left translation is an automorphism, so only the
# eccentricities of A_e and B_e need checking.
# ----------------------------------------------------------------------------

def _unreached(N, T, invs, e, S, D):
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (e, N + e):
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
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += 2 * N - count
    return total


def _climb(N, T, invs, e, d, D, rng, iters, deadline, restarts):
    """Hill-climb a connection set S containing the identity (WLOG) to zero unreached pairs."""
    if N < d:
        return None
    for _ in range(restarts):
        if time.monotonic() > deadline:
            return None
        S = [e]
        while len(S) < d:
            c = rng.randrange(N)
            if c not in S:
                S.append(c)
        cur = _unreached(N, T, invs, e, S, D)
        for _ in range(iters):
            if cur == 0 or time.monotonic() > deadline:
                break
            i = rng.randrange(1, d)
            c = rng.randrange(N)
            if c in S:
                continue
            S2 = S[:]
            S2[i] = c
            v = _unreached(N, T, invs, e, S2, D)
            if v <= cur:
                S, cur = S2, v
        if cur == 0:
            return S
    return None


def _try_bicayley(key, d, D, rng, deadline, iters, restarts):
    G, T, e = _table(key)
    invs = [row.index(e) for row in T]
    S = _climb(G, T, invs, e, d, D, rng, iters, deadline, restarts)
    if S is None:
        return None
    return 2 * G, [(x, G + T[x][g]) for x in range(G) for g in S]


# ----------------------------------------------------------------------------
# Two-base voltage lifts over a group, annealed.
# Dart (i, j, s): A_{i,g} ~ B_{j, g*s}. Left translation is an automorphism,
# so one representative per base vertex suffices.
# ----------------------------------------------------------------------------

def _multi_cost(k, G, T, D, darts):
    if len({tuple(x) for x in darts}) < len(darts):
        return BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + T[g][s]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    for src in [i * G for i in range(k)] + [(k + j) * G for j in range(k)]:
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
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
    return total


def _anneal(d, D, k, G, T, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    cost = _multi_cost(k, G, T, D, darts)
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.2, (2.0 + 0.05 * min(cost, 10 ** 6)) * (1.0 - it / iters))
        if rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _multi_cost(k, G, T, D, darts)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _multi_cost(k, G, T, D, darts)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    return darts if cost == 0 else None


def _multi_edges(k, G, T, darts):
    E = set()
    for i, j, s in darts:
        for g in range(G):
            E.add((i * G + g, (k + j) * G + T[g][s]))
    return 2 * k * G, sorted(E)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)
    if best[0] >= moore:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        q = next((x for x in range(d - 1, 1, -1) if lib.is_prime_power(x)), None)
        if q is not None:
            consider(*lib.projective_plane_incidence(q))
        if best[0] >= moore:
            return best

    try:
        # Phase 1: special matrix groups (non-abelian, bold family).
        for (p, kind), frac in SPECIALS:
            if time.monotonic() >= deadline:
                break
            G = _mat_order(p, kind)
            if G < d or 2 * G <= best[0] or 2 * G > moore:
                continue
            dl = min(deadline, time.monotonic() + frac * budget)
            res = _try_bicayley(("mat", p, kind), d, D, rng, dl,
                                CLIMB_ITERS * 4, RESTARTS + 2)
            if res is not None:
                consider(*res)

        # Phase 2: sweep bi-Cayley orders upward; interleave two-base lifts.
        sweep = 0
        bi_ok = True
        multi_ok = True
        while best[0] < moore and time.monotonic() < deadline and (bi_ok or multi_ok):
            use_bi = bi_ok and (not multi_ok or rng.random() < 0.6)
            if use_bi:
                lo = best[0] // 2 + 1
                if sweep < lo:
                    sweep = lo
                if sweep > moore // 2:
                    bi_ok = False
                    continue
                N = sweep
                sweep += 1
                if N < d:
                    continue
                for key in _catalog(N, rng, MAX_GROUPS):
                    if time.monotonic() >= deadline:
                        break
                    res = _try_bicayley(key, d, D, rng, deadline,
                                        CLIMB_ITERS, RESTARTS)
                    if res is not None:
                        consider(*res)
                        break
            else:
                k = 2
                lo = best[0] // (2 * k) // 2 + 1
                hi = moore // (2 * k)
                if lo > hi:
                    multi_ok = False
                    continue
                mats = [o for o in MAT_ORDERS if lo <= o <= hi]
                if mats and rng.random() < 0.3:
                    G = rng.choice(mats)
                else:
                    G = lo + rng.randrange(min(10, hi - lo + 1))
                for key in _catalog(G, rng, 3):
                    if time.monotonic() >= deadline:
                        break
                    Gg, T, _e = _table(key)
                    darts = _anneal(d, D, k, Gg, T, rng, deadline, ANNEAL_ITERS)
                    if darts is not None:
                        n, E = _multi_edges(k, Gg, T, darts)
                        consider(n, E)
                        break
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
