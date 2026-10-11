import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured baselines.
# ----------------------------------------------------------------------------

def _kdd(d):
    """K_{d,d}: diameter 2, degree d. Valid for every D >= 2 and is the safe fallback."""
    return lib.haar_graph(d, range(d))


def _d3(d):
    """Diameter-3 baselines: PG(2,q) incidence, or Araujo-Pardo & Lopez when d-2 is a prime power."""
    if d - 1 >= 2 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            n, e = lib.araujo_lopez_graph(q)
            if lib.is_valid(n, e, d, 3):
                return n, e
        except Exception:
            pass
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New search family: multi-base voltage lifts over semidirect products
# Z_m x|_r Z_k, with k base vertices per side and d perfect-matching layers.
#
# The lift has 2*k*G vertices. Left translation is an automorphism, so the
# diameter condition only needs eccentricities from the 2k base representatives.
# Cost = total number of unreached (representative, vertex) pairs; 0 means valid.
# Moves: change one voltage, or swap two endpoints inside one layer (keeps regularity).
# ----------------------------------------------------------------------------

ITERS = 2500
N_SLACK_DIV = 15


def _groups(G):
    """Semidirect parameters (m, k, r) with m*k = G, giving Z_m x|_r Z_k. Always non-empty (r=1, k=1)."""
    out = []
    for k in range(1, G + 1):
        if G % k:
            continue
        m = G // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _rperm(mul, G, g):
    """Permutation x -> x*g of the group (right multiplication)."""
    return [mul(x, g) for x in range(G)]


def _build_adj(k, G, darts, perms):
    """Adjacency lists of the lift. A-vertex (i, x) = i*G + x; B-vertex (j, y) = (k+j)*G + y."""
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _), pm in zip(darts, perms):
        ab = i * G
        bb = (k + j) * G
        for x in range(G):
            a = ab + x
            b = bb + pm[x]
            adj[a].append(b)
            adj[b].append(a)
    return adj


def _cost(k, G, D, adj):
    """Unreached (representative, vertex) pairs from the 2k base representatives. Zero iff diameter <= D."""
    N = 2 * k * G
    total = 0
    for v in range(2 * k):
        src = v * G  # group identity is code 0
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for w in adj[u]:
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += N - cnt
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _), pm in zip(darts, perms):
        for x in range(G):
            E.add((i * G + x, (k + j) * G + pm[x]))
    return 2 * k * G, sorted(E)


def _anneal(k, G, mul, d, D, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer endpoint permutations."""
    darts = []  # darts[L*k + i] = [i, endpoint j, voltage g]
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_rperm(mul, G, g) for _, _, g in darts]
    cost = _cost(k, G, D, _build_adj(k, G, darts, perms))

    T0, T1 = 3.0, 0.05
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)

        if k == 1 or rng.random() < 0.6:
            idx = rng.randrange(len(darts))
            new_g = rng.randrange(G)
            old_g = darts[idx][2]
            if new_g == old_g:
                continue
            old_pm = perms[idx]
            darts[idx][2] = new_g
            perms[idx] = _rperm(mul, G, new_g)
            c2 = _cost(k, G, D, _build_adj(k, G, darts, perms))
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old_g
                perms[idx] = old_pm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, _build_adj(k, G, darts, perms))
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
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

    if d < 1:
        return 1, []
    if D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback, valid for every D >= 2.
    best = _kdd(d)
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _d3(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: multi-base lifts over semidirect products, aiming just above the current order.
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        ks = [k for k in (1, 2, 3, 4) if 2 * k * (n_best // (2 * k) + 1) <= moore]
        if not ks:
            break
        k = rng.choice(ks)
        lo = n_best // (2 * k) + 1
        G = lo + rng.randrange(max(2, lo // N_SLACK_DIV))
        m, k2, r = rng.choice(_groups(G))
        order, mul, _ = lib.semidirect_group(m, k2, r)
        res = _anneal(k, order, mul, d, D, rng, deadline, ITERS)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = _kdd(d)
    return best
