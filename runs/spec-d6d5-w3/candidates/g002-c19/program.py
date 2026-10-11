import math
import random
import time

import numpy as np

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Small classical families (valid for D >= 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2, q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# NEW HELPER: frontier-matrix diameter oracle for bi-Cayley voltage lifts.
#
# A lift over a group H (order G) with k base vertices per side has vertices
# A_{i,g} and B_{j,h}. Dart t = (i_t, j_t, s_t) joins A_{i_t,g} to
# B_{j_t, g*s_t}. Left multiplication by H is an automorphism, so it suffices
# to BFS from one representative per block: A_{b,e} and B_{b,e}.
#
# Each BFS step is done for ALL darts at once with one fancy-index scatter:
# Ptab[t, g] = flat index of the B-neighbour of A_{i_t,g} along dart t, and
# Qtab[t, h] = flat index of the A-neighbour of B_{j_t,h} along dart t.
# This replaces a Python loop over darts and vertices in the parent's _cost.
# ----------------------------------------------------------------------------

def _right_table(mul, G):
    """RT[s, g] = g * s in the group."""
    RT = np.empty((G, G), dtype=np.int64)
    for s in range(G):
        RT[s] = [mul(g, s) for g in range(G)]
    return RT


def _cost(k, G, D, dI, dJ, Ptab, Qtab):
    """Total number of (representative, vertex) pairs at distance > D. Zero means diameter <= D."""
    N = 2 * k * G
    total = 0
    for side in (0, 1):
        for b in range(k):
            visA = np.zeros(k * G, dtype=bool)
            visB = np.zeros(k * G, dtype=bool)
            if side == 0:
                visA[b * G] = True
            else:
                visB[b * G] = True
            frA = visA.copy()
            frB = visB.copy()
            for _ in range(D):
                newB = np.zeros(k * G, dtype=bool)
                newB[Ptab[frA.reshape(k, G)[dI]]] = True
                newA = np.zeros(k * G, dtype=bool)
                newA[Qtab[frB.reshape(k, G)[dJ]]] = True
                newB &= ~visB
                newA &= ~visA
                visA |= newA
                visB |= newB
                frA, frB = newA, newB
                if not (frA.any() or frB.any()):
                    break
            total += N - int(visA.sum()) - int(visB.sum())
    return total


def _has_dup(dI, dJ, S):
    """True if two darts share the same (i, j, s), which would create a duplicate edge."""
    keys = set(zip(dI.tolist(), dJ.tolist(), S.tolist()))
    return len(keys) < len(S)


def _anneal(d, k, G, D, RT, INV, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments. Returns (cost, S, dJ, dI)."""
    T = d * k
    dI = np.array([t % k for t in range(T)], dtype=np.int64)
    dJ = np.zeros(T, dtype=np.int64)
    S = np.zeros(T, dtype=np.int64)
    for L in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            dJ[L * k + i] = p[i]
            S[L * k + i] = rng.randrange(G)
    Ptab = dJ[:, None] * G + RT[S]
    Qtab = dI[:, None] * G + INV[S]

    def refresh(t):
        Ptab[t] = dJ[t] * G + RT[S[t]]
        Qtab[t] = dI[t] * G + INV[S[t]]

    def evaluate():
        if _has_dup(dI, dJ, S):
            return _BIG
        return _cost(k, G, D, dI, dJ, Ptab, Qtab)

    cost = evaluate()
    temp0 = 2.0
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.05, temp0 * (1.0 - it / iters))
        if k == 1 or rng.random() < 0.75:
            t = rng.randrange(T)
            old = int(S[t])
            s = rng.randrange(G)
            if s == old:
                continue
            S[t] = s
            refresh(t)
            c2 = evaluate()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                S[t] = old
                refresh(t)
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ta, tb = L * k + a, L * k + b
            dJ[ta], dJ[tb] = dJ[tb], dJ[ta]
            refresh(ta)
            refresh(tb)
            c2 = evaluate()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                dJ[ta], dJ[tb] = dJ[tb], dJ[ta]
                refresh(ta)
                refresh(tb)
    return cost, S, dJ, dI


def _lift_edges(k, G, dI, dJ, S, RT):
    """Explicit (n, edges) of the lift. A-vertices are 0..kG-1, B-vertices kG..2kG-1."""
    n = 2 * k * G
    g = np.arange(G, dtype=np.int64)
    E = []
    for t in range(len(S)):
        A = int(dI[t]) * G + g
        B = k * G + int(dJ[t]) * G + RT[int(S[t])]
        E.extend(zip(A.tolist(), B.tolist()))
    return n, E


def _sample_group(G, rng):
    """Random group of order G: semidirect product Z_m x| Z_k2 with m * k2 = G (k2 = 1 is cyclic)."""
    divs = [x for x in range(1, min(G, 60) + 1) if G % x == 0 and G // x >= 2]
    if not divs:
        return None
    for _ in range(30):
        k2 = rng.choice(divs)
        m = G // k2
        if k2 == 1:
            order, mul, _ = lib.semidirect_group(m, 1, 1)
            return order, mul
        r = None
        for _ in range(40):
            cand = rng.randrange(1, m)
            if math.gcd(cand, m) == 1 and pow(cand, k2, m) == 1 % m:
                r = cand
                break
        if r is None:
            continue
        order, mul, _ = lib.semidirect_group(m, k2, r)
        return order, mul
    return None


# ----------------------------------------------------------------------------
# Near-miss repair (delete far-off vertices) and degree saturation.
# Saturation only adds edges, so it never increases the diameter.
# ----------------------------------------------------------------------------

def _repair(n, E, D, rng, deadline):
    """Delete the most-violating vertices in batches until diameter <= D. Returns (n, E) or None."""
    cur_n, cur_e = n, list(E)
    while time.monotonic() < deadline and cur_n > 0:
        balls = lib._balls(cur_n, cur_e, D)
        bad = [cur_n - b.bit_count() for b in balls]
        if not any(bad):
            return cur_n, cur_e
        cand = [v for v in range(cur_n) if bad[v] > 0]
        cand.sort(key=lambda v: (-bad[v], rng.random()))
        batch = max(1, len(cand) // 10)
        dead = set(cand[:batch])
        new = {}
        for v in range(cur_n):
            if v not in dead:
                new[v] = len(new)
        cur_e = [(new[u], new[v]) for u, v in cur_e if u in new and v in new]
        cur_n = len(new)
    return None


def _saturate(n, E, d, rng):
    """Join deficient opposite-colour vertices that are not yet adjacent."""
    E = list(E)
    adj = [[] for _ in range(n)]
    have = set()
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
        have.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in have]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            E.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return n, E


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and is the fallback for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D == 2 or best_n >= lib.moore_bound(d, D):
        return best_n, best_e

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Main search: bi-Cayley lifts over semidirect products, scored by the
    # frontier-matrix oracle, with occasional repair of near-miss lifts.
    while time.monotonic() < deadline:
        if best_n >= lib.moore_bound(d, D):
            break
        k = rng.choice([1, 1, 1, 2, 2, 3])
        lo = max(2, best_n // (2 * k) + 1)
        width = max(3, lo // 5) if k == 1 else max(2, lo // 8)
        G = rng.randint(lo, lo + width)
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        RT = _right_table(mul, order)
        INV = np.argsort(RT, axis=1)
        iters = 1500 if k == 1 else 800
        cost, S, dJ, dI = _anneal(d, k, order, D, RT, INV, rng, deadline, iters)

        if cost == 0:
            n, E = _lift_edges(k, order, dI, dJ, S, RT)
            consider(n, E)
        elif cost <= 24 and rng.random() < 0.3 and time.monotonic() < deadline:
            n, E = _lift_edges(k, order, dI, dJ, S, RT)
            rep = _repair(n, E, D, rng, min(deadline, time.monotonic() + 4.0))
            if rep is not None:
                n2, E2 = _saturate(rep[0], rep[1], d, rng)
                consider(n2, E2)

    if not lib.is_valid(best_n, best_e, d, D):
        return 1, []
    return best_n, best_e
