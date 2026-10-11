import math
import random
import time

import lib

_BIG = 10 ** 9
_REPAIR_MAX_COST = 60
_TARGET_FLOOR_D5 = 626


# ----------------------------------------------------------------------------
# Safe fallbacks: projective plane incidence and Araujo-Pardo-Lopez (D = 3).
# ----------------------------------------------------------------------------

def _pg_fallback(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Group machinery: semidirect products Z_m x| Z_k2 with lazily cached
# right-multiplication tables.
# ----------------------------------------------------------------------------

class _Rows:
    """Lazy table: self[s] is the permutation g -> g * s of the group."""

    def __init__(self, G, mul):
        self.G = G
        self.mul = mul
        self.cache = {}

    def __getitem__(self, s):
        r = self.cache.get(s)
        if r is None:
            mul = self.mul
            r = [mul(x, s) for x in range(self.G)]
            self.cache[s] = r
        return r


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        r = 1
        if k2 > 1:
            cands = [x for x in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(x, m) == 1 and pow(x, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


# ----------------------------------------------------------------------------
# Bi-regular voltage lifts. A dart (i, j, s) joins A_{i,g} to B_{j,g*s}.
# A base graph is d layers, each a permutation of range(k), so every base
# vertex has degree d. Left multiplication is an automorphism, so only one
# representative per fibre needs a BFS.
# ----------------------------------------------------------------------------

def _cost(k, G, D, darts, R):
    """Unreached (representative, vertex) pairs within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        row = R[s]
        bi, bj = i * G, (k + j) * G
        for g in range(G):
            a, b = bi + g, bj + row[g]
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
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
    return total


def _edges(k, G, darts, R):
    E = []
    for i, j, s in darts:
        row = R[s]
        bi, bj = i * G, (k + j) * G
        for g in range(G):
            E.append((bi + g, bj + row[g]))
    return 2 * k * G, E


def _greedy_lift(d, D, k, G, R, rng, deadline):
    """Construct darts layer by layer, choosing each voltage greedily, then do one improvement pass."""
    layers = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        layers.append(p)
    darts = []
    used = set()
    tries = 8
    for p in layers:
        for i in range(k):
            j = p[i]
            opts = [s for s in range(G) if (i, j, s) not in used]
            if not opts:
                return None
            best_c, best_s = None, None
            for s in rng.sample(opts, min(len(opts), tries)):
                darts.append([i, j, s])
                c = _cost(k, G, D, darts, R)
                darts.pop()
                if best_c is None or c < best_c:
                    best_c, best_s = c, s
                if time.monotonic() > deadline:
                    return None
            darts.append([i, j, best_s])
            used.add((i, j, best_s))
    cur = _cost(k, G, D, darts, R)
    for idx in range(len(darts)):
        if cur == 0 or time.monotonic() > deadline:
            break
        i, j, s0 = darts[idx]
        used.discard((i, j, s0))
        best_c, best_s = cur, s0
        for s in rng.sample(range(G), min(G, tries)):
            if s == s0 or (i, j, s) in used:
                continue
            darts[idx] = [i, j, s]
            c = _cost(k, G, D, darts, R)
            if c < best_c:
                best_c, best_s = c, s
        darts[idx] = [i, j, best_s]
        used.add((i, j, best_s))
        cur = best_c
    return darts, cur


def _random_darts(d, k, G, rng):
    out = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            out.append([i, p[i], rng.randrange(G)])
    return out


def _anneal(d, D, k, G, R, rng, deadline):
    """Simulated annealing over voltages and layer-preserving endpoint swaps."""
    darts = _random_darts(d, k, G, rng)
    cost = _cost(k, G, D, darts, R)
    T = 1.0
    while cost > 0 and time.monotonic() < deadline:
        T = max(0.05, T * 0.996)
        limit = cost - T * math.log(1.0 - rng.random())
        idx = rng.randrange(len(darts))
        if k == 1 or rng.random() < 0.7:
            old = darts[idx][2]
            darts[idx][2] = rng.randrange(G)
            c2 = _cost(k, G, D, darts, R)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = idx // k
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, R)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    return darts, cost


# ----------------------------------------------------------------------------
# Repair a near-miss graph by deleting far-off vertices in batches.
# Deletion keeps max degree, bipartiteness, and simple edges.
# ----------------------------------------------------------------------------

def _repair(n, edges, D, deadline, rng):
    while time.monotonic() < deadline and n > 0:
        adj = [[] for _ in range(n)]
        for u, v in edges:
            adj[u].append(v)
            adj[v].append(u)
        ball = [1 << v for v in range(n)]
        for _ in range(D):
            nb = []
            for v in range(n):
                x = ball[v]
                for u in adj[v]:
                    x |= ball[u]
                nb.append(x)
            ball = nb
        bad = [n - b.bit_count() for b in ball]
        bad_v = [v for v in range(n) if bad[v] > 0]
        if not bad_v:
            return n, edges
        rng.shuffle(bad_v)
        bad_v.sort(key=lambda v: -bad[v])
        batch = max(1, len(bad_v) // 12)
        dead = set(bad_v[:batch])
        keep = [v for v in range(n) if v not in dead]
        new = {old: idx for idx, old in enumerate(keep)}
        edges = [(new[u], new[v]) for u, v in edges if u in new and v in new]
        n = len(keep)
    return None


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = 0.82 * time_limit
    deadline = start + budget
    rng = random.Random(seed)

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

    if D >= 3:
        pg = _pg_fallback(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Calibration-sized cases and degenerate degrees return the known construction.
    if D <= 3 or d < 2:
        return best

    floor = _TARGET_FLOOR_D5 if D >= 5 else 0
    phase_end = start + 0.5 * budget

    while time.monotonic() < deadline:
        k = rng.choice([1, 2, 2, 3, 3, 4, 4, 5, 6]) if D >= 5 else rng.choice([1, 2, 3])
        target = max(best_n + 2, floor)
        lo = max(2, -(-target // (2 * k)))
        G = rng.randint(lo, lo + max(3, lo // 25))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        R = _Rows(order, mul)

        if time.monotonic() < phase_end:
            res = _greedy_lift(d, D, k, order, R, rng, deadline)
            if res is None:
                continue
            darts, c = res
        else:
            darts, c = _anneal(d, D, k, order, R, rng, deadline)

        if c == 0:
            n, e = _edges(k, order, darts, R)
            consider(n, e)
        elif c <= _REPAIR_MAX_COST and time.monotonic() < deadline:
            n, e = _edges(k, order, darts, R)
            rep = _repair(n, e, D, min(deadline, time.monotonic() + 4.0), rng)
            if rep is not None:
                consider(rep[0], rep[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
