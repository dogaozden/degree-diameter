import math
import random
import time

import lib

MAX_GROUPS = 10        # group specs tried per order N before moving on
CLIMB_ITERS = 1500     # annealing steps per bi-Cayley attempt
ANNEAL_ITERS = 1200    # annealing steps per multi-base attempt
MAX_TABLE = 400        # largest group order we tabulate
BIG = 10 ** 9
_CACHE = {}


class Grp:
    """Finite group of order n with identity 0, multiplication table T[x][y] = x*y, and inverses."""

    def __init__(self, n, mul):
        self.n = n
        self.T = [[mul(x, y) for y in range(n)] for x in range(n)]
        self.inv = [self.T[x].index(0) for x in range(n)]


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k (k = 1 gives cyclic)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _agaml(q):
    """AGammaL(1, q) for q = p^n: maps x -> a * x^(p^s) + b. Identity is index 0."""
    p, n = lib._prime_power(q)
    F = lib.GF(q)
    frob = [[F.pow(x, p ** s) if x else 0 for x in range(q)] for s in range(n)]

    def enc(a, b, s):
        return ((a - 1) * q + b) * n + s

    def mul(x, y):
        s1, t1 = x % n, x // n
        b1, a1 = t1 % q, t1 // q + 1
        s2, t2 = y % n, y // n
        b2, a2 = t2 % q, t2 // q + 1
        a = F.mul(a1, frob[s1][a2])
        b = F.add(F.mul(a1, frob[s1][b2]), b1)
        return enc(a, b, (s1 + s2) % n)

    return Grp((q - 1) * q * n, mul)


def _product(g1, g2):
    n2 = g2.n
    T1, T2 = g1.T, g2.T

    def mul(x, y):
        x1, x2 = divmod(x, n2)
        y1, y2 = divmod(y, n2)
        return T1[x1][y1] * n2 + T2[x2][y2]

    return Grp(g1.n * n2, mul)


def _build(spec):
    """Build (and cache) the group described by a spec tuple."""
    g = _CACHE.get(spec)
    if g is not None:
        return g
    t = spec[0]
    if t == 'sd':
        order, mul, _ = lib.semidirect_group(spec[1], spec[2], spec[3])
        g = Grp(order, mul)
    elif t == 'ag':
        g = _agaml(spec[1])
    else:
        g = _product(_build(spec[1]), _build(spec[2]))
    if len(_CACHE) >= 80:
        _CACHE.clear()
    _CACHE[spec] = g
    return g


def _specs(N, rng):
    """Shuffled list of group specs of order N: semidirect products, AGammaL(1,q), and small products."""
    out = [('sd', m, k, r) for (m, k, r) in _groups(N)]
    for q in range(3, 64):
        pk = lib._prime_power(q)
        if pk is not None and (q - 1) * q * pk[1] == N:
            out.append(('ag', q))
    divs = [a for a in range(2, N // 2 + 1) if N % a == 0]
    for _ in range(4):
        if not divs:
            break
        a = rng.choice(divs)
        b = N // a
        sa, sb = _groups(a), _groups(b)
        if sa and sb:
            out.append(('pr', ('sd',) + rng.choice(sa), ('sd',) + rng.choice(sb)))
    rng.shuffle(out)
    return out


# ----------------------------------------------------------------------------
# Bi-Cayley lifts: A_x ~ B_{x*s} for s in S, over a group of order N.
# Left translation is an automorphism, so BFS from A_e and B_e suffices.
# ----------------------------------------------------------------------------

def _unreached(G, S, D):
    N = G.n
    T, inv = G.T, G.inv
    Sinv = [inv[g] for g in S]
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


def _climb(G, d, D, rng, iters, deadline):
    """Simulated annealing over connection sets S of size d minimizing unreached pairs."""
    N = G.n
    if N < d:
        return None
    S = rng.sample(range(N), d)
    cur = _unreached(G, S, D)
    best_S, best_v = S[:], cur
    T0 = 2.0 + 0.1 * cur
    for step in range(iters):
        if best_v == 0 or time.monotonic() > deadline:
            break
        temp = T0 * (1.0 - step / iters) + 0.15
        i = rng.randrange(d)
        c = rng.randrange(N)
        if c in S:
            continue
        old = S[i]
        S[i] = c
        v = _unreached(G, S, D)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur = v
            if cur < best_v:
                best_v, best_S = cur, S[:]
        else:
            S[i] = old
    return best_S if best_v == 0 else None


# ----------------------------------------------------------------------------
# Multi-base lifts: k base vertices per side, d layers of permutations,
# voltages in a group of order G. Vertex (side, base i, x) with x in G.
# ----------------------------------------------------------------------------

def _multi_cost(G, k, D, darts):
    keys = set()
    for dt in darts:
        t = (dt[0], dt[1], dt[2])
        if t in keys:
            return BIG
        keys.add(t)
    n, T = G.n, G.T
    N2 = 2 * k * n
    adj = [[] for _ in range(N2)]
    for i, j, g in darts:
        for x in range(n):
            a = i * n + x
            b = (k + j) * n + T[x][g]
            adj[a].append(b)
            adj[b].append(a)
    sources = [i * n for i in range(k)] + [(k + j) * n for j in range(k)]
    total = 0
    for src in sources:
        seen = bytearray(N2)
        seen[src] = 1
        count = 1
        frontier = [src]
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
        total += N2 - count
    return total


def _multi_edges(k, G, darts):
    n, T = G.n, G.T
    E = set()
    for i, j, g in darts:
        for x in range(n):
            E.add((i * n + x, (k + j) * n + T[x][g]))
    return 2 * k * n, sorted(E)


def _anneal_multi(d, D, k, G, rng, deadline, iters):
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G.n)])
    cost = _multi_cost(G, k, D, darts)
    T = 1.5
    decay = (0.15 / 1.5) ** (1.0 / max(1, iters))
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T *= decay
        if k == 1 or rng.random() < 0.6:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G.n)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _multi_cost(G, k, D, darts)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _multi_cost(G, k, D, darts)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    if cost == 0:
        return _multi_edges(k, G, darts)
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

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        # Projective plane incidence graph of PG(2, q), q the largest prime power <= d - 1.
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                n, e = lib.projective_plane_incidence(q)
                consider(n, e)
                break
        return best

    # D >= 4: group-lift search. Most time goes to bi-Cayley lifts over many
    # groups (semidirect, AGammaL(1,q), small products); the rest to multi-base lifts.
    tried = {}
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        if rng.random() < 0.7:
            lo = n_best // 2 + 1
            if lo > moore // 2:
                break
            window = max(3, lo // 25)
            hi = min(lo + window, moore // 2 + 1)
            N = min(range(lo, hi), key=lambda x: (tried.get(x, 0), rng.random()))
            tried[N] = tried.get(N, 0) + 1
            found_G, found_S = None, None
            for spec in _specs(N, rng)[:MAX_GROUPS]:
                if time.monotonic() > deadline:
                    break
                G = _build(spec)
                S = _climb(G, d, D, rng, CLIMB_ITERS, deadline)
                if S is not None:
                    found_G, found_S = G, S
                    break
            if found_S is not None:
                T = found_G.T
                N = found_G.n
                edges = [(x, N + T[x][s]) for x in range(N) for s in found_S]
                consider(2 * N, edges)
        else:
            k = rng.choice((2, 3))
            lo_g = n_best // (2 * k) + 1
            if 2 * k * lo_g > moore:
                continue
            order = lo_g + rng.randrange(max(2, lo_g // 10))
            if order < 2 or order > MAX_TABLE:
                continue
            specs = _specs(order, rng)
            if not specs:
                continue
            G = _build(specs[0])
            res = _anneal_multi(d, D, k, G, rng, deadline, ANNEAL_ITERS)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
