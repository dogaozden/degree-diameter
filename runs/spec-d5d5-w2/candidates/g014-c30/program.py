import itertools
import math
import random
import time

import lib

CLIMB_ITERS = 350
MAX_GROUPS = 6
MAX_TABLE = 700
_TABLE_CACHE = {}
_BASE_CACHE = {}
_BASE_SPECS = [("psl", 3), ("pgl", 3), ("psl", 5), ("pgl", 5),
               ("psl", 7), ("pgl", 7), ("psl", 11)]


# ----------------------------------------------------------------------------
# Group tables. Besides semidirect products Z_m x|_r Z_k, this family uses
# PSL(2,p) and PGL(2,p) (matrix groups mod scalars) and direct products of
# those with cyclic groups. Each group is (N, T, invs) with identity index 0,
# T[x][g] = x*g and invs[g] = g^-1.
# ----------------------------------------------------------------------------

def _base_order(kind, p):
    full = p * (p * p - 1)
    return full if kind == "pgl" else full // 2


def _proj_norm(vals, p, full):
    """Canonical representative of a matrix class: projective (PGL) or +-1 (PSL)."""
    if full:
        for x in vals:
            if x:
                inv = pow(x, p - 2, p)
                return tuple(y * inv % p for y in vals)
        return None
    neg = tuple((-y) % p for y in vals)
    return min(vals, neg)


def _matrix_group(kind, p):
    full = kind == "pgl"
    elems = set()
    for a, b, c, d in itertools.product(range(p), repeat=4):
        det = (a * d - b * c) % p
        if (det == 0) if full else (det != 1):
            continue
        elems.add(_proj_norm((a, b, c, d), p, full))
    ident = (1, 0, 0, 1)
    elems.discard(ident)
    order = [ident] + sorted(elems)
    idx = {e: i for i, e in enumerate(order)}
    N = len(order)
    T = []
    for x in order:
        a, b, c, d = x
        row = []
        for g in order:
            e, f, h, k = g
            m = _proj_norm(((a * e + b * h) % p, (a * f + b * k) % p,
                            (c * e + d * h) % p, (c * f + d * k) % p), p, full)
            row.append(idx[m])
        T.append(row)
    invs = [row.index(0) for row in T]
    return N, T, invs


def _base(kind, p):
    key = (kind, p)
    if key not in _BASE_CACHE:
        _BASE_CACHE[key] = _matrix_group(kind, p)
    return _BASE_CACHE[key]


def _semidirect_table(m, k, r):
    order, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    invs = [inv(g) for g in range(order)]
    return order, T, invs


def _direct(G1, G2):
    N1, T1, I1 = G1
    N2, T2, I2 = G2
    N = N1 * N2
    T = []
    for x in range(N):
        a, b = divmod(x, N2)
        r1, r2 = T1[a], T2[b]
        row = [0] * N
        for y in range(N):
            c, e = divmod(y, N2)
            row[y] = r1[c] * N2 + r2[e]
        T.append(row)
    invs = [I1[x // N2] * N2 + I2[x % N2] for x in range(N)]
    return N, T, invs


def _get_group(desc):
    hit = _TABLE_CACHE.get(desc)
    if hit is not None:
        return hit
    if desc[0] == "s":
        G = _semidirect_table(desc[1], desc[2], desc[3])
    else:
        _, kind, p, z = desc
        base = _base(kind, p)
        G = base if z == 1 else _direct(base, _semidirect_table(z, 1, 1))
    if len(_TABLE_CACHE) >= 24:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[desc] = G
    return G


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


def _candidates(N, rng):
    """Group descriptors of order N: matrix-group products first, then semidirect."""
    prods = []
    for kind, p in _BASE_SPECS:
        order = _base_order(kind, p)
        if order <= N and N % order == 0:
            prods.append(("p", kind, p, N // order))
    rng.shuffle(prods)
    sems = [("s", m, k, r) for (m, k, r) in _groups(N)]
    rng.shuffle(sems)
    return prods + sems


# ----------------------------------------------------------------------------
# Bi-Cayley lift: A_x ~ B_{x g} for g in S, |S| = d. Vertex-transitive on each
# side, so eccentricities from A_0 and B_0 decide the diameter.
# ----------------------------------------------------------------------------

def _unreached(N, T, invs, S, D):
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


def _climb(N, T, invs, d, D, rng, iters, deadline):
    """Simulated annealing over S (identity fixed as one element, WLOG)."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    best_S, best_v = S, cur
    T0 = 4.0 + 0.05 * cur
    for step in range(iters):
        if best_v == 0 or time.monotonic() > deadline:
            break
        temp = T0 * (1.0 - step / iters) + 0.2
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S, cur = S2, v
            if cur < best_v:
                best_S, best_v = S, cur
    return best_S if best_v == 0 else None


# ----------------------------------------------------------------------------
# D = 3 structured start (projective plane), for calibration.
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
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
    if D == 2 or d == 1:
        return best

    moore = lib.moore_bound(d, D)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg

    tried = {}
    while best[0] < moore and time.monotonic() < deadline:
        lo = best[0] // 2 + 1
        if lo > moore // 2 or lo > MAX_TABLE:
            break
        window = max(2, lo // 10)
        hi = min(lo + window, moore // 2 + 1, MAX_TABLE + 1)
        N = min(range(lo, hi), key=lambda x: (tried.get(x, 0), rng.random()))
        tried[N] = tried.get(N, 0) + 1
        for desc in _candidates(N, rng)[:MAX_GROUPS]:
            if time.monotonic() > deadline:
                break
            _, T, invs = _get_group(desc)
            S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
            if S is not None:
                edges = [(x, N + T[x][g]) for x in range(N) for g in S]
                if 2 * N > best[0] and lib.is_valid(2 * N, edges, d, D):
                    best = (2 * N, edges)
                break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
