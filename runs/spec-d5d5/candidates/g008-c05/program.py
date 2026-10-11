import itertools
import math
import random
import time

import lib

_BIG = 10 ** 9
_GCACHE = {}
ATTEMPT_SECONDS = 4.0


# ----------------------------------------------------------------------------
# Group library: matrix groups over GF(p), direct products, semidirect products.
# Each group is (N, T) with identity at index 0 and T[x][y] = x*y.
# ----------------------------------------------------------------------------

def _matrix_group(p, kind):
    """SL(2,p), PSL(2,p) or PGL(2,p) as a multiplication table."""
    inv_p = [0] * p
    for c in range(1, p):
        inv_p[c] = pow(c, p - 2, p)

    def norm(t):
        if kind == "PGL":
            c = next(x for x in t if x)
            ci = inv_p[c]
            return (t[0] * ci % p, t[1] * ci % p, t[2] * ci % p, t[3] * ci % p)
        if kind == "PSL":
            neg = ((-t[0]) % p, (-t[1]) % p, (-t[2]) % p, (-t[3]) % p)
            return min(t, neg)
        return t

    def ok(t):
        det = (t[0] * t[3] - t[1] * t[2]) % p
        return det != 0 if kind == "PGL" else det == 1

    elems = {norm(t) for t in itertools.product(range(p), repeat=4) if ok(t)}
    ident = norm((1, 0, 0, 1))
    els = [ident] + sorted(e for e in elems if e != ident)
    idx = {e: i for i, e in enumerate(els)}
    N = len(els)
    T = [[0] * N for _ in range(N)]
    for i, x in enumerate(els):
        a, b, c, dd = x
        row = T[i]
        for j, y in enumerate(els):
            e, f, g, h = y
            row[j] = idx[norm(((a * e + b * g) % p, (a * f + b * h) % p,
                               (c * e + dd * g) % p, (c * f + dd * h) % p))]
    return N, T


def _order(spec):
    t = spec[0]
    if t == 'mat':
        p, kind = spec[1], spec[2]
        full = p * (p * p - 1)
        return full // 2 if kind == 'PSL' else full
    if t == 'cyc':
        return spec[1]
    if t == 'semi':
        return spec[1] * spec[2]
    return _order(spec[1]) * _order(spec[2])


def _build_group(spec):
    if spec in _GCACHE:
        return _GCACHE[spec]
    t = spec[0]
    if t == 'mat':
        N, T = _matrix_group(spec[1], spec[2])
    elif t == 'cyc':
        m = spec[1]
        N = m
        T = [[(a + b) % m for b in range(m)] for a in range(m)]
    elif t == 'semi':
        m, k, r = spec[1], spec[2], spec[3]
        N, mul, _ = lib.semidirect_group(m, k, r)
        T = [[mul(a, b) for b in range(N)] for a in range(N)]
    else:
        N1, T1 = _build_group(spec[1])
        N2, T2 = _build_group(spec[2])
        N = N1 * N2
        T = [[0] * N for _ in range(N)]
        for x in range(N):
            a1, b1 = divmod(x, N2)
            row = T[x]
            r1 = T1[a1]
            r2 = T2[b1]
            for y in range(N):
                a2, b2 = divmod(y, N2)
                row[y] = r1[a2] * N2 + r2[b2]
    if len(_GCACHE) >= 12:
        _GCACHE.clear()
    _GCACHE[spec] = (N, T)
    return N, T


def _candidate_specs(rng, gmin, gmax):
    """Shuffled list of group specs whose order lies in [gmin, gmax]."""
    specs = []
    bases = [('mat', 3, 'PGL'), ('mat', 3, 'PSL'), ('mat', 5, 'PSL'),
             ('mat', 5, 'PGL'), ('mat', 5, 'SL'), ('mat', 7, 'PSL'),
             ('mat', 7, 'PGL'), ('mat', 7, 'SL')]
    for b in bases:
        ob = _order(b)
        if ob <= gmax:
            specs.append(b)
            for m in range(2, gmax // ob + 1):
                specs.append(('dir', b, ('cyc', m)))
    for m in range(2, gmax + 1):
        specs.append(('cyc', m))
    for N in range(gmin, gmax + 1):
        for k in range(2, N + 1):
            if N % k:
                continue
            m = N // k
            if m < 2:
                continue
            rs = [r for r in range(1, m)
                  if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            rng.shuffle(rs)
            for r in rs[:2]:
                specs.append(('semi', m, k, r))
    specs = [s for s in specs if gmin <= _order(s) <= gmax]
    rng.shuffle(specs)
    return specs


# ----------------------------------------------------------------------------
# Multi-base voltage lifts over a group G: 2kG vertices, d-regular bipartite.
# Dart (i, j, s): A_{i,g} ~ B_{j,g*s}. Each layer is a permutation of the k
# base pairs, so every vertex has degree d. Left translation is an automorphism,
# so eccentricities from the 2k representatives A_{i,e}, B_{j,e} suffice.
# ----------------------------------------------------------------------------

def _distinct(darts):
    return len({(i, j, s) for i, j, s in darts}) == len(darts)


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D."""
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


def _edges(k, G, darts, perms):
    E = []
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.append((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, E


def _anneal(d, D, k, G, T, rng, deadline):
    """Simulated annealing over darts (voltages and layer permutations)."""
    if G < d:
        return None
    darts = None
    for _ in range(200):
        cand = []
        for _ in range(d):
            p = list(range(k))
            rng.shuffle(p)
            for i in range(k):
                cand.append([i, p[i], rng.randrange(G)])
        cand[0][2] = 0  # WLOG: right translation relabels B-vertices
        if _distinct(cand):
            darts = cand
            break
    if darts is None:
        return None
    perms = [[T[g][s] for g in range(G)] for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)
    if cost == 0:
        return _edges(k, G, darts, perms)

    t0 = max(1.0, 0.05 * cost)
    t_start = time.monotonic()
    span = max(1e-3, deadline - t_start)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        temp = t0 * (0.02 ** min(1.0, (now - t_start) / span))
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(1, len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            old_pm = perms[idx]
            darts[idx][2] = new
            perms[idx] = [T[g][new] for g in range(G)]
            if not _distinct(darts):
                darts[idx][2] = old
                perms[idx] = old_pm
                continue
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cost = c2
            else:
                darts[idx][2] = old
                perms[idx] = old_pm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            if not _distinct(darts):
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
                continue
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Fallbacks and main entry point.
# ----------------------------------------------------------------------------

def _fallback(d):
    """K_{d,d}: diameter 2, always valid for d >= 1."""
    if d < 1:
        return 1, []
    return lib.haar_graph(d, range(d))


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1:
        return 1, []
    if D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = _fallback(d)
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Structured baseline for D = 3: projective plane when d-1 is a prime power.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n2, e2 = lib.projective_plane_incidence(d - 1)
        consider(n2, e2)

    # Main search: bi-Cayley and multi-base lifts over non-abelian groups.
    if best[0] < moore and d >= 2:
        gmin = max(2, best[0] // 6 + 1)
        gmax = moore // 2
        specs = _candidate_specs(rng, gmin, gmax)
        for spec in specs:
            now = time.monotonic()
            if now >= deadline or best[0] >= moore:
                break
            G = _order(spec)
            ks = [k for k in (1, 2, 3) if best[0] < 2 * k * G <= moore]
            if not ks:
                continue
            k = rng.choice(ks)
            N, T = _build_group(spec)
            slice_end = min(deadline, now + ATTEMPT_SECONDS)
            res = _anneal(d, D, k, N, T, rng, slice_end)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = _fallback(d)
    return best[0], best[1]
