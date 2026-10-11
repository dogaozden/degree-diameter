import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline: projective plane incidence graph (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New family: bi-Cayley voltage lifts over explicit non-cyclic groups.
#
# Groups are built as multiplication tables (identity at index 0):
#   - abelian Z_a x Z_b
#   - metacyclic Z_m x| Z_k (r^k = 1 mod m)
#   - wreath products Z_m wr Z_k (order m^k * k)
#   - affine groups AGL(1, q): x -> a x + b, order q(q-1)
#
# Base graph: k vertices per side, d layers. Layer L pairs A_i with
# B_{p_L(i)} via a permutation p_L, and each dart (i, j, s) joins
# A_{i,g} to B_{j, g*s} for every g. Left multiplication is an automorphism,
# so distances only need checking from one representative per (side, layer).
# ----------------------------------------------------------------------------

_BIG_PENALTY_SCALE = 2


def _table(elems, mulf):
    """Multiplication table of a finite group given by elements and a product; identity is index 0."""
    n = len(elems)
    idx = {x: i for i, x in enumerate(elems)}
    T = [[idx[mulf(a, b)] for b in elems] for a in elems]
    e = None
    ident = list(range(n))
    for i in range(n):
        if T[i] == ident:
            e = i
            break
    if e is None:
        return None
    order = [e] + [i for i in range(n) if i != e]
    pos = [0] * n
    for new, old in enumerate(order):
        pos[old] = new
    newT = [[pos[T[order[p]][order[q]]] for q in range(n)] for p in range(n)]
    return n, newT


def _build_group(spec, rng):
    """Return (order, table) for a group spec, or None if it cannot be built."""
    kind = spec[0]
    if kind == 'ab':
        a, b = spec[1], spec[2]
        elems = [(x, y) for x in range(a) for y in range(b)]

        def mulf(u, v):
            return ((u[0] + v[0]) % a, (u[1] + v[1]) % b)

    elif kind == 'sd':
        m, k2 = spec[1], spec[2]
        cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                 if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if not cands:
            return None
        r = rng.choice(cands)
        pw = [pow(r, b, m) for b in range(k2)]
        elems = [(x, y) for x in range(m) for y in range(k2)]

        def mulf(u, v):
            return ((u[0] + pw[u[1]] * v[0]) % m, (u[1] + v[1]) % k2)

    elif kind == 'wr':
        m, k2 = spec[1], spec[2]
        elems = [(t, v) for t in range(k2) for v in itertools.product(range(m), repeat=k2)]

        def mulf(u, v):
            t, x = u
            s, w = v
            wr = tuple(w[(i + t) % k2] for i in range(k2))
            return ((t + s) % k2, tuple((x[i] + wr[i]) % m for i in range(k2)))

    elif kind == 'aff':
        q = spec[1]
        F = lib.GF(q)
        elems = [(a, b) for a in range(1, q) for b in range(q)]

        def mulf(u, v):
            a, b = u
            c, d = v
            return (F.mul(a, c), F.add(F.mul(a, d), b))

    else:
        return None
    return _table(elems, mulf)


def _specs(lo, hi):
    """All group specs with order in [lo, hi]."""
    out = []
    for G in range(max(2, lo), hi + 1):
        for a in range(1, G + 1):
            if G % a == 0 and a <= G // a:
                out.append(('ab', a, G // a))
        for k2 in range(2, G):
            if G % k2 == 0 and G // k2 >= 2:
                out.append(('sd', G // k2, k2))
        for k2 in (2, 3):
            for m in range(2, 13):
                if m ** k2 * k2 == G:
                    out.append(('wr', m, k2))
        for q in range(3, G + 2):
            if q * (q - 1) == G and lib.is_prime_power(q):
                out.append(('aff', q))
    return out


def _cost(k, G, D, darts, rp):
    """Unreached (representative, vertex) pairs within distance D, plus a penalty for duplicate darts."""
    dups = len(darts) - len({(i, j, s) for i, j, s in darts})
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        pm = rp[s]
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
    return total + _BIG_PENALTY_SCALE * G * dups


def _edges(k, G, darts, rp):
    E = set()
    for i, j, s in darts:
        pm = rp[s]
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, k, D, G, rp, rng, deadline, iters):
    """Simulated annealing over voltages and layer permutations. Returns (n, edges) or None."""
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    cost = _cost(k, G, D, darts, rp)
    T0, T1 = 2.0, 0.15
    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _cost(k, G, D, darts, rp)
            if c2 <= cost or rng.random() < math.exp((cost - c2) / T):
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, rp)
            if c2 <= cost or rng.random() < math.exp((cost - c2) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    if cost == 0:
        return _edges(k, G, darts, rp)
    return None


def _bicayley_search(d, D, best_n, consider, deadline, rng):
    """Repeatedly anneal bi-Cayley lifts over new group families, targeting orders above best_n."""
    ks = [1, 2, 2, 3, 4]
    iters = 3000
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        lo = max(2, best_n // (2 * k) + 1)
        specs = _specs(lo, lo + 4)
        if not specs:
            continue
        nonab = [s for s in specs if s[0] != 'ab']
        if nonab and rng.random() < 0.75:
            spec = rng.choice(nonab)
        else:
            spec = rng.choice(specs)
        built = _build_group(spec, rng)
        if built is None:
            continue
        G, T = built
        rp = [[T[x][s] for x in range(G)] for s in range(G)]
        res = _anneal(d, k, D, G, rp, rng, deadline, iters)
        if res is not None:
            consider(res[0], res[1])


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and d >= 3:
        _bicayley_search(d, D, best_n, consider, deadline, rng)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
