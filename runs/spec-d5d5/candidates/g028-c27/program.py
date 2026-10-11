import itertools
import random
import time

import lib

T_HOT = 1.5        # initial annealing temperature (in unreached-pair units)
T_COLD = 0.15      # final annealing temperature
ITERS = 1500       # annealing steps per restart
SAFETY = 0.72      # fraction of time_limit we allow ourselves
FIRST_BUDGET = 0.35


# ----------------------------------------------------------------------------
# Safe baselines (always checked with lib.is_valid before being returned).
# ----------------------------------------------------------------------------

def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# A different family from the parent: bi-Cayley graphs over permutation groups
# (non-solvable groups such as PSL(2,7), A5, S5, AGL(1,17), S4 x Z_k), instead of
# only semidirect products Z_m x| Z_k.
#
# Vertices A_x, B_y (x, y in G). Edge A_x -- B_{x s} for s in S, |S| = d.
# Identity is WLOG in S. Left multiplication is an automorphism, so the
# eccentricities of A_e and B_e decide the diameter.
# ----------------------------------------------------------------------------

def _cycle(n, cyc):
    """Permutation of range(n) that sends cyc[i] -> cyc[i+1] cyclically."""
    p = list(range(n))
    L = len(cyc)
    for i in range(L):
        p[cyc[i]] = cyc[(i + 1) % L]
    return tuple(p)


def _direct(gA, na, gB, nb):
    """Direct product of two permutation groups acting on disjoint domains."""
    gens = [tuple(g) + tuple(range(na, na + nb)) for g in gA]
    gens += [tuple(range(na)) + tuple(x + na for x in h) for h in gB]
    return gens, na + nb


def _psl_gens():
    """Generators of PSL(2,7) acting on the projective line (points 0..6, infinity = 7)."""
    t = tuple([(x + 1) % 7 for x in range(7)] + [7])
    s2 = tuple([(2 * x) % 7 for x in range(7)] + [7])
    iv = tuple([7] + [(-pow(x, -1, 7)) % 7 for x in range(1, 7)] + [0])
    return [t, s2, iv]


def _catalog():
    """List of (expected order, generators, number of points) for candidate groups."""
    cat = []
    psl = _psl_gens()
    cat.append((336, psl + [tuple([(3 * x) % 7 for x in range(7)] + [7])], 8))   # PGL(2,7)
    g, n = _direct(psl, 8, [_cycle(2, [0, 1])], 2)
    cat.append((336, g, n))                                                       # PSL(2,7) x Z2
    cat.append((168, psl, 8))                                                     # PSL(2,7)
    a5 = [_cycle(5, [0, 1, 2]), _cycle(5, [0, 1, 2, 3, 4])]
    g, n = _direct(a5, 5, [_cycle(5, [0, 1, 2, 3, 4])], 5)
    cat.append((300, g, n))                                                       # A5 x Z5
    t = tuple([(x + 1) % 17 for x in range(17)])
    m = tuple([(3 * x) % 17 for x in range(17)])
    cat.append((272, [t, m], 17))                                                 # AGL(1,17)
    s5 = [_cycle(5, [0, 1]), _cycle(5, [0, 1, 2, 3, 4])]
    g, n = _direct(s5, 5, [_cycle(2, [0, 1])], 2)
    cat.append((240, g, n))                                                       # S5 x Z2
    s4 = [_cycle(4, [0, 1]), _cycle(4, [0, 1, 2, 3])]
    a4 = [_cycle(4, [0, 1, 2]), _cycle(4, [1, 2, 3])]
    for k in (8, 11, 12, 13):
        g, n = _direct(s4, 4, [_cycle(k, list(range(k)))], k)
        cat.append((24 * k, g, n))                                                # S4 x Z_k
    for k in (20, 24):
        g, n = _direct(a4, 4, [_cycle(k, list(range(k)))], k)
        cat.append((12 * k, g, n))                                                # A4 x Z_k
    return cat


def _make_group(gens, npts, cap):
    """Close the permutation group, return (N, T, invs) with T[x][g] = index of x*g.

    Identity has index 0. Returns None if the group has more than cap elements.
    """
    ident = tuple(range(npts))
    elems = [ident]
    index = {ident: 0}
    frontier = [ident]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = tuple(g[i] for i in x)
                if y not in index:
                    if len(elems) >= cap:
                        return None
                    index[y] = len(elems)
                    elems.append(y)
                    nxt.append(y)
        frontier = nxt
    N = len(elems)
    T = []
    for x in elems:
        T.append([index[tuple(g[i] for i in x)] for g in elems])
    invs = [row.index(0) for row in T]
    return N, T, invs


def _unreached(N, T, invs, S, D):
    """Count (source, vertex) pairs not within distance D, for sources A_e and B_e (e = 0)."""
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


def _anneal(N, T, invs, d, D, rng, iters, deadline):
    """Simulated annealing over S = {0, s_1, ..., s_{d-1}} to zero the unreached pair count."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur or rng.random() < pow(2.718281828459045, -(v - cur) / temp):
            S, cur = S2, v
    if cur == 0:
        return S
    return None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + SAFETY * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = [1, []]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0] = n
            best[1] = e

    def finish():
        n, e = best
        if n == 1 or lib.is_valid(n, e, d, D):
            return n, e
        return 1, []

    # Record-matching case for D = 3.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return finish()

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _pg_best(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return finish()

    Nmax = lib._moore_bound(d, D) // 2   # bi-Cayley graph has 2N vertices
    cat = [c for c in _catalog() if d + 1 <= c[0] <= Nmax]
    cat.sort(key=lambda c: -c[0])
    built = {}
    budget = FIRST_BUDGET

    while time.monotonic() < deadline:
        live = [i for i, c in enumerate(cat) if 2 * c[0] > best[0]]
        if not live:
            break
        ran = False
        for i in live:
            if time.monotonic() >= deadline:
                break
            if 2 * cat[i][0] <= best[0]:
                continue
            if i not in built:
                _, gens, npts = cat[i]
                built[i] = _make_group(gens, npts, Nmax)
            grp = built[i]
            if grp is None:
                continue
            N, T, invs = grp
            if 2 * N <= best[0] or N <= d:
                continue
            end = min(deadline, time.monotonic() + budget)
            S = None
            ran = True
            while time.monotonic() < end:
                S = _anneal(N, T, invs, d, D, rng, ITERS, end)
                if S is not None:
                    break
            if S is not None:
                consider(2 * N, [(x, N + T[x][g]) for x in range(N) for g in S])
        if not ran:
            break
        budget *= 2

    return finish()
