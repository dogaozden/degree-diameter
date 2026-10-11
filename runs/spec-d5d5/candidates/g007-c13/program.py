import itertools
import math
import random
import time

import lib

ITERS = 600                   # annealing steps per (group, connection set) try
T_HOT = 1.5                   # initial annealing temperature (in unreached-pair units)
T_COLD = 0.15                 # final annealing temperature
WINDOW0 = 12                  # initial width of the order window above the current best
PICKS = 12                    # group specs sampled per pass

# Permutation-group bases: PSL(2,p), PGL(2,p), AGL(1,p). These are non-metacyclic
# groups (PSL(2,7) has order 168, PGL(2,7) has order 336) that the semidirect family
# misses. They are built from generators by closure (see _perm_table).
_PERM_BASES = [(kind, p) for p in (3, 5, 7, 11, 13, 17)
               for kind in ('psl', 'pgl', 'agl')]


# ----------------------------------------------------------------------------
# Baseline families (fast, always valid when they pass lib.is_valid).
# ----------------------------------------------------------------------------

def _best_pg(d):
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
# Group tables.
#
# Every group is given as a multiplication table T with T[x][g] = x*g, where
# index 0 is the identity. A bi-Cayley graph on two copies of G uses only T.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _prim_root(p):
    """Smallest primitive root modulo the odd prime p."""
    fs = set()
    n = p - 1
    f = 2
    while f * f <= n:
        while n % f == 0:
            fs.add(f)
            n //= f
        f += 1
    if n > 1:
        fs.add(n)
    for g in range(2, p):
        if all(pow(g, (p - 1) // f, p) != 1 for f in fs):
            return g
    return 1


def _perm_order(kind, p):
    """Order of the permutation group of the given kind over the prime p."""
    if kind == 'psl':
        return p * (p * p - 1) // 2
    if kind == 'pgl':
        return p * (p * p - 1)
    return p * (p - 1)  # agl


def _perm_gens(kind, p):
    """Generators (as permutation tuples) of PSL(2,p), PGL(2,p) or AGL(1,p).

    PSL/PGL act on the projective line {0..p-1, p = infinity}. The maps are
    x -> x+1, x -> s*x and x -> -1/x, with s = nu (PGL) or nu^2 (PSL).
    """
    nu = _prim_root(p)
    if kind == 'agl':
        shift = tuple((x + 1) % p for x in range(p))
        scale = tuple((nu * x) % p for x in range(p))
        return [shift, scale]
    shift = tuple((x + 1) % p for x in range(p)) + (p,)
    s = nu if kind == 'pgl' else (nu * nu) % p
    scale = tuple((s * x) % p for x in range(p)) + (p,)
    inv = (p,) + tuple((-pow(x, p - 2, p)) % p for x in range(1, p)) + (0,)
    return [shift, scale, inv]


def _perm_table(gens, limit=400):
    """Multiplication table of the permutation group generated by gens.

    Closure is by BFS from the identity under right multiplication by generators.
    Returns None if the group exceeds limit elements.
    """
    n = len(gens[0])
    idt = tuple(range(n))
    elems = [idt]
    index = {idt: 0}
    i = 0
    while i < len(elems):
        x = elems[i]
        i += 1
        for g in gens:
            y = tuple(x[j] for j in g)  # x composed with g
            if y not in index:
                if len(elems) >= limit:
                    return None
                index[y] = len(elems)
                elems.append(y)
    T = []
    for a in elems:
        T.append([index[tuple(a[j] for j in b)] for b in elems])
    return T


def _direct_cyclic(T1, k):
    """Table of G x Z_k, with element (a, b) coded as a*k + b."""
    N1 = len(T1)
    N = N1 * k
    T = [[0] * N for _ in range(N)]
    for a in range(N1):
        for b in range(k):
            row = T[a * k + b]
            for c in range(N1):
                base = T1[a][c] * k
                for e in range(k):
                    row[c * k + e] = base + (b + e) % k
    return T


def _build_table(spec):
    """Build the group table described by spec, or return None if it fails."""
    kind = spec[0]
    if kind == 'sd':
        _, m, k, r = spec
        order, mul, _inv = lib.semidirect_group(m, k, r)
        return [[mul(x, g) for g in range(order)] for x in range(order)]
    if kind == 'dc':
        base = _build_table(spec[1])
        if base is None:
            return None
        return _direct_cyclic(base, spec[2])
    return _perm_table(_perm_gens(kind, spec[1]))


def _invs(T):
    """Inverse of each element, using identity index 0: x * inv(x) = 0."""
    N = len(T)
    invs = [0] * N
    for x in range(N):
        row = T[x]
        for g in range(N):
            if row[g] == 0:
                invs[x] = g
                break
    return invs


_SPEC_CACHE = {}


def _specs_for(N):
    """All group specs of order N: semidirect, permutation, and direct-with-cyclic."""
    if N in _SPEC_CACHE:
        return _SPEC_CACHE[N]
    out = []
    for (m, k, r) in _groups(N):
        out.append(('sd', m, k, r))
    for kind, p in _PERM_BASES:
        n0 = _perm_order(kind, p)
        if n0 == N:
            out.append((kind, p))
        elif n0 < N and N % n0 == 0:
            out.append(('dc', (kind, p), N // n0))
    _SPEC_CACHE[N] = out
    return out


# ----------------------------------------------------------------------------
# Bi-Cayley search over a group G of order N.
#
# Vertices A_x and B_y (x, y in G). Edge A_x -- B_{x s} for s in S, |S| = d.
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


def _anneal(N, T, invs, d, D, rng, iters, deadline):
    """Simulated annealing over S = {0, s_1, ..., s_{d-1}} to zero unreached pairs."""
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
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    if cur == 0:
        return S
    return None


def _attempt_spec(N, spec, d, D, rng, deadline):
    """Anneal one group spec. Return (T, S) on success, else None."""
    if time.monotonic() > deadline:
        return None
    T = _build_table(spec)
    if T is None or len(T) != N:
        return None
    invs = _invs(T)
    S = _anneal(N, T, invs, d, D, rng, ITERS, deadline)
    if S is None:
        return None
    return T, S


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])
    best_n = 1

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    Nmax = lib._moore_bound(d, D) // 2   # bi-Cayley graph has 2N vertices
    best_N = best_n // 2                 # need 2N > best_n to improve

    # Window search: only orders in (best_N, best_N + step] are sampled, so
    # the search climbs upward from the current record instead of spending
    # time on orders that are almost certainly out of reach.
    step = WINDOW0
    budget = 1.0
    while time.monotonic() < deadline and best_N < Nmax:
        lo = max(best_N + 1, d)
        hi = min(Nmax, best_N + step)
        cand = [(N, s) for N in range(lo, hi + 1) for s in _specs_for(N)]
        if not cand:
            if hi >= Nmax:
                break
            step += WINDOW0
            continue
        pick = rng.sample(cand, min(len(cand), PICKS))
        pick.sort(key=lambda t: -t[0])   # try larger orders first within the pass
        success = False
        for N, spec in pick:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt_spec(N, spec, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            T, S = res
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            if consider(2 * N, edges):
                best_N = N
                success = True
                break
        if not success:
            budget = min(budget * 1.2, 6.0)
            step += WINDOW0 // 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
