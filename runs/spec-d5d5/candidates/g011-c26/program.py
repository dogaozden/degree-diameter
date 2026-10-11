import itertools
import math
import random
import time

import lib

# New idea: layered block-voltage lifts.
# A base graph has b "A-blocks" and b "B-blocks". It has d layers. In layer t, A-block i
# is joined to B-block perm[t][i] with group voltage volt[t][i]. Each perm[t] is a bijection,
# so every block vertex has degree exactly d. The lift has 2*b*N vertices. The search
# anneals over the permutations and voltages to make the lift diameter <= D.
# b = 1 reduces to bi-Cayley graphs. b >= 2 gives larger orders from smaller groups.

BLOCKS = (1, 2, 3, 4)       # block counts b tried
ITERS = 2500                # annealing steps per (group, b) try
MAX_GROUPS = 60             # groups tried per attempt


# ----------------------------------------------------------------------------
# Baseline families (fast, always validated).
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
# Groups: semidirect products Z_m x| Z_k of order N (identity encoded as 0).
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


def _mul_table(N, mul):
    """Full multiplication table T[x][g] = x * g for a group on 0..N-1."""
    return [[mul(x, g) for g in range(N)] for x in range(N)]


# ----------------------------------------------------------------------------
# Layered block-voltage lifts.
# ----------------------------------------------------------------------------

def _dupfree(b, d, perm, volt):
    """True if no two darts give the same edge pattern (A-block i, B-block j, voltage g)."""
    seen = set()
    for t in range(d):
        pt = perm[t]
        vt = volt[t]
        for i in range(b):
            key = (i, pt[i], vt[i])
            if key in seen:
                return False
            seen.add(key)
    return True


def _unreached(b, N, d, D, perm, volt, T):
    """Count (source, vertex) pairs not within distance D, using one source per block.

    Left multiplication by G is an automorphism of every lift, so the source A_i(e) for each
    A-block and B_j(e) for each B-block determines all eccentricities.
    """
    n2 = 2 * b * N
    adj = [[] for _ in range(n2)]
    for t in range(d):
        pt = perm[t]
        vt = volt[t]
        for i in range(b):
            j = pt[i]
            g = vt[i]
            base_b = b * N + j * N
            for x in range(N):
                a = i * N + x
                bv = base_b + T[x][g]
                adj[a].append(bv)
                adj[bv].append(a)
    sources = [i * N for i in range(b)] + [b * N + j * N for j in range(b)]
    total = 0
    for src in sources:
        seen = bytearray(n2)
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
        total += n2 - count
    return total


def _anneal(b, N, d, D, T, rng, iters, deadline):
    """Anneal permutations and voltages of a layered lift to zero unreached pairs."""
    perm = [rng.sample(range(b), b) for _ in range(d)]
    volt = [[rng.randrange(N) for _ in range(b)] for _ in range(d)]
    fix = 0
    while not _dupfree(b, d, perm, volt):
        fix += 1
        if fix > 2000:
            return None
        volt[rng.randrange(d)][rng.randrange(b)] = rng.randrange(N)

    cur = _unreached(b, N, d, D, perm, volt, T)
    for it in range(iters):
        if cur == 0:
            return perm, volt
        if time.monotonic() > deadline:
            break
        temp = max(0.2, 3.0 * (1.0 - it / iters))
        if b == 1 or rng.random() < 0.7:
            t = rng.randrange(d)
            i = rng.randrange(b)
            old = volt[t][i]
            new = rng.randrange(N)
            if new == old:
                continue
            volt[t][i] = new
            if not _dupfree(b, d, perm, volt):
                volt[t][i] = old
                continue
            v = _unreached(b, N, d, D, perm, volt, T)
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                volt[t][i] = old
        else:
            t = rng.randrange(d)
            i1, i2 = rng.sample(range(b), 2)
            pt = perm[t]
            pt[i1], pt[i2] = pt[i2], pt[i1]
            if not _dupfree(b, d, perm, volt):
                pt[i1], pt[i2] = pt[i2], pt[i1]
                continue
            v = _unreached(b, N, d, D, perm, volt, T)
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                pt[i1], pt[i2] = pt[i2], pt[i1]
    if cur == 0:
        return perm, volt
    return None


def _materialize(b, N, d, T, perm, volt):
    """Turn a layered lift into (n, edges)."""
    edges = []
    for t in range(d):
        for i in range(b):
            j = perm[t][i]
            g = volt[t][i]
            for x in range(N):
                edges.append((i * N + x, b * N + j * N + T[x][g]))
    return 2 * b * N, edges


def _attempt(b, N, d, D, rng, deadline):
    """Try groups of order N for block count b until one lift has diameter <= D or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, _inv = lib.semidirect_group(m, k, r)
        T = _mul_table(N, mul)
        res = _anneal(b, N, d, D, T, rng, ITERS, deadline)
        if res is not None:
            perm, volt = res
            return _materialize(b, N, d, T, perm, volt)
    return None


def _next_order(b, best_n, moore):
    """Smallest N with 2*b*N > best_n, or None if that already exceeds the Moore bound."""
    N = best_n // (2 * b) + 1
    if 2 * b * N > moore:
        return None
    return N


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
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

    moore = lib._moore_bound(d, D)
    budget = {b: 0.5 for b in BLOCKS}

    while time.monotonic() < deadline:
        any_target = False
        for b in BLOCKS:
            now = time.monotonic()
            if now >= deadline:
                break
            N = _next_order(b, best_n, moore)
            if N is None:
                continue
            any_target = True
            att_deadline = min(deadline, now + budget[b])
            res = _attempt(b, N, d, D, rng, att_deadline)
            if res is None:
                budget[b] *= 1.5
                continue
            n, e = res
            consider(n, e)
        if not any_target:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
