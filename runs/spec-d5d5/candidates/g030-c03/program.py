import itertools
import math
import random
import time

import lib

ITERS = 700          # annealing steps per (group, dart assignment) try
T_HOT = 1.5          # initial annealing temperature (unreached-pair units)
T_COLD = 0.15        # final annealing temperature
MAX_GROUPS = 8       # groups tried per (b, N) attempt
MAX_B = 6            # maximum number of base orbits per side
BASE_BUDGET = 0.4    # seconds per (b, N) attempt in the first pass
CAP_FACTOR = 1.2     # search only orders up to this factor above the best found


# ----------------------------------------------------------------------------
# Baseline families (kept from the parent; cheap and always valid when they pass).
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
# NEW: multi-orbit bi-Cayley lifts ("permutation-sum voltage graphs").
#
# Base graph: b vertices A_0..A_{b-1} and b vertices B_0..B_{b-1}. The lift over a
# group G of order N has vertices A(i,x), B(j,y) for x, y in G (2bN in total).
# The base is d-regular on both sides, built as the sum of d permutation matrices:
# for each k in 0..d-1 and each i, there is a dart (i, sigma_k(i), g_{k,i}), and
# the dart lifts to the edges A(i,x) -- B(sigma_k(i), x g_{k,i}) for all x.
#
# Left multiplication by z is an automorphism, so eccentricities only need to be
# checked from the 2b representatives A(i,0) and B(j,0). This turns the search
# into a joint search over group, permutations and voltages, with orders
# 2bN for every b, not only b = 1 as in the parent.
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


def _lists(b, invs, sig, gs):
    """Adjacency data of the base darts: out[i] = [(j, g)], inn[j] = [(i, g^-1)]."""
    out = [[] for _ in range(b)]
    inn = [[] for _ in range(b)]
    for k in range(len(sig)):
        row_s, row_g = sig[k], gs[k]
        for i in range(b):
            j, g = row_s[i], row_g[i]
            out[i].append((j, g))
            inn[j].append((i, invs[g]))
    return out, inn


def _unreached(b, N, T, out, inn, D):
    """Count (representative, vertex) pairs not within distance D, over all 2b representatives."""
    bn = b * N
    total_v = 2 * bn
    sources = [i * N for i in range(b)] + [bn + j * N for j in range(b)]
    total = 0
    for src in sources:
        seen = bytearray(total_v)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < bn:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in out[i]:
                        v = bn + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - bn, N)
                    row = T[y]
                    for i, h in inn[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += total_v - count
    return total


def _darts_distinct(b, d, sig, gs):
    """True if no two darts coincide as (i, j, g), so the lift is simple and d-regular."""
    seen = set()
    for k in range(d):
        for i in range(b):
            t = (i, sig[k][i], gs[k][i])
            if t in seen:
                return False
            seen.add(t)
    return True


def _anneal(b, N, T, invs, d, D, rng, iters, deadline):
    """Anneal over permutations sigma_k and voltages g_{k,i} until all representatives reach within D."""
    sig = None
    gs = None
    for _ in range(200):
        sig = [rng.sample(range(b), b) for _ in range(d)]
        gs = [[rng.randrange(N) for _ in range(b)] for _ in range(d)]
        if _darts_distinct(b, d, sig, gs):
            break
    else:
        return None
    out, inn = _lists(b, invs, sig, gs)
    cur = _unreached(b, N, T, out, inn, D)
    for it in range(iters):
        if cur == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        k = rng.randrange(d)
        if b > 1 and rng.random() < 0.3:
            i1, i2 = rng.sample(range(b), 2)
            nsig = [row[:] for row in sig]
            nsig[k][i1], nsig[k][i2] = nsig[k][i2], nsig[k][i1]
            ngs = gs
        else:
            i = rng.randrange(b)
            g = rng.randrange(N)
            if g == gs[k][i]:
                continue
            nsig = sig
            ngs = [row[:] for row in gs]
            ngs[k][i] = g
        if not _darts_distinct(b, d, nsig, ngs):
            continue
        nout, ninn = _lists(b, invs, nsig, ngs)
        v = _unreached(b, N, T, nout, ninn, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            sig, gs, cur = nsig, ngs, v
    if cur == 0:
        return sig, gs
    return None


def _attempt(b, N, d, D, rng, deadline):
    """Try groups of order N for base size b; return (T, sig, gs) on success, else None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        res = _anneal(b, N, T, invs, d, D, rng, ITERS, deadline)
        if res is not None:
            sig, gs = res
            return T, sig, gs
    return None


def _edges_from(b, d, N, T, sig, gs):
    """Expand a base solution into (n, edges): A(i,x) = i*N + x, B(j,y) = b*N + j*N + y."""
    bn = b * N
    edges = []
    for k in range(d):
        for i in range(b):
            j = sig[k][i]
            g = gs[k][i]
            for x in range(N):
                edges.append((i * N + x, bn + j * N + T[x][g]))
    return 2 * bn, edges


def _candidates(lo, cap, moore, rng):
    """Even orders V = 2bN in (lo, cap] with b in 1..MAX_B, sorted by V, shuffled within V."""
    cands = []
    top = min(cap, moore)
    V = lo + 1 if (lo + 1) % 2 == 0 else lo + 2
    while V <= top:
        half = V // 2
        group = []
        for b in range(1, MAX_B + 1):
            if half % b:
                continue
            N = half // b
            if N >= 2:
                group.append((V, b, N))
        rng.shuffle(group)
        cands.extend(group)
        V += 2
    return cands


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

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
    budget = BASE_BUDGET
    while time.monotonic() < deadline:
        lo = best[0]
        cap = int(CAP_FACTOR * lo) + 8
        cands = _candidates(lo, cap, moore, rng)
        if not cands:
            break
        found = False
        for V, b, N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            if V <= best[0]:
                continue
            att_deadline = min(deadline, now + budget)
            res = _attempt(b, N, d, D, rng, att_deadline)
            if res is None:
                continue
            T, sig, gs = res
            n, edges = _edges_from(b, d, N, T, sig, gs)
            consider(n, edges)
            found = True
        if not found:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
