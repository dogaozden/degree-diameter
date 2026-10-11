import itertools
import math
import random
import time

import lib

MAX_GROUPS = 8          # groups tried per (base, order) attempt
ITERS = 1500            # annealing steps per attempt
T_HOT = 2.0             # initial annealing temperature (unreached-pair units)
T_COLD = 0.1            # final annealing temperature
WINDOW = 12             # lift orders tried above the current floor per pass
MAXM = 300              # cap on group order (keeps group tables small)
BUDGET_START = 0.5      # seconds per (a, m) attempt in the first pass
BUDGET_CAP = 3.0        # cap on per-attempt seconds as passes fail
FLOOR_START = 0.48      # first target: total order >= FLOOR_START * Moore bound
FLOOR_STEP = 0.03       # lower the floor by this after a failed pass

_GROUP_CACHE = {}


# ----------------------------------------------------------------------------
# Structured fallbacks (always checked with lib.is_valid before use).
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
# Voltage lifts of small bipartite base multigraphs over non-abelian groups.
#
# Base: `a` A-vertices and `a` B-vertices; each A and B vertex carries exactly
# d darts, so the lift is d-regular. Dart (u, v, g) joins (u, x) to (a+v, x*g)
# for every x in the group of order `order`. Left multiplication by any group
# element is an automorphism, so the diameter is decided by BFS from the
# identity of each of the 2a fibres.
#
# Vertex id: block * order + x, with A-blocks 0..a-1 and B-blocks a..2a-1.
# ----------------------------------------------------------------------------

def _groups(order):
    """Return semidirect parameters (m, k, r) with m*k = order, giving Z_m x|_r Z_k."""
    if order in _GROUP_CACHE:
        return _GROUP_CACHE[order]
    out = []
    for k in range(1, order + 1):
        if order % k:
            continue
        m = order // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    _GROUP_CACHE[order] = out
    return out


def _random_base(a, d, rng):
    """Random d-regular bipartite multigraph on a+a vertices as a list of (u, v) darts; connected or None."""
    for _ in range(40):
        pairs = []
        parent = list(range(2 * a))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        for _ in range(d):
            perm = list(range(a))
            rng.shuffle(perm)
            for u in range(a):
                v = perm[u]
                pairs.append((u, v))
                parent[find(u)] = find(a + v)
        if len({find(x) for x in range(2 * a)}) == 1:
            return pairs
    return None


def _init_voltages(pairs, order, rng):
    """Random voltages; darts sharing a base pair get distinct voltages (no duplicate edges)."""
    byp = {}
    for i, p in enumerate(pairs):
        byp.setdefault(p, []).append(i)
    vol = [0] * len(pairs)
    for p, idxs in byp.items():
        gs = rng.sample(range(order), len(idxs))
        for i, g in zip(idxs, gs):
            vol[i] = g
    return vol, byp


def _unreached(a, order, T, pairs, vol, D):
    """Total count of (fibre-source, vertex) pairs not within distance D, over all 2a fibre identities."""
    N2 = 2 * a * order
    adj = [[] for _ in range(N2)]
    for (u, v), g in zip(pairs, vol):
        bv = (a + v) * order
        for x in range(order):
            p = u * order + x
            q = bv + T[x][g]
            adj[p].append(q)
            adj[q].append(p)
    total = 0
    for s in range(2 * a):
        src = s * order
        seen = bytearray(N2)
        seen[src] = 1
        frontier = [src]
        reached = 1
        for _ in range(D):
            nxt = []
            for p in frontier:
                for q in adj[p]:
                    if not seen[q]:
                        seen[q] = 1
                        nxt.append(q)
            if not nxt:
                break
            reached += len(nxt)
            frontier = nxt
        total += N2 - reached
    return total


def _anneal(a, order, T, pairs, vol, sib, D, rng, iters, deadline):
    """Simulated annealing over dart voltages to drive the unreached count to zero."""
    cur = _unreached(a, order, T, pairs, vol, D)
    L = len(pairs)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i = rng.randrange(L)
        c = rng.randrange(order)
        if any(vol[j] == c for j in sib[i]):
            continue
        old = vol[i]
        if c == old:
            continue
        vol[i] = c
        new = _unreached(a, order, T, pairs, vol, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
            cur = new
        else:
            vol[i] = old
    return list(vol) if cur == 0 else None


def _attempt(a, order, d, D, rng, deadline):
    """Try groups of the given order and random bases until a valid lift is found or time runs out."""
    groups = list(_groups(order))
    rng.shuffle(groups)
    for (m, k, r) in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        base = _random_base(a, d, rng)
        if base is None:
            continue
        _, mul, _inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(order)] for x in range(order)]
        vol, byp = _init_voltages(base, order, rng)
        sib = [[j for j in byp[base[i]] if j != i] for i in range(len(base))]
        res = _anneal(a, order, T, base, vol, sib, D, rng, ITERS, deadline)
        if res is not None:
            return base, res, T
    return None


def _edges(a, order, T, base, vol):
    """Expand a voltage assignment into the lifted edge list."""
    E = []
    for (u, v), g in zip(base, vol):
        bv = (a + v) * order
        for x in range(order):
            E.append((u * order + x, bv + T[x][g]))
    return 2 * a * order, E


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.3, 0.8 * time_limit - 1.5)
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

    if D == 1:
        consider(2, [(0, 1)])
        return best

    # Complete bipartite K_{d,d}: diameter 2, always valid for D >= 2.
    consider(2 * d, [(i, d + j) for i in range(d) for j in range(d)])

    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
        except Exception:
            pass

    if d < 2 or D < 2:
        return best

    moore = lib._moore_bound(d, D)
    floor = FLOOR_START
    budget = BUDGET_START

    while time.monotonic() < deadline:
        lo = max(best_n + 1, int(floor * moore))
        cands = []
        for a in (2, 3):
            mlo = -(-lo // (2 * a))
            mhi = min(MAXM, moore // (2 * a), mlo + WINDOW)
            for m in range(max(mlo, d), mhi + 1):
                cands.append((a, m))
        if not cands:
            if floor <= 0:
                break
            floor = max(0.0, floor - FLOOR_STEP)
            continue

        rng.shuffle(cands)
        success = False
        for a, m in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(a, m, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            base, vol, T = res
            n, E = _edges(a, m, T, base, vol)
            consider(n, E)
            success = True
            break

        if not success:
            budget = min(BUDGET_CAP, budget * 1.5)
            floor = max(0.0, floor - FLOOR_STEP)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
