import itertools
import math
import random
import time

import lib

MAX_GROUPS = 8          # groups tried per (order N, block pattern) attempt
ITERS = 400             # annealing steps per group
T_HOT = 1.5             # initial annealing temperature (unreached-pair units)
T_COLD = 0.15           # final annealing temperature
WINDOW_FRAC = 0.9       # search N in [WINDOW_FRAC * top, top] first
BUDGET_START = 2.5      # seconds per N attempt in the first pass
BUDGET_CAP = 8.0        # cap on per-attempt seconds as passes fail
GROUP_MOVE_PROB = 0.5   # chance a move proposes a product of two set elements
PARTS2_SHARE = 0.8      # fraction of search time for the 2x2 block-lift family


# ----------------------------------------------------------------------------
# Fast baseline families (always checked with lib.is_valid before use).
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Block-lift search over semidirect products Z_m x| Z_k.
#
# Construction (new family): a "parts" A_0..A_{a-1} and B_0..B_{a-1}, each a
# copy of G (|G| = N). A block (i, j) carries a set of distinct group elements
# D_ij; the lift has edges  A_i,x -- B_j,x*g  for every g in D_ij, every x in G.
# Every A-vertex has degree sum_j |D_ij| and every B-vertex has degree
# sum_i |D_ij|. With a = 2 we use the regular pattern
#     [[c, d-c], [d-c, c]],  1 <= c <= d/2,
# giving 4N vertices (a = 1 is the parent's bi-Cayley family, 2N vertices).
#
# Left multiplication by h is an automorphism that fixes each part, so the
# diameter is at most D iff every part's identity vertex reaches all 2aN
# vertices within D steps. The cost sums the unreached counts from those 2a
# sources; annealing drives it to zero.
# ----------------------------------------------------------------------------

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


def _unreached(a, N, T, invs, state, D):
    """Total unreached (source, vertex) pairs over the 2a part-identity sources."""
    nparts = 2 * a
    size = nparts * N
    fromA = [[] for _ in range(a)]
    intoB = [[] for _ in range(a)]
    for i, j, gs in state:
        fromA[i].append((a + j, gs))
        intoB[j].append((i, [invs[g] for g in gs]))
    total = 0
    for p in range(nparts):
        src = p * N
        seen = bytearray(size)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                q, x = divmod(u, N)
                row = T[x]
                if q < a:
                    for tp, gs in fromA[q]:
                        base = tp * N
                        for g in gs:
                            v = base + row[g]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
                else:
                    for ip, hs in intoB[q - a]:
                        base = ip * N
                        for h in hs:
                            v = base + row[h]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += size - count
    return total


def _anneal(a, N, T, invs, cnts, D, rng, iters, deadline):
    """Simulated annealing over the block element sets; returns state or None."""
    state = [[i, j, rng.sample(range(N), cnt)] for i, j, cnt in cnts]
    cur = _unreached(a, N, T, invs, state, D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        blk = state[rng.randrange(len(state))][2]
        pos = rng.randrange(len(blk))
        if rng.random() < GROUP_MOVE_PROB:
            allg = [g for _, _, gs in state for g in gs]
            c = T[rng.choice(allg)][rng.choice(allg)]
        else:
            c = rng.randrange(N)
        if c in blk:
            continue
        old = blk[pos]
        blk[pos] = c
        v = _unreached(a, N, T, invs, state, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            blk[pos] = old
    if cur == 0:
        return [(i, j, list(gs)) for i, j, gs in state]
    return None


def _attempt(a, N, d, D, rng, deadline):
    """Try groups of order N for a random block pattern; return (T, state) or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    if a == 1:
        cnts = [(0, 0, d)]
    else:
        c = rng.randint(1, d // 2)
        cnts = [(0, 0, c), (0, 1, d - c), (1, 0, d - c), (1, 1, c)]
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        state = _anneal(a, N, T, invs, cnts, D, rng, ITERS, deadline)
        if state is not None:
            return T, state
    return None


def _search(d, D, a, rng, deadline, cur_best, consider):
    """Search block lifts with a parts per side, descending window with growing budgets."""
    top = lib.moore_bound(d, D) // (2 * a)
    if top < d + 1:
        return
    bestN = cur_best() // (2 * a)
    floor = max(d + 1, int(WINDOW_FRAC * top))
    budget = BUDGET_START
    while time.monotonic() < deadline:
        lo = max(floor, bestN + 1)
        cands = list(range(lo, top + 1))
        if not cands:
            break
        rng.shuffle(cands)
        success = False
        for N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(a, N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            T, state = res
            edges = []
            for i, j, gs in state:
                for x in range(N):
                    row = T[x]
                    for g in gs:
                        edges.append((i * N + x, (a + j) * N + row[g]))
            if consider(2 * a * N, edges):
                bestN = N
                success = True
                break
        if not success:
            if budget < BUDGET_CAP:
                budget = min(BUDGET_CAP, budget * 1.5)
            elif floor > d + 1:
                floor -= 1


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

    if D == 1:
        consider(2, [(0, 1)])
        return best

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

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

    # Main bold family: 2x2 block lifts (4N vertices), then the bi-Cayley family.
    t_mid = start + PARTS2_SHARE * (deadline - start)
    _search(d, D, 2, rng, t_mid, lambda: best[0], consider)
    _search(d, D, 1, rng, deadline, lambda: best[0], consider)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
