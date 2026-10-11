import itertools
import math
import random
import time

import lib

KMAX = 4                # max base vertices per side in the voltage lift
MAX_GROUPS = 10         # groups tried per (k, N) attempt
ITERS = 700             # annealing steps per (group, base structure) try
T_HOT = 1.5
T_COLD = 0.15
GROUP_MOVE_PROB = 0.5   # chance a label move proposes a product of two labels
BUDGET_START = 1.2      # seconds per (k, N) attempt in the first pass
BUDGET_CAP = 6.0
WINDOW_START = 0.95     # search N in [WINDOW_START * top, top] first
WINDOW_MIN = 0.6

_GROUP_CACHE = {}


# ----------------------------------------------------------------------------
# Safe baseline families.
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
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Voltage lifts over semidirect groups with k base vertices per side.
#
# Vertices A_{i,x} (index i*N + x) and B_{j,y} (index (k+j)*N + y).
# The base is d "darts" per base-vertex side: for t in 0..d-1 and i in 0..k-1,
# dart (i, sig[t][i], lab[t][i]) joins A_{i,x} to B_{j, x*g} for all x.
# sig[t] is a permutation of range(k), so every A and B vertex has degree d.
# Darts with the same (i, j) must have distinct labels so the lift is simple.
# Left multiplication is an automorphism, so the diameter is decided by
# eccentricities of A_{i,e} and B_{j,e}.
# ----------------------------------------------------------------------------

def _group_tables(gm, gk, gr):
    key = (gm, gk, gr)
    hit = _GROUP_CACHE.get(key)
    if hit is None:
        if len(_GROUP_CACHE) > 40:
            _GROUP_CACHE.clear()
        N, mul, inv = lib.semidirect_group(gm, gk, gr)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        INV = [inv(g) for g in range(N)]
        hit = (T, INV)
        _GROUP_CACHE[key] = hit
    return hit


def _groups(N):
    out = []
    for gk in range(1, N + 1):
        if N % gk:
            continue
        gm = N // gk
        for gr in range(gm):
            if math.gcd(gr, gm) == 1 and pow(gr, gk, gm) == 1 % gm:
                out.append((gm, gk, gr))
    return out


def _valid_state(k, d, sig, lab):
    """Darts with the same base pair (i, j) must carry distinct labels."""
    seen = set()
    for t in range(d):
        for i in range(k):
            key = (i, sig[t][i], lab[t][i])
            if key in seen:
                return False
            seen.add(key)
    return True


def _darts(k, d, sig, lab, INV):
    dA = [[] for _ in range(k)]
    dB = [[] for _ in range(k)]
    for t in range(d):
        for i in range(k):
            j = sig[t][i]
            g = lab[t][i]
            dA[i].append((j, g))
            dB[j].append((i, INV[g]))
    return dA, dB


def _unreached(N, k, D, T, dA, dB):
    """Count (source, vertex) pairs at distance > D, over base sources A_{i,e} and B_{j,e}."""
    kN = k * N
    n = 2 * kN
    total = 0
    sources = [i * N for i in range(k)] + [kN + j * N for j in range(k)]
    for src in sources:
        seen = bytearray(n)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < kN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in dA[i]:
                        v = kN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - kN, N)
                    row = T[y]
                    for i, h in dB[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            cnt += len(nxt)
            if not nxt:
                break
            frontier = nxt
        total += n - cnt
    return total


def _anneal(N, k, d, D, T, INV, rng, iters, deadline):
    sig = None
    for _ in range(300):
        cs = [list(range(k))] + [rng.sample(range(k), k) for _ in range(d - 1)]
        cl = [[rng.randrange(N) for _ in range(k)] for _ in range(d)]
        if _valid_state(k, d, cs, cl):
            sig, lab = cs, cl
            break
    if sig is None:
        return None
    dA, dB = _darts(k, d, sig, lab, INV)
    cur = _unreached(N, k, D, T, dA, dB)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            return None
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        nsig = [row[:] for row in sig]
        nlab = [row[:] for row in lab]
        if k >= 2 and rng.random() < 0.3:
            t = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            nsig[t][i1], nsig[t][i2] = nsig[t][i2], nsig[t][i1]
        else:
            t = rng.randrange(d)
            i = rng.randrange(k)
            if rng.random() < GROUP_MOVE_PROB:
                a = lab[rng.randrange(d)][rng.randrange(k)]
                b = lab[rng.randrange(d)][rng.randrange(k)]
                g = T[a][b]
            else:
                g = rng.randrange(N)
            nlab[t][i] = g
        if not _valid_state(k, d, nsig, nlab):
            continue
        ndA, ndB = _darts(k, d, nsig, nlab, INV)
        v = _unreached(N, k, D, T, ndA, ndB)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            sig, lab, cur = nsig, nlab, v
    if cur == 0:
        return sig, lab
    return None


def _attempt(k, N, d, D, rng, deadline):
    groups = _groups(N)
    rng.shuffle(groups)
    for gm, gk, gr in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        T, INV = _group_tables(gm, gk, gr)
        res = _anneal(N, k, d, D, T, INV, rng, ITERS, deadline)
        if res is not None:
            sig, lab = res
            return k, N, sig, lab, T
    return None


def _lift_edges(k, N, d, sig, lab, T):
    E = []
    for t in range(d):
        for i in range(k):
            j = sig[t][i]
            g = lab[t][i]
            a0 = i * N
            b0 = (k + j) * N
            for x in range(N):
                E.append((a0 + x, b0 + T[x][g]))
    return 2 * k * N, E


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + max(0.5, min(0.85 * time_limit, time_limit - 5.0))
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

    consider(2, [(0, 1)])
    consider(*lib.haar_graph(d, range(d)))

    # Record-matching case for D = 3.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    M = lib.moore_bound(d, D)
    frac = WINDOW_START
    budget = BUDGET_START

    while time.monotonic() < deadline:
        cands = []
        for k in range(1, KMAX + 1):
            top = M // (2 * k)
            if top < d:
                continue
            lo = max(d, int(frac * top), best_n // (2 * k) + 1)
            for N in range(lo, top + 1):
                if 2 * k * N > best_n:
                    cands.append((k, N))
        if not cands:
            if frac <= WINDOW_MIN:
                break
            frac = max(WINDOW_MIN, frac - 0.05)
            continue
        rng.shuffle(cands)
        success = False
        for k, N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            att = min(deadline, now + budget)
            res = _attempt(k, N, d, D, rng, att)
            if res is None:
                continue
            kk, NN, sig, lab, T = res
            n, e = _lift_edges(kk, NN, d, sig, lab, T)
            consider(n, e)
            success = True
            break
        if not success:
            if budget < BUDGET_CAP:
                budget = min(BUDGET_CAP, budget * 1.5)
            elif frac > WINDOW_MIN:
                frac = max(WINDOW_MIN, frac - 0.05)

    return best
