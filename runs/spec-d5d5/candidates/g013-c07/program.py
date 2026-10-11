import itertools
import math
import random
import time

import lib

# ----------------------------------------------------------------------------
# Multi-orbit voltage lifts (new in this version).
#
# Parent searched only bi-Cayley graphs: one vertex orbit A and one orbit B,
# each a copy of a group G. Here the base graph has b vertices on each side,
# with a b x b multiplicity matrix M (every row and column sums to d). Cell
# (i, j) carries M[i][j] distinct voltages g, giving edges
#     A_{i,x} -- B_{j, x*g}   for x in G.
# Each side then has b orbits of size |G|, so the order is 2*b*|G|. The b = 1
# case is the parent's bi-Cayley search. Since G acts on each orbit by left
# multiplication, eccentricities from one representative per orbit (2b sources
# in total) decide the diameter.
# ----------------------------------------------------------------------------

ITERS = 1000        # annealing steps per attempt
T_HOT = 2.0
T_COLD = 0.2
SLICE = 2.5         # seconds per attempt
BS = [2, 3, 4, 5, 6, 1]


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


def _random_matrix(b, d, rng):
    """b x b nonnegative integer matrix with all row and column sums equal to d (sum of d permutations)."""
    M = [[0] * b for _ in range(b)]
    for _ in range(d):
        p = list(range(b))
        rng.shuffle(p)
        for i in range(b):
            M[i][p[i]] += 1
    return M


def _build_nb(b, N, T, cells):
    """Adjacency lists of the lift. A vertices are i*N + x; B vertices are b*N + j*N + y."""
    V = 2 * b * N
    nb = [[] for _ in range(V)]
    for i in range(b):
        for j in range(b):
            base = b * N + j * N
            for g in cells[i][j]:
                for x in range(N):
                    a = i * N + x
                    c = base + T[x][g]
                    nb[a].append(c)
                    nb[c].append(a)
    return nb


def _cost(b, N, D, nb):
    """Total number of (source, vertex) pairs not within distance D, over one source per orbit."""
    V = len(nb)
    sources = [i * N for i in range(b)] + [b * N + j * N for j in range(b)]
    total = 0
    for s in sources:
        seen = bytearray(V)
        seen[s] = 1
        frontier = [s]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in nb[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += V - cnt
    return total


def _anneal(b, N, D, T, M, rng, deadline):
    """Anneal the voltage sets so the lift has diameter <= D. Returns cells or None."""
    cells = [[rng.sample(range(N), M[i][j]) for j in range(b)] for i in range(b)]
    active = [(i, j) for i in range(b) for j in range(b) if M[i][j] > 0]
    nb = _build_nb(b, N, T, cells)
    cur = _cost(b, N, D, nb)
    for it in range(ITERS):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        i, j = rng.choice(active)
        lst = cells[i][j]
        t = rng.randrange(len(lst))
        g = rng.randrange(N)
        if g in lst:
            continue
        old = lst[t]
        lst[t] = g
        nb2 = _build_nb(b, N, T, cells)
        v = _cost(b, N, D, nb2)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
            nb = nb2
        else:
            lst[t] = old
    return cells if cur == 0 else None


def _try(b, N, d, D, rng, deadline):
    """One attempt at order 2*b*N: random group, random base matrix, anneal voltages."""
    groups = _groups(N)
    if not groups:
        return None
    m, k, r = rng.choice(groups)
    _, mul, _ = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    M = _random_matrix(b, d, rng)
    cells = _anneal(b, N, D, T, M, rng, deadline)
    if cells is None:
        return None
    edges = []
    for i in range(b):
        for j in range(b):
            base = b * N + j * N
            for g in cells[i][j]:
                for x in range(N):
                    edges.append((i * N + x, base + T[x][g]))
    return 2 * b * N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
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

    Moore = lib._moore_bound(d, D)

    # Per-b search state: N is the current order parameter, lo/hi bracket the
    # largest successful and smallest failed N seen so far.
    states = {}
    for b in BS:
        N0 = max(d, (best[0] + 2 * b) // (2 * b))
        if 2 * b * N0 > Moore:
            continue
        states[b] = {'N': N0, 'lo': 0, 'hi': None, 'done': False}

    while time.monotonic() < deadline and any(not s['done'] for s in states.values()):
        progressed = False
        for b in BS:
            if b not in states or states[b]['done']:
                continue
            if time.monotonic() >= deadline:
                break
            st = states[b]
            N = st['N']
            att_deadline = min(deadline, time.monotonic() + SLICE)
            res = _try(b, N, d, D, rng, att_deadline)
            progressed = True
            ok = res is not None
            if ok:
                consider(*res)
                st['lo'] = max(st['lo'], N)
            else:
                st['hi'] = N if st['hi'] is None else min(st['hi'], N)

            lo, hi = st['lo'], st['hi']
            if ok:
                nxt = int(N * 1.08) + 1 if hi is None else (lo + hi) // 2
            else:
                nxt = max(d, int(N * 0.92)) if lo == 0 else (lo + hi) // 2

            if 2 * b * nxt > Moore:
                nxt = Moore // (2 * b)
            if hi is not None and hi - lo <= 1:
                st['done'] = True
                continue
            if nxt <= lo:
                nxt = lo + 1
            if hi is not None and nxt >= hi:
                st['done'] = True
                continue
            if 2 * b * nxt > Moore or nxt < d:
                st['done'] = True
                continue
            st['N'] = nxt
        if not progressed:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
