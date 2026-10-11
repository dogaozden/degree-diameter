import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact algebraic families (kept from the parent).
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Representation: a d-regular bipartite graph on n+n vertices.
# Left vertex i (0..n-1) has slots EB[i*d .. i*d+d-1], each holding a right
# index j in 0..n-1 (graph vertex n+j). Regularity on the right is maintained
# by all moves, so the right neighbours of j are the d slots whose value is j.
#
# NEW IDEA: regularity-preserving pair insertion ("edge subdivision growth").
# Pick d edges (u_i, v_i) with pairwise distinct u_i and distinct v_i. Add a
# new left vertex x adjacent to all v_i and a new right vertex y adjacent to
# all u_i, by redirecting each slot of u_i from v_i to y. Every degree stays d,
# so the graph remains d-regular bipartite with n+1 vertices per side. Then
# edge-switch annealing repairs the diameter.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP8 = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)


def _base(N):
    """Bitset rows: row v has only bit v set."""
    W = (N + 63) // 64
    base = np.zeros((N, W), dtype=np.uint64)
    v = np.arange(N, dtype=np.int64)
    base[v, v // 64] = np.uint64(1) << (v % 64).astype(np.uint64)
    return base


def _cost(n, d, EB, D, base):
    """Ordered unreachable pairs within distance D, plus a duplicate-edge penalty."""
    N = 2 * n
    E2 = EB.reshape(n, d)
    order = np.argsort(EB, kind="stable")
    nb = np.empty((N, d), dtype=np.int64)
    nb[:n] = n + E2
    nb[n:] = (order // d).reshape(n, d)
    R = base
    for _ in range(D):
        R = R | np.bitwise_or.reduce(R[nb], axis=1)
    reached = int(_POP8[R.view(np.uint8)].sum())
    srt = np.sort(E2, axis=1)
    dup = int(np.count_nonzero(srt[:, 1:] == srt[:, :-1]))
    return N * N - reached + _PENALTY * dup


def _anneal(n, d, EB, D, base, deadline, steps, rng):
    """Edge-switch annealing on a copy of EB. Returns (success, EB_copy)."""
    EB = EB.copy()
    M = n * d
    cur = _cost(n, d, EB, D, base)
    t0 = time.monotonic()
    tspan = max(1e-3, deadline - t0)
    t = 0
    while cur != 0 and t < steps:
        now = time.monotonic()
        if now > deadline:
            break
        frac = max(t / steps, (now - t0) / tspan)
        temp = 4.0 * (0.02 ** frac) + 0.05
        e1 = rng.randrange(M)
        e2 = rng.randrange(M)
        t += 1
        if EB[e1] == EB[e2]:
            continue
        EB[e1], EB[e2] = EB[e2], EB[e1]
        c2 = _cost(n, d, EB, D, base)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            cur = c2
        else:
            EB[e1], EB[e2] = EB[e2], EB[e1]
    return cur == 0, EB


def _insert(n, d, EB, rng):
    """Regularity-preserving pair insertion. Returns (n+1, new EB) or None."""
    chosen = []
    usedL = set()
    usedR = set()
    tries = 0
    while len(chosen) < d and tries < 2000:
        tries += 1
        e = rng.randrange(n * d)
        u = e // d
        v = int(EB[e])
        if u in usedL or v in usedR:
            continue
        usedL.add(u)
        usedR.add(v)
        chosen.append(e)
    if len(chosen) < d:
        return None
    newEB = np.empty((n + 1) * d, dtype=np.int64)
    newEB[:n * d] = EB
    y = n
    x_slots = []
    for e in chosen:
        x_slots.append(int(EB[e]))
        newEB[e] = y
    newEB[n * d:(n + 1) * d] = np.array(x_slots, dtype=np.int64)
    return n + 1, newEB


def _grow(d, D, rng, deadline, n, EB):
    """Repeatedly insert a pair and repair by annealing; keep the largest valid state."""
    best_n, best_EB = n, EB
    fails = 0
    while time.monotonic() < deadline:
        ins = _insert(n, d, EB, rng)
        if ins is None:
            fails += 1
            continue
        n2, EB2 = ins
        steps = min(4000, 200 * (1 + fails // 3))
        ok, EB3 = _anneal(n2, d, EB2, D, _base(2 * n2), deadline, steps, rng)
        if ok:
            n, EB = n2, EB3
            fails = 0
            if n > best_n:
                best_n, best_EB = n, EB
        else:
            fails += 1
    return best_n, best_EB


def _rr_search(n, d, D, rng, deadline):
    """Anneal a random d-regular bipartite graph on n+n vertices to diameter <= D."""
    EB = np.array([rng.sample(range(n), n) for _ in range(d)], dtype=np.int64).T.copy().ravel()
    ok, EB = _anneal(n, d, EB, D, _base(2 * n), deadline, 10 ** 9, rng)
    return (n, EB) if ok else None


def _rr_arm(d, D, rng, deadline):
    """Ladder over the side size n: grow while annealing succeeds, bisect after failure."""
    moore = 2 * sum((d - 1) ** i for i in range(D))
    cap = 1500
    side = max(d + 1, min(cap, int(0.3 * moore / 2)))
    lo = None
    hi = None
    best = None
    while time.monotonic() < deadline - 0.5:
        now = time.monotonic()
        remaining = deadline - now
        slice_end = min(deadline, now + max(3.0, 0.3 * remaining))
        res = _rr_search(side, d, D, rng, slice_end)
        if res is not None:
            if best is None or res[0] > best[0]:
                best = res
            lo = side
            if side >= cap:
                break
            if hi is None:
                side = int(side * 1.06) + 1
            else:
                if hi - lo <= 1:
                    break
                side = (lo + hi) // 2
        else:
            hi = side
            if lo is None:
                side = int(side * 0.94)
            else:
                if hi - lo <= 1:
                    break
                side = (lo + hi) // 2
        side = min(max(side, d + 1), cap)
    return best


def _edges_from(n, d, EB):
    """Convert the slot representation to (N, edges) with left 0..n-1 and right n..2n-1."""
    E2 = EB.reshape(n, d).tolist()
    return 2 * n, [(i, n + int(j)) for i in range(n) for j in E2[i]]


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} is valid for D >= 2 and optimal for D == 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions (calibration-style cases return immediately).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Seed: a random-regular annealed graph if available, else K_{d,d} in slot form.
    seed_n = None
    seed_EB = None
    if D >= 3 and d >= 2 and time.monotonic() < deadline:
        res = _rr_arm(d, D, rng, start + 0.3 * budget)
        if res is not None:
            seed_n, seed_EB = res
    if seed_n is None:
        seed_n = d
        seed_EB = np.tile(np.arange(d, dtype=np.int64), d)

    # New arm: regularity-preserving pair insertion with annealing repair.
    if D >= 3 and d >= 2 and time.monotonic() < deadline - 1.0:
        gn, gEB = _grow(d, D, rng, deadline, seed_n, seed_EB)
        if gn > seed_n:
            seed_n, seed_EB = gn, gEB

    if seed_n > 0:
        N, edges = _edges_from(seed_n, d, seed_EB)
        consider(N, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
