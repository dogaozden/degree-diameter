import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact / near-exact families used as cheap baselines.
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
# Bold new construction: random d-regular bipartite graphs repaired by
# simulated annealing on double edge swaps.
#
# Vertices 0..s-1 are side A, s..2s-1 are side B. Every vertex has degree d,
# so the degree bound holds by construction and bipartiteness is automatic.
# The cost is the number of unordered vertex pairs at distance > D, computed
# exactly with packed bitsets (numpy uint64) over the whole graph. A cost of 0
# means the diameter is at most D. Random regular graphs already come close to
# this at sizes well above the lift records, and the annealing removes the few
# remaining defects. Every success is re-checked with lib.is_valid before use.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)
_MOVES = 3000


def _bad_pairs(nb, n, D):
    """Number of unordered vertex pairs at distance > D in the graph with neighbour table nb (n x d)."""
    d = nb.shape[1]
    W = (n + 63) // 64
    idx = np.arange(n, dtype=np.int64)
    R = np.zeros((n, W), dtype=np.uint64)
    R[idx, idx // 64] = np.left_shift(np.uint64(1), (idx % 64).astype(np.uint64))
    for _ in range(D):
        NR = R.copy()
        for l in range(d):
            NR |= R[nb[:, l]]
        if np.array_equal(NR, R):
            break
        R = NR
    total = int(_POP8[R.view(np.uint8)].sum())
    return (n * n - total) // 2


def _random_regular_bip(s, d, rng):
    """Random simple d-regular bipartite graph on sides of size s, as an (2s x d) neighbour table, or None."""
    if d > s:
        return None
    nb = np.empty((2 * s, d), dtype=np.int64)
    forb = [set() for _ in range(s)]
    for l in range(d):
        perm = list(range(s))
        rng.shuffle(perm)
        ok = False
        for _ in range(50 * s + 100):
            bads = [i for i in range(s) if perm[i] in forb[i]]
            if not bads:
                ok = True
                break
            i = bads[rng.randrange(len(bads))]
            j = rng.randrange(s)
            perm[i], perm[j] = perm[j], perm[i]
        if not ok:
            return None
        for i in range(s):
            forb[i].add(perm[i])
            nb[i, l] = s + perm[i]
            nb[s + perm[i], l] = i
    return nb


def _anneal(nb, s, D, rng, moves, deadline):
    """Repair nb in place by double edge swaps until the cost (bad pairs) is 0. Returns True on success."""
    d = nb.shape[1]
    n = 2 * s
    cur = _bad_pairs(nb, n, D)
    for t in range(moves):
        if cur == 0:
            return True
        if (t & 63) == 0 and time.monotonic() > deadline:
            return False
        a1 = rng.randrange(s)
        a2 = rng.randrange(s)
        if a1 == a2:
            continue
        s1 = rng.randrange(d)
        s2 = rng.randrange(d)
        b1 = int(nb[a1, s1])
        b2 = int(nb[a2, s2])
        if b1 == b2:
            continue
        if (nb[a1] == b2).any() or (nb[a2] == b1).any():
            continue
        save = (nb[a1].copy(), nb[a2].copy(), nb[b1].copy(), nb[b2].copy())
        t1 = int(np.flatnonzero(nb[b1] == a1)[0])
        t2 = int(np.flatnonzero(nb[b2] == a2)[0])
        nb[a1, s1] = b2
        nb[a2, s2] = b1
        nb[b1, t1] = a2
        nb[b2, t2] = a1
        new = _bad_pairs(nb, n, D)
        delta = new - cur
        temp = 1.0 * (1.0 - t / moves) + 0.05
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cur = new
        else:
            nb[a1] = save[0]
            nb[a2] = save[1]
            nb[b1] = save[2]
            nb[b2] = save[3]
    return cur == 0


def _attempt(d, D, s, rng, deadline):
    """Try to build a valid d-regular bipartite graph of order 2s. Returns (n, edges) or None."""
    nb = _random_regular_bip(s, d, rng)
    if nb is None:
        return None
    if not _anneal(nb, s, D, rng, _MOVES, deadline):
        return None
    edges = [(i, int(nb[i, l])) for i in range(s) for l in range(d)]
    return 2 * s, edges


def _grow_search(d, D, rng, deadline, s0, consider):
    """Climb the side size s while attempts succeed; back off the step on repeated failure."""
    s = max(d, s0)
    step = 16
    last_ok = None
    fails = 0
    while time.monotonic() < deadline:
        res = _attempt(d, D, s, rng, deadline)
        if res is not None:
            consider(res[0], res[1])
            last_ok = s
            s = s + step
            fails = 0
        else:
            fails += 1
            if last_ok is None:
                s = max(d, s - 8)
            else:
                if fails >= 2:
                    step = max(1, step // 2)
                    fails = 0
                s = last_ok + step


def build(d, D, seed, time_limit):
    start = time.monotonic()
    # Use ~90% of the limit, keeping a 5 s safety margin.
    budget = max(1.0, min(0.90 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        cyc = (n, [(i, (i + 1) % n) for i in range(n)])
        if lib.is_valid(cyc[0], cyc[1], d, D):
            return cyc

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions: return immediately for calibration-style cases.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() < start + 0.3 * budget:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: repaired random regular bipartite graphs.
    if D >= 3:
        s0 = max(d, best_n // 2 + 1)
        try:
            _grow_search(d, D, rng, deadline, s0, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
