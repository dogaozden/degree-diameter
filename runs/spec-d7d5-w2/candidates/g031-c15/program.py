import math
import random
import time

import numpy as np

import lib

_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)


# ----------------------------------------------------------------------------
# Exact baseline: incidence graph of PG(2, q), diameter 3.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New family: grow-and-repair random bipartite regular graphs.
#
# State: side size s, and d-regular bipartite edge list (EA[e] in A, EB[e] in B),
# with A = 0..s-1 and B = 0..s-1. Every vertex has degree exactly d.
#
# Repair: double-edge switches (degree-preserving) annealed to minimise the
# number of ordered vertex pairs at distance > D (computed with packed bitsets).
#
# Growth: insert one A-vertex and one B-vertex by removing a matching of d-1
# edges and reconnecting them to the new vertices, then re-anneal. Accept only
# if the annealed graph has zero defects. The last accepted graph is kept.
# Every returned graph is checked with lib.is_valid, with K_{d,d} as fallback.
# ----------------------------------------------------------------------------

def _pack(s, d, EA, EB):
    """Neighbour table NB (2s x d), slot indices, and A-B adjacency matrix."""
    E = s * d
    NB = np.empty((2 * s, d), dtype=np.int64)
    SA = np.empty(E, dtype=np.int64)
    SB = np.empty(E, dtype=np.int64)
    adjm = np.zeros((s, s), dtype=bool)
    ca = [0] * s
    cb = [0] * s
    for e in range(E):
        a = int(EA[e])
        b = int(EB[e])
        SA[e] = ca[a]
        NB[a, ca[a]] = s + b
        ca[a] += 1
        SB[e] = cb[b]
        NB[s + b, cb[b]] = a
        cb[b] += 1
        adjm[a, b] = True
    return NB, SA, SB, adjm


def _cost(NB, D):
    """Number of ordered vertex pairs at distance > D (bitset ball expansion)."""
    N = NB.shape[0]
    R = np.packbits(np.eye(N, dtype=np.uint8), axis=1)
    for _ in range(D):
        R2 = R | np.bitwise_or.reduce(R[NB], axis=1)
        if np.array_equal(R2, R):
            break
        R = R2
    return N * N - int(_POP8[R].sum())


def _swap(e1, e2, s, EA, EB, SA, SB, NB, adjm):
    """Double-edge switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Involution on the same pair."""
    a1 = int(EA[e1])
    b1 = int(EB[e1])
    a2 = int(EA[e2])
    b2 = int(EB[e2])
    EB[e1] = b2
    EB[e2] = b1
    SB[e1], SB[e2] = SB[e2], SB[e1]
    NB[a1, SA[e1]] = s + b2
    NB[a2, SA[e2]] = s + b1
    NB[s + b2, SB[e1]] = a1
    NB[s + b1, SB[e2]] = a2
    adjm[a1, b1] = False
    adjm[a2, b2] = False
    adjm[a1, b2] = True
    adjm[a2, b1] = True


def _anneal(s, d, D, EA, EB, rng, max_moves, deadline, T0):
    """Anneal double-edge switches in place. Returns True if the graph reaches zero defects."""
    NB, SA, SB, adjm = _pack(s, d, EA, EB)
    cost = _cost(NB, D)
    E = s * d
    for t in range(max_moves):
        if cost == 0 or time.monotonic() > deadline:
            break
        e1 = rng.randrange(E)
        e2 = rng.randrange(E)
        a1 = int(EA[e1])
        b1 = int(EB[e1])
        a2 = int(EA[e2])
        b2 = int(EB[e2])
        if a1 == a2 or b1 == b2 or adjm[a1, b2] or adjm[a2, b1]:
            continue
        _swap(e1, e2, s, EA, EB, SA, SB, NB, adjm)
        new = _cost(NB, D)
        T = T0 * (1.0 - t / max_moves) + 0.05
        if new <= cost or rng.random() < math.exp(-(new - cost) / T):
            cost = new
        else:
            _swap(e1, e2, s, EA, EB, SA, SB, NB, adjm)
    return cost == 0


def _random_regular(s, d, rng):
    """Random d-regular bipartite graph on sides of size s, built from d disjoint-edge permutations."""
    idx = np.arange(s)
    for _ in range(30):
        adj = np.zeros((s, s), dtype=bool)
        perms = []
        ok = True
        for _layer in range(d):
            done = False
            for _try in range(3000):
                p = list(range(s))
                rng.shuffle(p)
                p = np.array(p, dtype=np.int64)
                if not adj[idx, p].any():
                    done = True
                    break
            if not done:
                ok = False
                break
            adj[idx, p] = True
            perms.append(p)
        if ok:
            EA = np.tile(idx, d).astype(np.int64)
            EB = np.concatenate(perms).astype(np.int64)
            return EA, EB
    return None


def _grow(s, d, EA, EB, rng):
    """Add one A-vertex and one B-vertex, keeping d-regularity and bipartiteness."""
    E = len(EA)
    order = list(range(E))
    rng.shuffle(order)
    used_a, used_b, chosen = set(), set(), []
    for e in order:
        if len(chosen) == d - 1:
            break
        a = int(EA[e])
        b = int(EB[e])
        if a in used_a or b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        chosen.append(e)
    if len(chosen) < d - 1:
        return None
    x = s  # new A-vertex
    y = s  # new B-vertex
    nA = EA.tolist()
    nB = EB.tolist()
    for e in chosen:
        a = nA[e]
        b = nB[e]
        nA[e] = x          # edge (a, b) becomes (x, b)
        nA.append(a)       # new edge (a, y)
        nB.append(y)
    nA.append(x)           # new edge (x, y)
    nB.append(y)
    return s + 1, np.array(nA, dtype=np.int64), np.array(nB, dtype=np.int64)


def _grow_repair(d, D, rng, deadline):
    """Grow a d-regular bipartite graph of diameter <= D, one pair at a time, repairing with annealing."""
    s = max(2 * d, 20)
    init = _random_regular(s, d, rng)
    if init is None:
        return None
    EA, EB = init
    if not _anneal(s, d, D, EA, EB, rng, 3000, deadline, 2.0):
        return None
    best = (s, EA.copy(), EB.copy())
    cur = (s, EA, EB)
    fails = 0
    while time.monotonic() < deadline and fails < 8:
        cs, cA, cB = cur
        step = max(1, cs // 12)
        ns, nA, nB = cs, cA, cB
        ok = True
        for _ in range(step):
            g = _grow(ns, d, nA, nB, rng)
            if g is None:
                ok = False
                break
            ns, nA, nB = g
        if not ok:
            break
        if _anneal(ns, d, D, nA, nB, rng, 300, deadline, 1.5):
            cur = (ns, nA, nB)
            best = (ns, nA.copy(), nB.copy())
            fails = 0
        else:
            fails += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # cycle C_{2D}: bipartite, 2-regular, diameter D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best_n, best_e

    if D >= 3:
        rng = random.Random(seed)
        try:
            res = _grow_repair(d, D, rng, deadline)
        except Exception:
            res = None
        if res is not None:
            s, EA, EB = res
            edges = [(int(EA[e]), s + int(EB[e])) for e in range(len(EA))]
            consider(2 * s, edges)

    return best_n, best_e
