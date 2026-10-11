import itertools
import math
import random
import time

import lib

ITERS = 2500            # annealing steps per (group, voltage assignment) try
T_HOT = 6.0             # initial temperature (unreached-pair units)
T_COLD = 0.3            # final temperature
MAX_GROUPS = 40         # groups tried per (b, N) attempt
ATTEMPT_BUDGET = 4.0    # seconds per (b, N) candidate
SWAP_PROB = 0.3         # chance a move permutes the B-side of one layer


# ----------------------------------------------------------------------------
# Safe fallback families.
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
    """W(q) for the largest small prime power q with q + 1 <= d."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New construction: bipartite group lifts of small base graphs.
#
# Base graph: b A-vertices and b B-vertices, d "layers". Layer l is a
# permutation sig[l] (A_i -> B_{sig[l][i]}) with a voltage G[l][i] in G.
# Lift over a finite group G of order N (right multiplication):
#     A_{i,x} ~ B_{sig[l][i], x * G[l][i]}   for every layer l.
# Vertices: 2*b*N. The lift is d-regular and bipartite by construction.
# Left translations are automorphisms, so the diameter is decided by BFS
# from A_{i,e} and B_{j,e} only (2b sources).
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(m, k, r):
    """Return (N, M, ginv) with M[x][g] = x*g and ginv[g] = g^-1 for the group."""
    N, mul, inv = lib.semidirect_group(m, k, r)
    M = [[mul(x, g) for g in range(N)] for x in range(N)]
    ginv = [inv(g) for g in range(N)]
    return N, M, ginv


def _valid_darts(b, d, sig, G):
    """True if the b*d darts (i, sig[l][i], G[l][i]) are pairwise distinct (so the lift is simple)."""
    seen = set()
    for l in range(d):
        for i in range(b):
            seen.add((i, sig[l][i], G[l][i]))
    return len(seen) == b * d


def _adjacency(b, N, d, M, sig, G):
    """Adjacency lists of the lift (all vertices, A-block first then B-block)."""
    nv = 2 * b * N
    adj = [[] for _ in range(nv)]
    off = b * N
    for l in range(d):
        sl = sig[l]
        Gl = G[l]
        for i in range(b):
            g = Gl[i]
            base_a = i * N
            base_b = off + sl[i] * N
            for x in range(N):
                a = base_a + x
                bb = base_b + M[x][g]
                adj[a].append(bb)
                adj[bb].append(a)
    return adj


def _unreached(nv, D, adj, srcs):
    """Total count of (source, vertex) pairs at distance > D, summed over sources."""
    total = 0
    for s in srcs:
        seen = bytearray(nv)
        seen[s] = 1
        frontier = [s]
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
        total += nv - count
    return total


def _cost(b, N, d, D, M, sig, G, srcs):
    adj = _adjacency(b, N, d, M, sig, G)
    return _unreached(len(adj), D, adj, srcs)


def _anneal(b, N, d, D, M, rng, iters, deadline):
    """Anneal voltages and layer permutations to zero unreached pairs; return (sig, G) or None."""
    srcs = [i * N for i in range(b)] + [b * N + j * N for j in range(b)]
    sig = []
    for _ in range(d):
        p = list(range(b))
        rng.shuffle(p)
        sig.append(p)
    G = [[rng.randrange(N) for _ in range(b)] for _ in range(d)]
    tries = 0
    while not _valid_darts(b, d, sig, G):
        G = [[rng.randrange(N) for _ in range(b)] for _ in range(d)]
        tries += 1
        if tries > 500:
            return None

    cur = _cost(b, N, d, D, M, sig, G, srcs)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            return None
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)

        if b == 1 or rng.random() >= SWAP_PROB:
            l = rng.randrange(d)
            i = rng.randrange(b)
            old = G[l][i]
            new = rng.randrange(N)
            if new == old:
                continue
            G[l][i] = new

            def undo(l=l, i=i, old=old):
                G[l][i] = old
        else:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(b), 2)
            sig[l][i1], sig[l][i2] = sig[l][i2], sig[l][i1]

            def undo(l=l, i1=i1, i2=i2):
                sig[l][i1], sig[l][i2] = sig[l][i2], sig[l][i1]

        if not _valid_darts(b, d, sig, G):
            undo()
            continue
        v = _cost(b, N, d, D, M, sig, G, srcs)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            undo()

    if cur == 0:
        return sig, G
    return None


def _attempt(b, N, d, D, rng, deadline):
    """Try several groups of order N with a b-vertex base; return (N, M, sig, G) or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, M, _ = _tables(m, k, r)
        res = _anneal(b, N, d, D, M, rng, ITERS, deadline)
        if res is not None:
            sig, G = res
            return N, M, sig, G
    return None


def _lift_edges(b, N, d, M, sig, G):
    """Edge list of the lift: A_{i,x} -- B_{j,x*g} for each dart (i, j, g)."""
    off = b * N
    edges = []
    for l in range(d):
        for i in range(b):
            g = G[l][i]
            j = sig[l][i]
            for x in range(N):
                edges.append((i * N + x, off + j * N + M[x][g]))
    return edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 4.0))
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

    # Record-matching case for D = 3: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    # Cheap fallbacks (always validated before use).
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

    # Candidate (size, b, N) with size = 2*b*N in (best_n, Moore bound],
    # tried in ascending size so each success is the smallest improvement.
    moore = lib._moore_bound(d, D)
    cands = []
    for b in range(1, 5):
        for N in range(max(d, 2), moore // (2 * b) + 1):
            size = 2 * b * N
            if best_n < size <= moore:
                cands.append((size, b, N))
    cands.sort()

    for size, b, N in cands:
        if size <= best_n:
            continue
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0.5:
            break
        budget = min(remaining, ATTEMPT_BUDGET)
        res = _attempt(b, N, d, D, rng, now + budget)
        if res is None:
            continue
        N_, M, sig, G = res
        consider(2 * b * N_, _lift_edges(b, N_, d, M, sig, G))

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
