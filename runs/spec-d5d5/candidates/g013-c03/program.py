import itertools
import math
import random
import time

import lib

ITERS = 2000        # annealing steps per (group, base graph) try
MAX_GROUPS = 25     # groups tried per attempt
MAX_BASE = 3        # base vertices per side: p = 1 .. MAX_BASE
WINDOW = 6          # orders tried above the current best, per p
DUP_PENALTY = 4     # cost per repeated dart (keeps the lift simple and degree-full)


# ----------------------------------------------------------------------------
# Baseline families (fast, always checked with lib.is_valid before use).
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
# Multi-base voltage lifts over semidirect products Z_m x| Z_k.
#
# Base graph: p "A" vertices and p "B" vertices, d darts leaving each A vertex
# and entering each B vertex (d permutations of range(p)). Each dart (a, b) gets
# a voltage g in G, and the lift joins A(a, x) to B(b, x*g) for all x in G.
# Left multiplication by G is an automorphism that is transitive on each fibre,
# so diameter <= D is checked by BFS from the 2p fibre representatives A(s, e),
# B(s, e). Each vertex has degree d and the lift has 2*p*|G| vertices.
#
# This differs from the single-base bi-Cayley search: the base graph has up to
# MAX_BASE vertices per side, so the search space is much wider.
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


def _base(p, d, rng):
    """Base darts: d random permutations of range(p), giving a d-regular bipartite multigraph."""
    base = []
    for _ in range(d):
        perm = list(range(p))
        rng.shuffle(perm)
        for a in range(p):
            base.append((a, perm[a]))
    return base


def _cost(p, N, T, base, V, D):
    """Unreached (source, vertex) pairs over the 2p fibre sources, plus a penalty for repeated darts."""
    n = 2 * p * N
    off = p * N
    adj = [[] for _ in range(n)]
    for (a, b), g in zip(base, V):
        ao = a * N
        bo = off + b * N
        for x in range(N):
            u = ao + x
            w = bo + T[x][g]
            adj[u].append(w)
            adj[w].append(u)
    total = 0
    for s in range(p):
        for src in (s * N, off + s * N):
            seen = bytearray(n)
            seen[src] = 1
            frontier = [src]
            cnt = 1
            for _ in range(D):
                nxt = []
                for u in frontier:
                    for w in adj[u]:
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                if not nxt:
                    break
                cnt += len(nxt)
                frontier = nxt
            total += n - cnt
    dup = len(base) - len(set(zip(base, V)))
    return total + DUP_PENALTY * dup


def _anneal(p, N, T, base, D, rng, deadline):
    """Simulated annealing over the dart voltages to reach zero unreached pairs."""
    L = len(base)
    V = [rng.randrange(N) for _ in range(L)]
    cur = _cost(p, N, T, base, V, D)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / ITERS))
        i = rng.randrange(L)
        c = rng.randrange(N)
        if c == V[i]:
            continue
        old = V[i]
        V[i] = c
        v = _cost(p, N, T, base, V, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            V[i] = old
    return V if cur == 0 else None


def _attempt(p, N, d, D, rng, deadline):
    """Try groups of order N with a random base graph until voltages give diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, mul, _ = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        base = _base(p, d, rng)
        V = _anneal(p, N, T, base, D, rng, deadline)
        if V is not None:
            return base, V, T
    return None


def _edges(p, N, T, base, V):
    """Edge list of the lift; A indices are < p*N <= B indices, so every pair is (small, large)."""
    es = set()
    off = p * N
    for (a, b), g in zip(base, V):
        for x in range(N):
            es.add((a * N + x, off + b * N + T[x][g]))
    return sorted(es)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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
            return True
        return False

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

    bound = lib._moore_bound(d, D)
    budget = 0.6
    while time.monotonic() < deadline:
        cands = []
        for p in range(1, MAX_BASE + 1):
            lo = best_n // (2 * p) + 1          # smallest N with 2*p*N > best_n
            hi = min(bound // (2 * p), lo + WINDOW)
            for N in range(max(lo, 2), hi + 1):
                cands.append((2 * p * N, p, N))
        if not cands:
            break
        cands.sort()
        success = False
        for n_, p, N in cands:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(p, N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            base, V, T = res
            if consider(n_, _edges(p, N, T, base, V)):
                success = True
                break
        if not success:
            budget *= 1.5

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
