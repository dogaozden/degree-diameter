import math
import random
import time

import lib

ITERS = 1200                  # annealing steps per (group, dart assignment) try
MAX_GROUPS_PER_ATTEMPT = 25   # groups tried per (b, N) attempt
WINDOW = 16                   # N values searched below each top for every base size b
TOP_SLACK = 8
MAX_B = 5                     # base vertices per side of the voltage lift


# ----------------------------------------------------------------------------
# Safe baselines.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Multi-base voltage lifts over semidirect products Z_m x| Z_k (order N).
#
# Base graph: b vertices A_0..A_{b-1} and b vertices B_0..B_{b-1}, each of degree d.
# Darts (i, j, g) with i, j in range(b) and g in G give edges
#     (A_i, x) -- (B_j, x*g)   for all x in G.
# Left multiplication by h maps (A_i, x) -> (A_i, h x) and is an automorphism, so the
# eccentricity of any vertex equals that of (A_i, e) or (B_j, e). Checking these 2b
# sources decides the diameter. Each dart set gives a d-regular bipartite graph on 2bN
# vertices. Darts sharing the same (i, j) must have distinct g to avoid duplicate edges.
# b = 1 is the classical bi-Cayley search; b >= 2 is the new, broader family.
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


def _tables(N, m, k, r):
    """Multiplication table T[x][g] = x*g and inverse list for the group of order N."""
    _, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    invs = [inv(g) for g in range(N)]
    return T, invs


def _graph_maps(b, ai, bj, gs, invs):
    """Adjacency maps out[i] = [(j, g)] for A_i and inn[j] = [(i, g^-1)] for B_j."""
    out = [[] for _ in range(b)]
    inn = [[] for _ in range(b)]
    for i, j, g in zip(ai, bj, gs):
        out[i].append((j, g))
        inn[j].append((i, invs[g]))
    return out, inn


def _unreached(b, N, T, out, inn, D):
    """Count (source, vertex) pairs not within distance D, over the 2b base sources."""
    bN = b * N
    total = 2 * bN
    sources = [i * N for i in range(b)] + [bN + j * N for j in range(b)]
    bad = 0
    for s in sources:
        seen = bytearray(total)
        seen[s] = 1
        count = 1
        frontier = [s]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < bN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in out[i]:
                        v = bN + j * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - bN, N)
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
        bad += total - count
    return bad


def _anneal(b, N, d, D, T, invs, rng, iters, deadline):
    """Simulated annealing over dart assignments to reach zero unreached pairs."""
    ai = [i for i in range(b) for _ in range(d)]
    nd = len(ai)
    bj = ai[:]
    rng.shuffle(bj)
    gs = None
    for _ in range(200):
        cand = [rng.randrange(N) for _ in range(nd)]
        if len(set(zip(ai, bj, cand))) == nd:
            gs = cand
            break
    if gs is None:
        return None

    def ok(bj_, gs_):
        return len(set(zip(ai, bj_, gs_))) == nd

    out, inn = _graph_maps(b, ai, bj, gs, invs)
    cur = _unreached(b, N, T, out, inn, D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            return None
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        bj2, gs2 = bj, gs
        if rng.random() < 0.5:
            k = rng.randrange(nd)
            c = rng.randrange(N)
            if c == gs[k]:
                continue
            gs2 = gs[:]
            gs2[k] = c
        else:
            k1 = rng.randrange(nd)
            k2 = rng.randrange(nd)
            if bj[k1] == bj[k2]:
                continue
            bj2 = bj[:]
            bj2[k1], bj2[k2] = bj[k2], bj[k1]
        if not ok(bj2, gs2):
            continue
        out2, inn2 = _graph_maps(b, ai, bj2, gs2, invs)
        v = _unreached(b, N, T, out2, inn2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            bj, gs, cur = bj2, gs2, v
    if cur != 0:
        return None
    return ai, bj, gs


def _attempt(b, N, d, D, rng, deadline):
    """Try groups of order N for base size b until a dart assignment works."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        T, invs = _tables(N, m, k, r)
        res = _anneal(b, N, d, D, T, invs, rng, ITERS, deadline)
        if res is not None:
            return T, invs, res
    return None


def _edges(b, N, T, ai, bj, gs):
    """Expand the dart assignment into the explicit edge list on 2bN vertices."""
    bN = b * N
    edges = []
    for i, j, g in zip(ai, bj, gs):
        for x in range(N):
            edges.append((i * N + x, bN + j * N + T[x][g]))
    return edges


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

    # Record-matching case for D = 3: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D == 1:
        consider(2, [(0, 1)])
        return best

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2 or D < 2:
        return best

    # Candidate (order, b, N) triples: order = 2*b*N vertices, N near the top of each window.
    M = lib._moore_bound(d, D)
    cands = []
    for b in range(1, MAX_B + 1):
        cap = M // (2 * b)
        top = min(cap, cap // 2 + TOP_SLACK)
        lo = max(d, top - WINDOW)
        for N in range(lo, top + 1):
            cands.append((2 * b * N, b, N))
    cands.sort()  # ascending: small successes raise the bar, then the frontier is probed

    budget = 0.3
    while time.monotonic() < deadline:
        pending = [c for c in cands if c[0] > best_n]
        if not pending:
            break
        for order, b, N in pending:
            if order <= best_n:
                continue
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(b, N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            T, invs, (ai, bj, gs) = res
            consider(2 * b * N, _edges(b, N, T, ai, bj, gs))
        budget *= 1.5

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
