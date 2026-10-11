import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 30   # groups tried per order N within one attempt
ITERS = 800                   # annealing steps per restart (bi-Cayley baseline)
RESTARTS = 4                  # fresh random connection sets per group (baseline)
TOP_SLACK = 8                 # baseline searches orders up to Nmax//2 + TOP_SLACK

LIFT_ITERS = 3000             # annealing steps per restart (multi-vertex lift)
LIFT_RESTARTS = 3             # restarts per group (multi-vertex lift)
LIFT_BASES = (2, 3)           # base-graph sizes t (t vertices per side)

# Strategy:
#   1. Cheap classical constructions (projective plane, generalized quadrangle, Haar).
#   2. Baseline: bi-Cayley search over semidirect products (single base vertex per side).
#   3. New family: t-vertex-per-side base graphs. The base is a sum of d random
#      permutations of {0..t-1}, each with a random group voltage in a semidirect
#      product Z_m x| Z_k. Vertices are A_{i,x} and B_{j,y}, with edges
#      A_{i,x} -- B_{sigma_k(i), x*g_k}. Left multiplication by the group is an
#      automorphism, so checking eccentricity from the t+t representatives A_{i,0},
#      B_{j,0} is enough to certify diameter <= D. The order 2tN is searched by
#      bisection with annealing.
#   Every candidate is checked with lib.is_valid before being kept, so the fallback is
#   always a valid graph.


# ----------------------------------------------------------------------------
# Classical baselines.
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
# Shared group utilities.
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


# ----------------------------------------------------------------------------
# Baseline: bi-Cayley search (one base vertex per side).
# ----------------------------------------------------------------------------

def _unreached(N, T, invs, S, D):
    """Count (source, vertex) pairs not within distance D, for sources A_0 and B_0."""
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _anneal(N, T, invs, d, D, rng, iters, deadline):
    """Simulated annealing over S = {0, s_1, ..., s_{d-1}} to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _attempt(N, d, D, rng, deadline):
    """Try groups of order N; for each group run several independent annealing restarts."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        for _ in range(RESTARTS):
            if time.monotonic() > deadline:
                return None
            S = _anneal(N, T, invs, d, D, rng, ITERS, deadline)
            if S is not None:
                return T, S
    return None


def _bicayley_search(d, D, rng, deadline, consider):
    """Baseline search over bi-Cayley graphs; calls consider(n, edges) on each success."""
    if d < 2 or D < 2:
        return
    Nmax = lib._moore_bound(d, D) // 2
    top = min(Nmax, Nmax // 2 + TOP_SLACK)
    cands = set(range(d + 1, top + 1))

    budget = 0.4
    while time.monotonic() < deadline and cands:
        success = False
        for N in sorted(cands, reverse=True):
            now = time.monotonic()
            if now >= deadline:
                break
            att_deadline = min(deadline, now + budget)
            res = _attempt(N, d, D, rng, att_deadline)
            if res is None:
                continue
            T, S = res
            edges = [(x, N + T[x][g]) for x in range(N) for g in S]
            consider(2 * N, edges)
            cands = {M for M in cands if M > N}
            if N + 1 <= Nmax:
                cands.add(N + 1)
            success = True
            break
        if not success:
            budget *= 1.5


# ----------------------------------------------------------------------------
# New family: t-vertex-per-side group lifts with permutation base graphs.
#
# Vertices A_{i,x} = i*N + x and B_{j,y} = t*N + j*N + y, for i, j in 0..t-1
# and x, y in G. Each of the d darts k has a permutation sigma_k of {0..t-1} and
# a voltage g_k in G, giving edges A_{i,x} -- B_{sigma_k(i), x*g_k}. Every A and B
# vertex gets exactly one edge per dart, so degree <= d.
# ----------------------------------------------------------------------------

def _lift_cost(N, t, D, T, perms, gs):
    """Number of (representative, vertex) pairs not within distance D."""
    total = 2 * t * N
    tN = t * N
    adj = [[] for _ in range(total)]
    for k in range(len(gs)):
        p = perms[k]
        g = gs[k]
        for i in range(t):
            ob = i * N
            bb = tN + p[i] * N
            for x in range(N):
                a = ob + x
                b = bb + T[x][g]
                adj[a].append(b)
                adj[b].append(a)
    sources = [i * N for i in range(t)] + [tN + j * N for j in range(t)]
    unreached = 0
    for src in sources:
        seen = bytearray(total)
        seen[src] = 1
        frontier = [src]
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
        unreached += total - count
    return unreached


def _lift_anneal(N, t, d, D, T, rng, deadline):
    """Anneal over d darts (permutation, voltage) to zero unreached pairs."""
    perms = []
    for _ in range(d):
        p = list(range(t))
        rng.shuffle(p)
        perms.append(p)
    gs = [rng.randrange(N) for _ in range(d)]
    cur = _lift_cost(N, t, D, T, perms, gs)
    for it in range(LIFT_ITERS):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = max(0.2, 2.0 * (1.0 - it / LIFT_ITERS))
        k = rng.randrange(d)
        old_g = gs[k]
        old_p = perms[k][:]
        if rng.random() < 0.5:
            gs[k] = rng.randrange(N)
        else:
            i, j = rng.sample(range(t), 2)
            perms[k][i], perms[k][j] = perms[k][j], perms[k][i]
        v = _lift_cost(N, t, D, T, perms, gs)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            gs[k] = old_g
            perms[k] = old_p
    if cur == 0:
        return perms, gs
    return None


def _lift_attempt(N, t, d, D, rng, deadline):
    """Try groups of order N for a t-vertex-per-side lift."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        for _ in range(LIFT_RESTARTS):
            if time.monotonic() > deadline:
                return None
            res = _lift_anneal(N, t, d, D, T, rng, deadline)
            if res is not None:
                perms, gs = res
                return T, perms, gs
    return None


def _lift_edges(N, t, perms, gs, T):
    """Edge list of the lift; A vertices come first, then B vertices."""
    es = set()
    tN = t * N
    for k in range(len(gs)):
        p = perms[k]
        g = gs[k]
        for i in range(t):
            for x in range(N):
                es.add((i * N + x, tN + p[i] * N + T[x][g]))
    return sorted(es)


def _lift_search(d, D, t, rng, phase_deadline, consider):
    """Bisection on the group order N for a t-base lift, keeping the largest success."""
    hi = lib._moore_bound(d, D) // (2 * t)
    lo = d + 1
    while lo <= hi and time.monotonic() < phase_deadline:
        mid = (lo + hi + 1) // 2
        now = time.monotonic()
        att = min(phase_deadline, now + max(1.5, (phase_deadline - now) / 4.0))
        res = _lift_attempt(mid, t, d, D, rng, att)
        if res is None:
            hi = mid - 1
        else:
            T, perms, gs = res
            consider(2 * t * mid, _lift_edges(mid, t, perms, gs, T))
            lo = mid + 1


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = {"n": 1, "e": []}

    def consider(n, e):
        if n > best["n"] and lib.is_valid(n, e, d, D):
            best["n"] = n
            best["e"] = e

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best["n"], best["e"]

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
        return best["n"], best["e"]

    # Phase 1: baseline bi-Cayley search, short slice to secure a valid baseline.
    _bicayley_search(d, D, rng, start + 0.2 * time_limit * 0.85, consider)

    # Phase 2: multi-vertex lifts with permutation base graphs.
    remaining_bases = len(LIFT_BASES)
    for idx, t in enumerate(LIFT_BASES):
        now = time.monotonic()
        if now >= deadline:
            break
        share = (deadline - now) / (remaining_bases - idx)
        phase_deadline = min(deadline, now + share)
        _lift_search(d, D, t, rng, phase_deadline, consider)

    # Phase 3: leftover time goes back to the baseline search.
    if time.monotonic() < deadline:
        _bicayley_search(d, D, rng, deadline, consider)

    if not lib.is_valid(best["n"], best["e"], d, D):
        return 1, []
    return best["n"], best["e"]
