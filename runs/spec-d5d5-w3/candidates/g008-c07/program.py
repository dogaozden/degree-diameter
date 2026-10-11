import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 30   # groups tried per order N within one bi-Cayley attempt
ITERS = 800                   # annealing steps per restart (bi-Cayley)
RESTARTS = 4                  # fresh random connection sets per group
TOP_SLACK = 8                 # bi-Cayley orders searched up to Nmax//2 + TOP_SLACK

PARENT_FRACTION = 0.30        # share of the budget for the bi-Cayley fallback search
HARD_FRACTION = 0.85          # overall safety margin
LS_SLICE = 12.0               # seconds per local-search attempt at a fixed half-order


# ----------------------------------------------------------------------------
# Baseline families (always validated before use).
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
# Bi-Cayley search over semidirect products Z_m x| Z_k of order N (fallback).
# ----------------------------------------------------------------------------

def _groups(N):
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _unreached(N, T, invs, S, D):
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
            res = _attempt(N, d, D, rng, min(deadline, now + budget))
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
# NEW construction: direct edge-switch local search on bipartite graphs.
#
# Start from a random d-regular bipartite graph on h + h vertices (a random
# Haar-type circulant), then repeatedly apply degree-preserving 2-switches
# (a1-b1, a2-b2) -> (a1-b2, a2-b1) that keep the graph simple and bipartite.
# The cost is the number of unordered vertex pairs at distance > D.
# Simulated annealing drives the cost to zero. This is algebra-free and
# does not depend on any group structure.
# ----------------------------------------------------------------------------

def _ls_cost(nb, n, D):
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in nb[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _swap(E, eset, nb, i, j, a1, b1, a2, b2):
    """Replace current pairs (a1,b1) at index i and (a2,b2) at index j by (a1,b2) and (a2,b1)."""
    eset.discard((a1, b1))
    eset.discard((a2, b2))
    nb[a1].remove(b1)
    nb[b1].remove(a1)
    nb[a2].remove(b2)
    nb[b2].remove(a2)
    eset.add((a1, b2))
    eset.add((a2, b1))
    nb[a1].append(b2)
    nb[b2].append(a1)
    nb[a2].append(b1)
    nb[b1].append(a2)
    E[i] = (a1, b2)
    E[j] = (a2, b1)


def _ls_attempt(h, d, D, rng, deadline):
    """Anneal a random d-regular bipartite graph on h+h vertices to diameter <= D."""
    n = 2 * h
    S = rng.sample(range(h), d)
    E = [(i, h + (i + s) % h) for i in range(h) for s in S]
    eset = set(E)
    nb = [[] for _ in range(n)]
    for a, b in E:
        nb[a].append(b)
        nb[b].append(a)
    cur = _ls_cost(nb, n, D)
    m = len(E)
    it = 0
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        it += 1
        temp = max(0.05, 1.5 * math.exp(-it / 200.0))
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in eset or (a2, b1) in eset:
            continue
        _swap(E, eset, nb, i, j, a1, b1, a2, b2)
        new = _ls_cost(nb, n, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
            cur = new
        else:
            _swap(E, eset, nb, i, j, a1, b2, a2, b1)  # revert
    return list(E)


def _local_search_phase(d, D, rng, hard, consider, best_n):
    h = max(best_n // 2 + 1, d + 1)
    while time.monotonic() < hard:
        now = time.monotonic()
        att_deadline = min(hard, now + LS_SLICE)
        E = _ls_attempt(h, d, D, rng, att_deadline)
        if E is None:
            continue  # failed slice: retry same h with a fresh random start
        consider(2 * h, E)
        h += 1


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    hard = start + HARD_FRACTION * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = [1, []]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best[0], best[1]

    # Safe baselines.
    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < hard:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d >= 2 and D >= 2:
        # Fallback algebraic search first, so a valid strong graph is secured.
        parent_deadline = start + PARENT_FRACTION * time_limit
        _bicayley_search(d, D, rng, parent_deadline, consider)

        # Bold new construction: switch-based annealing on general bipartite graphs.
        if time.monotonic() < hard:
            _local_search_phase(d, D, rng, hard, consider, best[0])

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best[0], best[1]
