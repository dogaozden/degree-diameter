import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baselines: K_{d,d}, cycles, projective-plane incidence, Araujo-Pardo-Lopez.
# ----------------------------------------------------------------------------

def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (q capped for speed)."""
    for q in range(min(d - 1, 30), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo_candidate(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power in [3, 30]."""
    q = d - 2
    if 3 <= q <= 30 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
    return None


# ----------------------------------------------------------------------------
# Fast diameter evaluation for bipartite graphs given as neighbour sets.
# ----------------------------------------------------------------------------

def _reach(adj, src, D, N):
    """Number of vertices (including src) within distance D of src."""
    seen = bytearray(N)
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
    return count


def _bad_ordered(n, nbr, D):
    """Number of ordered vertex pairs at distance > D (zero iff diameter <= D and connected)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in nbr[v]:
                r |= reach[u]
            new.append(r)
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach)


# ----------------------------------------------------------------------------
# Phase A: Haar graphs of small non-abelian groups.
#
# Haar graph H(G, S): A_g ~ B_{g*s} for s in S. Left multiplication is an
# automorphism that is transitive on each side, so the diameter is <= D iff
# both A_e and B_e reach everything within D. That needs only two BFS per try.
# ----------------------------------------------------------------------------

def _random_group(G, rng):
    """Return (mul, inv) for a random semidirect product Z_m x| Z_k of order G, else cyclic."""
    ks = [k for k in range(2, G) if G % k == 0 and G // k >= 2]
    rng.shuffle(ks)
    for k in ks[:8]:
        m = G // k
        cands = [r for r in range(2, m)
                 if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if cands and rng.random() < 0.9:
            r = rng.choice(cands)
            _, mul, inv = lib.semidirect_group(m, k, r)
            return mul, inv
    _, mul, inv = lib.semidirect_group(G, 1, 1)
    return mul, inv


def _haar_cost_fn(G, mul, inv, D):
    """Return cost(S): unreached ordered pairs of the Haar graph H(G, S) seen from A_e and B_e."""
    cache = {}

    def rperm(t):
        p = cache.get(t)
        if p is None:
            p = [mul(h, t) for h in range(G)]
            cache[t] = p
        return p

    N = 2 * G

    def cost(S):
        adj = [[] for _ in range(N)]
        for s in S:
            P = rperm(s)
            Q = rperm(inv(s))
            for g in range(G):
                adj[g].append(G + P[g])
                adj[G + g].append(Q[g])
        return (N - _reach(adj, 0, D, N)) + (N - _reach(adj, G, D, N))

    return cost


def _try_G(G, d, D, rng, deadline, iters):
    """Hill-climb a d-subset S of some group of order G so H(G, S) has diameter <= D."""
    for _ in range(3):
        if time.monotonic() >= deadline:
            return None
        mul, inv = _random_group(G, rng)
        cost = _haar_cost_fn(G, mul, inv, D)
        S = rng.sample(range(G), d)
        c = cost(S)
        for _ in range(iters):
            if c == 0 or time.monotonic() >= deadline:
                break
            i = rng.randrange(d)
            x = rng.randrange(G)
            if x in S:
                continue
            T = list(S)
            T[i] = x
            ct = cost(T)
            if ct <= c or rng.random() < 0.01:
                S, c = T, ct
        if c == 0:
            return S, mul
    return None


def _phase_a(d, D, deadline, rng):
    """Grow the group order while Haar graphs of diameter <= D are found. Returns (n, edges) or None."""
    G = d + 1
    best = None
    while time.monotonic() < deadline:
        res = _try_G(G, d, D, rng, deadline, 300)
        if res is None:
            break
        S, mul = res
        best = (2 * G, [(g, G + mul(g, s)) for g in range(G) for s in S])
        G += 1
    return best


# ----------------------------------------------------------------------------
# Phase B: grow-and-anneal on the general bipartite graph.
#
# Growth: add one A-vertex and one B-vertex. Remove d edges (x_i, y_i) with
# distinct x_i and distinct y_i, then add (new_A, y_i) and (x_i, new_B). All
# degrees stay exactly d.
# Repair: annealed edge switches (a,b),(c,e) -> (a,e),(c,b), which keep degrees
# and bipartiteness, with cost = number of unreached ordered pairs.
# ----------------------------------------------------------------------------

def _grow(E, nbr, d, rng):
    """Add one A-vertex and one B-vertex by rewiring d edges. Returns False if impossible."""
    m = len(E)
    if m < d:
        return False
    idxs = rng.sample(range(m), min(m, 300))
    chosen, usedA, usedB = [], set(), set()
    for i in idxs:
        a, b = E[i]
        if a in usedA or b in usedB:
            continue
        chosen.append(i)
        usedA.add(a)
        usedB.add(b)
        if len(chosen) == d:
            break
    if len(chosen) < d:
        return False
    na = len(nbr)
    nb = na + 1
    nbr.append(set())
    nbr.append(set())
    for i in chosen:
        a, b = E[i]
        nbr[a].discard(b)
        nbr[b].discard(a)
        E[i] = (na, b)
        nbr[na].add(b)
        nbr[b].add(na)
        E.append((a, nb))
        nbr[a].add(nb)
        nbr[nb].add(a)
    return True


def _anneal(E, nbr, D, deadline, rng, cost):
    """Edge-switch annealing until the cost reaches zero or the deadline passes."""
    T = 0.5
    m = len(E)
    n = len(nbr)
    it = 0
    while cost > 0:
        it += 1
        if (it & 15) == 0 and time.monotonic() >= deadline:
            break
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in nbr[a] or b in nbr[c]:
            continue
        nbr[a].discard(b)
        nbr[b].discard(a)
        nbr[c].discard(e)
        nbr[e].discard(c)
        nbr[a].add(e)
        nbr[e].add(a)
        nbr[c].add(b)
        nbr[b].add(c)
        E[i] = (a, e)
        E[j] = (c, b)
        nc = _bad_ordered(n, nbr, D)
        if nc <= cost or rng.random() < math.exp(-(nc - cost) / T):
            cost = nc
        else:
            nbr[a].discard(e)
            nbr[e].discard(a)
            nbr[c].discard(b)
            nbr[b].discard(c)
            nbr[a].add(b)
            nbr[b].add(a)
            nbr[c].add(e)
            nbr[e].add(c)
            E[i] = (a, b)
            E[j] = (c, e)
    return cost


def _phase_b(d, D, n, edges, deadline, rng, consider):
    """Repeatedly anneal to zero cost, record the valid graph, then grow by two vertices."""
    E = [(int(a), int(b)) for a, b in edges]
    nbr = [set() for _ in range(n)]
    for a, b in E:
        nbr[a].add(b)
        nbr[b].add(a)
    cost = _bad_ordered(n, nbr, D)
    while time.monotonic() < deadline:
        if cost == 0:
            consider(len(nbr), list(E))
            if not _grow(E, nbr, d, rng):
                break
            cost = _bad_ordered(len(nbr), nbr, D)
            continue
        cost = _anneal(E, nbr, D, deadline, rng, cost)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.8 * time_limit - 1.0)
    deadline = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D  # even cycle: degree 2, diameter D, bipartite
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d} has diameter 2 (valid for D >= 2).
    best = [2 * d, [(i, d + j) for i in range(d) for j in range(d)]]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[:] = [n, e]

    try:
        if D == 2:
            return best[0], best[1]

        if D == 3:
            try:
                pg = _pg_candidate(d)
                if pg is not None:
                    consider(pg[0], pg[1])
            except Exception:
                pass
            try:
                ar = _araujo_candidate(d)
                if ar is not None:
                    consider(ar[0], ar[1])
            except Exception:
                pass
            if best[0] > 2 * d:
                return best[0], best[1]

        # Main search (D >= 4, or D == 3 with no baseline).
        p_deadline = start + 0.35 * total
        haar = _phase_a(d, D, p_deadline, rng)
        if haar is not None:
            consider(haar[0], haar[1])
            sn, se = haar
        else:
            sn, se = best[0], best[1]
        _phase_b(d, D, sn, se, deadline, rng, consider)
    except Exception:
        pass

    return best[0], best[1]
