import math
import random
import time

import lib

ITERS = 1500          # annealing steps per (group, voltage assignment) try
MAX_GROUPS = 40       # groups tried inside one attempt
TOP_FRAC = 0.62       # search orders up to this fraction of the Moore bound


# ----------------------------------------------------------------------------
# Baseline families. Each is validated before use, so these only ever help.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Voltage lifts of small bipartite base graphs over finite groups.
#
# Base: a A-vertices and a B-vertices, each with exactly d darts. A dart
# (u, v, g) joins A(u,x) to B(v, x*g) for all x in G, so the lift has 2*a*N
# vertices and is d-regular and bipartite. Left multiplication by G acts
# transitively on each fibre, so diameter is checked by BFS from one
# representative per fibre (2a BFS runs).
#
# The state is the dart list. Moves change a voltage, or swap the B-endpoints
# of two darts (this keeps every degree exact). The cost is the number of
# (source, vertex) pairs at distance more than D.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k (k=1 is cyclic)."""
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
    """Multiplication table T[x][g] = x*g and inverse list for the group."""
    _, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    invs = [inv(g) for g in range(N)]
    return T, invs


def _init(a, N, d, rng):
    """Random dart list: darts from A_u are indices u*d..u*d+d-1; each B_v receives d darts."""
    vs = [v for v in range(a) for _ in range(d)]
    for _ in range(50):
        rng.shuffle(vs)
        darts = [(i // d, vs[i], rng.randrange(N)) for i in range(a * d)]
        if len(set(darts)) == len(darts):
            return darts
    return None


def _adjacency(a, N, darts, T, invs):
    """Adjacency lists of the lift. A(u,x) = u*N + x, B(v,y) = a*N + v*N + y."""
    base = a * N
    adj = [[] for _ in range(2 * base)]
    for u, v, g in darts:
        ig = invs[g]
        bv = base + v * N
        for x in range(N):
            adj[u * N + x].append(bv + T[x][g])
            adj[bv + x].append(u * N + T[x][ig])
    return adj


def _cost(a, N, D, adj):
    """Number of (source, vertex) pairs not within distance D, over one source per fibre."""
    V = len(adj)
    sources = [u * N for u in range(a)] + [a * N + v * N for v in range(a)]
    total = 0
    for s in sources:
        seen = bytearray(V)
        seen[s] = 1
        frontier = [s]
        cnt = 1
        for _ in range(D):
            nxt = []
            for w in frontier:
                for z in adj[w]:
                    if not seen[z]:
                        seen[z] = 1
                        nxt.append(z)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += V - cnt
    return total


def _anneal(a, N, d, D, T, invs, rng, iters, deadline):
    """Simulated annealing over darts to reach cost 0. Returns darts or None."""
    darts = _init(a, N, d, rng)
    if darts is None:
        return None
    adj = _adjacency(a, N, darts, T, invs)
    cur = _cost(a, N, D, adj)
    nd = len(darts)
    for it in range(iters):
        if cur == 0:
            return darts
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        cand = darts[:]
        if rng.random() < 0.5:
            i = rng.randrange(nd)
            u, v, _ = cand[i]
            cand[i] = (u, v, rng.randrange(N))
        else:
            i = rng.randrange(nd)
            j = rng.randrange(nd)
            ui, vi, gi = cand[i]
            uj, vj, gj = cand[j]
            if vi == vj:
                continue
            cand[i] = (ui, vj, gi)
            cand[j] = (uj, vi, gj)
        if len(set(cand)) != nd:
            continue
        adj2 = _adjacency(a, N, cand, T, invs)
        v2 = _cost(a, N, D, adj2)
        if v2 <= cur or rng.random() < math.exp(-(v2 - cur) / temp):
            darts, cur, adj = cand, v2, adj2
    if cur == 0:
        return darts
    return None


def _attempt(a, N, d, D, rng, deadline):
    """Try groups of order N in random order until one yields a valid lift."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        T, invs = _tables(N, m, k, r)
        darts = _anneal(a, N, d, D, T, invs, rng, ITERS, deadline)
        if darts is not None:
            return darts, T
    return None


def _edges(a, N, darts, T):
    """Edge list of the lift for the given darts."""
    base = a * N
    edges = []
    for u, v, g in darts:
        bv = base + v * N
        for x in range(N):
            edges.append((u * N + x, bv + T[x][g]))
    return 2 * base, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.80 * time_limit, time_limit - 5.0))
    rng = random.Random(seed)

    best = (1, [])
    if d < 1 or D < 1:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Fast exact families.
    try:
        if D == 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
            return best
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            consider(*lib.araujo_lopez_graph(d - 2))
        if D >= 2:
            consider(*lib.haar_graph(d, range(d)))
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
    except Exception:
        pass

    if d < 2 or D < 2:
        return best

    try:
        moore = lib._moore_bound(d, D)
        top = min(moore, int(TOP_FRAC * moore))

        cands = []
        for a in (1, 2, 3, 4):
            for N in range(max(d, 2), top // (2 * a) + 1):
                n = 2 * a * N
                if best[0] < n <= top:
                    cands.append((n, a, N))
        cands.sort()

        budget = 0.7
        while time.monotonic() < deadline and cands:
            for item in list(cands):
                n, a, N = item
                if n <= best[0]:
                    continue
                now = time.monotonic()
                if now >= deadline:
                    break
                res = _attempt(a, N, d, D, rng, min(deadline, now + budget))
                if res is not None:
                    darts, T = res
                    nn, e = _edges(a, N, darts, T)
                    consider(nn, e)
            cands = [c for c in cands if c[0] > best[0]]
            budget *= 1.7
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
