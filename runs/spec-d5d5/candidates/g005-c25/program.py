import itertools
import math
import random
import time

import lib

# New idea (multi-orbit layered voltage lift): a bipartite graph with `a` orbits per
# side is built over a group G of order N. Layer t gives a permutation sigma_t of the
# a A-orbits onto the a B-orbits, and a voltage g_{t,i} in G. The lift joins
# A_{i,x} to B_{sigma_t(i), x*g_{t,i}} for every x in G and every layer t. Every
# vertex then has degree d (before dedup). Left multiplication by G is an automorphism,
# so the diameter is decided by BFS from one representative per orbit (2a sources).
# a = 1 reproduces the bi-Cayley search, and a = 2, 3 give more freedom at smaller N.

MAX_GROUPS_PER_ATTEMPT = 8
ITERS = 1200
ORBIT_CHOICES = (2, 1, 3)


# ----------------------------------------------------------------------------
# Baseline families (kept for the non-target cases).
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
# Multi-orbit layered voltage lifts over semidirect products Z_m x| Z_k.
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


def _lift_adjacency(a, N, T, sig, volt):
    """Adjacency of the lift. A_{i,x} has index i*N+x; B_{j,y} has index a*N+j*N+y."""
    base = a * N
    adj = [[] for _ in range(2 * base)]
    for t in range(len(sig)):
        st = sig[t]
        vt = volt[t]
        for i in range(a):
            j = st[i]
            g = vt[i]
            ai = i * N
            bj = base + j * N
            for x in range(N):
                u = ai + x
                v = bj + T[x][g]
                adj[u].append(v)
                adj[v].append(u)
    return adj


def _orbit_cost(a, N, D, adj):
    """Total count of (source, vertex) pairs not within distance D, over one source per orbit."""
    base = a * N
    n = 2 * base
    sources = [i * N for i in range(a)] + [base + j * N for j in range(a)]
    total = 0
    for s in sources:
        seen = bytearray(n)
        seen[s] = 1
        frontier = [s]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += n - cnt
    return total


def _anneal(a, N, T, d, D, rng, iters, deadline):
    """Anneal per-layer permutations and voltages until the lift has diameter <= D."""
    sig = [rng.sample(range(a), a) for _ in range(d)]
    volt = [[rng.randrange(N) for _ in range(a)] for _ in range(d)]
    cur = _orbit_cost(a, N, D, _lift_adjacency(a, N, T, sig, volt))
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        sg = [row[:] for row in sig]
        vl = [row[:] for row in volt]
        t = rng.randrange(d)
        if a > 1 and rng.random() < 0.3:
            i, j = rng.sample(range(a), 2)
            sg[t][i], sg[t][j] = sg[t][j], sg[t][i]
        else:
            vl[t][rng.randrange(a)] = rng.randrange(N)
        v = _orbit_cost(a, N, D, _lift_adjacency(a, N, T, sg, vl))
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            sig, volt, cur = sg, vl, v
    return (sig, volt) if cur == 0 else None


def _attempt(a, N, d, D, rng, deadline):
    """Try groups of order N for an a-orbit lift until one reaches diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        _, mul, _ = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        res = _anneal(a, N, T, d, D, rng, ITERS, deadline)
        if res is not None:
            sig, volt = res
            return T, sig, volt
    return None


def _lift_edges(a, N, T, sig, volt):
    """Return (n, edges) of the lift, deduplicated."""
    base = a * N
    s = set()
    for t in range(len(sig)):
        for i in range(a):
            j = sig[t][i]
            g = volt[t][i]
            for x in range(N):
                s.add((i * N + x, base + j * N + T[x][g]))
    return 2 * base, list(s)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 5.0)
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

    Nmax = lib._moore_bound(d, D)
    budget = 0.5
    active = list(ORBIT_CHOICES)
    while time.monotonic() < deadline and active:
        progressed = False
        for a in list(active):
            # Smallest order per side that beats the current best.
            N = best_n // (2 * a) + 1
            if 2 * a * N > Nmax:
                active.remove(a)
                continue
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(a, N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            T, sig, volt = res
            before = best_n
            n, e = _lift_edges(a, N, T, sig, volt)
            consider(n, e)
            if best_n > before:
                progressed = True
        if not progressed:
            budget = min(budget * 2, 20.0)

    return best
