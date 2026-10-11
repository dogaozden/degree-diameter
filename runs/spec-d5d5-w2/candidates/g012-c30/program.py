import math
import random
import time

import lib

MAX_GROUPS = 8        # groups tried per (a, N) attempt
ITERS = 1500          # annealing steps per group
T_HOT = 2.0           # initial annealing temperature
T_COLD = 0.2          # final annealing temperature
WINDOW = 8            # N values searched above the lower edge
FLOOR_FRAC = 0.47     # search lift orders from this fraction of the Moore-limited top
ATT_START = 1.0       # seconds per attempt in the first pass
ATT_CAP = 6.0         # cap on seconds per attempt
A_CHOICES = (1, 2, 3, 4)  # base graphs with a vertices per side
DUP_PEN = 20          # penalty per duplicate neighbour


# ----------------------------------------------------------------------------
# Safe baseline families (always checked with lib.is_valid).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Voltage lifts of small bipartite base graphs over semidirect products.
#
# Base: a A-vertices and a B-vertices, d darts from each A-vertex. Dart (k, i)
# joins A_i to B_{sig_k(i)} with a voltage g[k][i] in G. The lift has
# 2 * a * N vertices: A_i(x) ~ B_{sig_k(i)}(x * g[k][i]).
#
# Left multiplication by h is an automorphism, so each fibre is one orbit.
# Distances from the 2a representatives A_i(e), B_j(e) decide the diameter.
# a = 1 with identity permutations is the bi-Cayley case.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _connected(a, sig):
    """True if the base multigraph on 2a vertices is connected."""
    parent = list(range(2 * a))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for perm in sig:
        for i in range(a):
            ra, rb = find(i), find(a + perm[i])
            if ra != rb:
                parent[ra] = rb
    root = find(0)
    return all(find(v) == root for v in range(2 * a))


def _random_darts(a, d, rng):
    """d random permutations of range(a) forming a connected d-regular base."""
    while True:
        sig = []
        for _ in range(d):
            p = list(range(a))
            rng.shuffle(p)
            sig.append(p)
        if a == 1 or _connected(a, sig):
            return sig


def _cost(N, a, d, D, T, invs, sig, sinv, g):
    """Unreached (source, vertex) pairs at distance > D, plus duplicate-neighbour penalty."""
    V = 2 * a * N
    base_b = a * N
    adj = [None] * V
    for i in range(a):
        for x in range(N):
            row = T[x]
            adj[i * N + x] = [base_b + sig[k][i] * N + row[g[k][i]] for k in range(d)]
    for j in range(a):
        for y in range(N):
            row = T[y]
            nb = []
            for k in range(d):
                i = sinv[k][j]
                nb.append(i * N + row[invs[g[k][i]]])
            adj[base_b + j * N + y] = nb
    pen = 0
    for v in range(V):
        s = len(set(adj[v]))
        if s < d:
            pen += d - s
    sources = [i * N for i in range(a)] + [base_b + j * N for j in range(a)]
    total = 0
    for s in sources:
        seen = bytearray(V)
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
        total += V - cnt
    return total + DUP_PEN * pen


def _anneal(N, a, d, D, T, invs, sig, sinv, rng, deadline):
    """Simulated annealing over the voltages g[k][i] to zero the cost."""
    g = [[rng.randrange(N) for _ in range(a)] for _ in range(d)]
    cur = _cost(N, a, d, D, T, invs, sig, sinv, g)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
        k = rng.randrange(d)
        i = rng.randrange(a)
        c = rng.randrange(N)
        old = g[k][i]
        if c == old:
            continue
        g[k][i] = c
        v = _cost(N, a, d, D, T, invs, sig, sinv, g)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            g[k][i] = old
    if cur == 0:
        return g
    return None


def _attempt(a, N, d, D, rng, deadline):
    """Try groups of order N for base size a until a zero-cost voltage assignment appears."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() >= deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, y) for y in range(N)] for x in range(N)]
        invs = [inv(y) for y in range(N)]
        sig = _random_darts(a, d, rng)
        sinv = [[0] * a for _ in range(d)]
        for kk in range(d):
            for i in range(a):
                sinv[kk][sig[kk][i]] = i
        g = _anneal(N, a, d, D, T, invs, sig, sinv, rng, deadline)
        if g is not None:
            return T, sig, g
    return None


def _edges(N, a, d, T, sig, g):
    """Edge list and vertex count of the lift."""
    V = 2 * a * N
    edges = set()
    for i in range(a):
        for x in range(N):
            u = i * N + x
            for k in range(d):
                v = a * N + sig[k][i] * N + T[x][g[k][i]]
                edges.add((u, v))
    return V, sorted(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = [1, []]

    def consider(n, e):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best[0], best[1] = n, e
            return True
        return False

    # Exact record family for D = 3 when d - 1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best[0], best[1]

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2 or D < 2:
        return best[0], best[1]

    moore = lib._moore_bound(d, D)
    cur = best[0]
    att = ATT_START

    while time.monotonic() < deadline:
        found_any = False
        order = list(A_CHOICES)
        rng.shuffle(order)
        viable = False
        for a in order:
            now = time.monotonic()
            if now >= deadline:
                break
            Nhi = moore // (2 * a)
            if Nhi < 1:
                continue
            Nlo = max(cur // (2 * a) + 1, int(FLOOR_FRAC * Nhi))
            if Nlo > Nhi:
                continue
            viable = True
            if rng.random() < 0.5:
                N = Nlo
            else:
                N = rng.randint(Nlo, min(Nhi, Nlo + WINDOW))
            res = _attempt(a, N, d, D, rng, min(deadline, now + att))
            if res is None:
                continue
            found_any = True
            T, sig, g = res
            V, edges = _edges(N, a, d, T, sig, g)
            if consider(V, edges):
                cur = best[0]
        if not viable:
            break
        if not found_any:
            att = min(ATT_CAP, att * 1.5)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best[0], best[1]
