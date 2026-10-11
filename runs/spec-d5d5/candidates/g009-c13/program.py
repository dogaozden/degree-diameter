import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 30   # groups tried per (orbits, order) attempt
ITERS = 800                   # annealing steps per group try
KS = (1, 2, 3)                # orbits per side in the multi-orbit bi-Cayley search
CAP_FRAC = 0.56               # only search total orders up to CAP_FRAC * Moore bound


# ----------------------------------------------------------------------------
# Baseline families (fast, validated before use).
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
# Groups: semidirect products Z_m x|_r Z_k of order N.
# ----------------------------------------------------------------------------

def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for kk in range(1, N + 1):
        if N % kk:
            continue
        m = N // kk
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, kk, m) == 1 % m:
                out.append((m, kk, r))
    return out


# ----------------------------------------------------------------------------
# NEW IDEA: multi-orbit bi-Cayley graphs with a random regular base matrix.
#
# Vertices: A^i_x and B^j_y for i, j in 0..k-1 and x, y in G (|G| = N).
# Base matrix M (k x k, nonnegative integers, all row and column sums = d).
# For each (i, j) choose a set S[i][j] of M[i][j] group elements and join
#     A^i_x -- B^j_{x s}   for all x in G, s in S[i][j].
# Left multiplication by G is an automorphism, and each side splits into k
# G-orbits, so the diameter is the max eccentricity over the 2k sources
# A^i_e and B^j_e. The order is 2kN and the degree is exactly d.
# Base matrices come from sums of d random permutation matrices, which
# guarantees the row and column sums.
# ----------------------------------------------------------------------------

def _random_base(k, d, rng):
    """Random k x k nonnegative integer matrix with all row and column sums d."""
    M = [[0] * k for _ in range(k)]
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            M[i][p[i]] += 1
    return M


def _support_connected(k, M):
    """True if the bipartite support of M (rows i, columns j) is connected."""
    parent = list(range(2 * k))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for i in range(k):
        for j in range(k):
            if M[i][j]:
                parent[find(i)] = find(k + j)
    root = find(0)
    return all(find(x) == root for x in range(2 * k))


def _pick_base(k, d, rng):
    """Return a random base matrix whose support is connected, or None."""
    for _ in range(20):
        M = _random_base(k, d, rng)
        if _support_connected(k, M):
            return M
    return None


def _unreached(N, k, T, M, S, D):
    """Count (source, vertex) pairs not within distance D, for the 2k orbit representatives."""
    V = 2 * k * N
    adj = [[] for _ in range(V)]
    for i in range(k):
        for j in range(k):
            boff = k * N + j * N
            for s in S[i][j]:
                for x in range(N):
                    a = i * N + x
                    b = boff + T[x][s]
                    adj[a].append(b)
                    adj[b].append(a)
    total = 0
    sources = [i * N for i in range(k)] + [k * N + j * N for j in range(k)]
    for src in sources:
        seen = bytearray(V)
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
        total += V - count
    return total


def _anneal(N, k, T, M, d, D, rng, iters, deadline):
    """Anneal the connection sets S[i][j] (sizes fixed by M) to zero unreached pairs."""
    cells = [(i, j) for i in range(k) for j in range(k) if M[i][j] > 0]
    S = [[(rng.sample(range(N), M[i][j]) if M[i][j] else []) for j in range(k)]
         for i in range(k)]
    cur = _unreached(N, k, T, M, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        i, j = rng.choice(cells)
        p = rng.randrange(len(S[i][j]))
        c = rng.randrange(N)
        if c in S[i][j]:
            continue
        old = S[i][j][p]
        S[i][j][p] = c
        v = _unreached(N, k, T, M, S, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            S[i][j][p] = old
    return S if cur == 0 else None


def _attempt(N, k, d, D, rng, deadline):
    """Try groups of order N for k orbits per side until a valid connection system is found."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, kk, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        M = _pick_base(k, d, rng)
        if M is None:
            return None
        _, mul, _ = lib.semidirect_group(m, kk, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        S = _anneal(N, k, T, M, d, D, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


def _edges(N, k, T, S):
    """Edge list of the multi-orbit bi-Cayley graph (A-orbits 0..kN-1, B-orbits kN..2kN-1)."""
    edges = []
    for i in range(k):
        for j in range(k):
            boff = k * N + j * N
            for s in S[i][j]:
                for x in range(N):
                    edges.append((i * N + x, boff + T[x][s]))
    return edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
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

    moore = lib._moore_bound(d, D)
    cap = min(moore, int(CAP_FRAC * moore))
    cands = set()
    for kk in KS:
        for N in range(d + 1, cap // (2 * kk) + 1):
            n = 2 * kk * N
            if best_n < n <= cap:
                cands.add((kk, N))

    budget = 0.5
    while time.monotonic() < deadline and cands:
        success = False
        for kk, N in sorted(cands, key=lambda c: (-2 * c[0] * c[1], -c[0])):
            now = time.monotonic()
            if now >= deadline:
                break
            att_deadline = min(deadline, now + budget)
            res = _attempt(N, kk, d, D, rng, att_deadline)
            if res is None:
                continue
            T, S = res
            n = 2 * kk * N
            consider(n, _edges(N, kk, T, S))
            # Only strictly larger orders can improve now.
            cands = {c for c in cands if 2 * c[0] * c[1] > n}
            success = True
            break
        if not success:
            budget *= 1.5

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
