import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried for one (k, N) configuration within an attempt
ITERS = 1500                  # annealing steps per attempt
T_HOT = 1.5                   # initial annealing temperature (unreached-pair units)
T_COLD = 0.15                 # final annealing temperature
WINDOW = 10                   # number of smallest-order candidates tried per round
MAX_BASE = 4                  # maximum number of base vertices per side

# ----------------------------------------------------------------------------
# Multi-orbit bi-Cayley lifts.
#
# Vertices: A_{i,x} (i < k, x in G) and B_{j,y} (j < k, y in G), with
# |G| = N, so the graph has 2kN vertices.  The dart multiset is a k x k matrix
# of connection sets S[i][j] (subsets of G) with |S[i][j]| = M[i][j].
# Edges: A_{i,x} -- B_{j, x*g} for every g in S[i][j].
#
# Row and column sums of M equal d, so every vertex has degree d.  M is
# circulant, M[i][j] = c[(j - i) mod k] with c a composition of d into k
# parts, which gives row and column sums d automatically.
#
# Left multiplication by h is an automorphism (A_{i,x} -> A_{i,hx}), so each
# A-orbit and B-orbit is vertex-transitive.  The diameter check therefore
# only needs BFS from A_{i,e} and B_{j,e}, which are 2k sources.
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


def _unreached(k, N, T, invs, S, D):
    """Count (source, vertex) pairs not within distance D over the 2k orbit representatives."""
    KN = k * N
    V = 2 * KN
    Sinv = [[[invs[g] for g in S[i][j]] for j in range(k)] for i in range(k)]
    sources = [i * N for i in range(k)] + [KN + j * N for j in range(k)]
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < KN:
                    i, x = divmod(u, N)
                    row = T[x]
                    Si = S[i]
                    for j in range(k):
                        base = KN + j * N
                        for g in Si[j]:
                            v = base + row[g]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
                else:
                    j, y = divmod(u - KN, N)
                    row = T[y]
                    for i in range(k):
                        base = i * N
                        for h in Sinv[i][j]:
                            v = base + row[h]
                            if not seen[v]:
                                seen[v] = 1
                                nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _anneal(k, N, T, invs, d, D, M, rng, iters, deadline):
    """Anneal the connection sets S[i][j] (|S[i][j]| = M[i][j]) to zero unreached pairs."""
    S = [[rng.sample(range(N), M[i][j]) for j in range(k)] for i in range(k)]
    cells = [(i, j) for i in range(k) for j in range(k) if M[i][j] > 0]
    cur = _unreached(k, N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = T_HOT * (T_COLD / T_HOT) ** (it / iters)
        i, j = rng.choice(cells)
        t = rng.randrange(M[i][j])
        c = rng.randrange(N)
        row = S[i][j]
        if c in row:
            continue
        old = row[t]
        row[t] = c
        v = _unreached(k, N, T, invs, S, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            row[t] = old
    if cur == 0:
        return S
    return None


def _attempt(k, N, d, D, rng, deadline):
    """Try groups of order N with k base vertices per side until one lift has diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, kk, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, kk, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        c = [0] * k
        for _ in range(d):
            c[rng.randrange(k)] += 1
        M = [[c[(j - i) % k] for j in range(k)] for i in range(k)]
        S = _anneal(k, N, T, invs, d, D, M, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


def _lift_edges(k, N, T, S):
    """Edge list of the bi-Cayley lift: A_{i,x} = i*N + x, B_{j,y} = k*N + j*N + y."""
    KN = k * N
    edges = []
    for i in range(k):
        for j in range(k):
            for g in S[i][j]:
                for x in range(N):
                    edges.append((i * N + x, KN + j * N + T[x][g]))
    return edges


# ----------------------------------------------------------------------------
# Baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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

    if d < 2 or D < 2:
        return best

    moore = lib._moore_bound(d, D)
    lo = max(best_n + 1, int(0.45 * moore))
    cands = sorted({
        (2 * k * N, k, N)
        for k in range(1, min(d, MAX_BASE) + 1)
        for N in range(d + 1, moore // (2 * k) + 1)
        if 2 * k * N >= lo
    })

    budget = 0.3
    while time.monotonic() < deadline:
        window = [c for c in cands if c[0] > best_n][:WINDOW]
        if not window:
            break
        progress = False
        for n, k, N in window:
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(k, N, d, D, rng, min(deadline, now + budget))
            if res is None:
                continue
            T, S = res
            consider(2 * k * N, _lift_edges(k, N, T, S))
            progress = True
            break
        if not progress:
            budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
