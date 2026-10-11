import itertools
import math
import random
import time

import lib

ITERS = 1800          # annealing steps per attempt
GROUPS_PER_TRY = 6    # groups tried for one (a, N) attempt
A_LIST = [2, 3, 4, 1]  # base-graph sizes per side; a=2 gives 4N vertices


# ----------------------------------------------------------------------------
# Groups: semidirect products Z_m x|_r Z_k of order N (cyclic when r = 1).
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


# ----------------------------------------------------------------------------
# Voltage lifts over a bipartite base with a A-vertices and a B-vertices.
#
# Base: a multigraph whose (i, j) multiplicity M[i][j] has row and column sums d.
# Darts (i, j, g) give edges A_{i,x} -- B_{j, x*g} for all x in G.
# Left multiplication by G is an automorphism, so one source per base vertex
# suffices for the diameter check. Vertices: A_{i,x} -> i*N + x,
# B_{j,y} -> a*N + j*N + y.
# ----------------------------------------------------------------------------

def _random_pattern(a, d, rng):
    """Nonnegative a x a integer matrix with all row and column sums equal to d."""
    M = [[0] * a for _ in range(a)]
    for _ in range(d):
        p = list(range(a))
        rng.shuffle(p)
        for i in range(a):
            M[i][p[i]] += 1
    return M


def _unreached(a, N, D, T, Aadj, Badj):
    """Number of (source, vertex) pairs not within distance D, over one source per base vertex."""
    aN = a * N
    V = 2 * aN
    total = 0
    srcs = [i * N for i in range(a)] + [aN + j * N for j in range(a)]
    for src in srcs:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < aN:
                    i, x = divmod(u, N)
                    Tx = T[x]
                    for j, g in Aadj[i]:
                        v = aN + j * N + Tx[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - aN, N)
                    Ty = T[y]
                    for i2, gi in Badj[j]:
                        v = i2 * N + Ty[gi]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _attempt(a, N, d, D, rng, deadline):
    """Anneal voltages over several groups of order N; return (T, darts) on success, else None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUPS_PER_TRY]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        ginv = [inv(g) for g in range(N)]

        M = _random_pattern(a, d, rng)
        darts = []   # entries [i, j, g]
        used = {}    # (i, j) -> set of voltages used in that block
        for i in range(a):
            for j in range(a):
                c = M[i][j]
                if c:
                    gs = rng.sample(range(N), c)
                    used[(i, j)] = set(gs)
                    for g in gs:
                        darts.append([i, j, g])

        def cost():
            Aadj = [[] for _ in range(a)]
            Badj = [[] for _ in range(a)]
            for i, j, g in darts:
                Aadj[i].append((j, g))
                Badj[j].append((i, ginv[g]))
            return _unreached(a, N, D, T, Aadj, Badj)

        cur = cost()
        for it in range(ITERS):
            if cur == 0:
                break
            if (it & 63) == 0 and time.monotonic() > deadline:
                break
            temp = max(0.2, 2.0 * (1.0 - it / ITERS))
            idx = rng.randrange(len(darts))
            i, j, g = darts[idx]
            s = used[(i, j)]
            if len(s) >= N:
                continue
            g2 = rng.randrange(N)
            while g2 in s:
                g2 = rng.randrange(N)
            s.discard(g)
            s.add(g2)
            darts[idx][2] = g2
            v = cost()
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                s.discard(g2)
                s.add(g)
                darts[idx][2] = g
        if cur == 0:
            return T, darts
    return None


def _lift_edges(a, N, T, darts):
    aN = a * N
    edges = []
    for i, j, g in darts:
        for x in range(N):
            edges.append((i * N + x, aN + j * N + T[x][g]))
    return 2 * aN, edges


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 5.0))

    if d < 1 or D < 1:
        return 1, []

    rng = random.Random(seed)
    best = [(1, [])]

    def consider(n, e):
        if n > best[0][0] and lib.is_valid(n, e, d, D):
            best[0] = (n, e)

    # Diameter 1 forces complete bipartite K_{1,1}; degree 1 also gives at most 2 vertices.
    if d == 1 or D == 1:
        consider(2, [(0, 1)])
        return best[0]

    # Moore-optimal incidence graph of PG(2, d-1) when D = 3.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best[0]

    # Safe baselines.
    consider(2 * d, [(i, d + j) for i in range(d) for j in range(d)])   # K_{d,d}, diameter 2
    consider(*lib.haar_graph(d, range(d)))

    Vmax = lib._moore_bound(d, D)
    cur_N = {}
    fails = {}

    while time.monotonic() < deadline:
        progressed = False
        for a in A_LIST:
            if time.monotonic() >= deadline:
                break
            floor_N = max(d + 1, best[0][0] // (2 * a) + 1)
            N = max(cur_N.get(a, 0), floor_N)
            cur_N[a] = N
            if 2 * a * N > Vmax:
                continue
            budget = min(8.0, float(2 ** fails.get(a, 0)))
            att_dl = min(deadline, time.monotonic() + budget)
            res = _attempt(a, N, d, D, rng, att_dl)
            progressed = True
            if res is not None:
                T, darts = res
                n, edges = _lift_edges(a, N, T, darts)
                consider(n, edges)
                cur_N[a] = N + 1
                fails[a] = 0
            else:
                fails[a] = fails.get(a, 0) + 1
        if not progressed:
            break

    if not lib.is_valid(best[0][0], best[0][1], d, D):
        return 1, []
    return best[0]
