import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
# Start from PG(2, q) incidence (every vertex has degree q+1). With d >= q+1
# each vertex has spare capacity s = d - q - 1. Choose a point set S whose
# line-loads and point-loads are <= s, then add an A-vertex per point of S
# (joined to the lines through it) and a B-vertex per line of S (joined to
# the points on it).
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 30, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# NEW bold construction for D = 3: multi-orbit bi-Cayley graphs.
#
# Vertices: A_i = {a_{i,g}}, B_j = {b_{j,g}} for g in Z_m, i, j in 0..k-1.
# Blocks: for each (i, j) a set S_ij of shifts in Z_m, with edges
#     a_{i,g} ~ b_{j,g+s}   for s in S_ij.
# Row sums and column sums of the block-size matrix M (|S_ij|) equal d, so the
# graph is d-regular on 2km vertices and bipartite. Translation by Z_m is an
# automorphism, so distances from all vertices follow from the 2k
# representatives a_{i,0}, b_{j,0}. Simulated annealing moves single shifts to
# minimise the number of (representative, vertex) pairs at distance > 3.
# Bitsets over Z_m make each cost evaluation cheap.
# k = 1 is the cyclic Haar case; k = 2, 3, 4 give 2km-vertex graphs.
# ----------------------------------------------------------------------------

def _rotl(X, s, m, mask):
    """Cyclic left rotation of the m-bit set X by s: bit g -> bit (g + s) mod m."""
    s %= m
    if s == 0:
        return X
    return ((X << s) | (X >> (m - s))) & mask


def _perm_matrix(k, d, rng):
    """Block-size matrix M (k x k) with all row and column sums equal to d."""
    sigma = list(range(k))
    tau = list(range(k))
    rng.shuffle(sigma)
    rng.shuffle(tau)
    c = rng.randint(0, d)
    M = [[0] * k for _ in range(k)]
    for i in range(k):
        M[i][sigma[i]] += c
        M[i][tau[i]] += d - c
    return M


def _bi_cost(m, k, blocks):
    """Number of (representative, vertex) pairs not reached within distance 3. Zero means diameter <= 3."""
    mask = (1 << m) - 1
    fw = []
    bw = []
    for i, j, S in blocks:
        for s in S:
            fw.append((i, j, s))
            bw.append((j, i, (m - s) % m))
    total = 0
    for side in (0, 1):
        for idx in range(k):
            A = [0] * k
            B = [0] * k
            if side == 0:
                A[idx] = 1
            else:
                B[idx] = 1
            for _ in range(3):
                nA = A[:]
                nB = B[:]
                for i, j, s in fw:
                    x = A[i]
                    if x:
                        nB[j] |= _rotl(x, s, m, mask)
                for j, i, s in bw:
                    y = B[j]
                    if y:
                        nA[i] |= _rotl(y, s, m, mask)
                A, B = nA, nB
            reached = sum(x.bit_count() for x in A) + sum(x.bit_count() for x in B)
            total += 2 * k * m - reached
    return total


def _bi_search(d, k, m, deadline, rng):
    """Anneal shift sets for a random block pattern. Returns blocks [(i, j, S)] with zero cost, or None."""
    M = _perm_matrix(k, d, rng)
    if max(max(row) for row in M) > m:
        return None
    blocks = []
    for i in range(k):
        for j in range(k):
            if M[i][j] > 0:
                blocks.append([i, j, rng.sample(range(m), M[i][j])])
    if not blocks:
        return None
    cost = _bi_cost(m, k, blocks)
    T = 1.5
    it = 0
    while cost > 0:
        it += 1
        if (it & 63) == 0 and time.monotonic() > deadline:
            return None
        if it % 20000 == 0:
            T = 1.0  # reheat
        T = max(0.2, T * 0.9995)
        blk = rng.choice(blocks)
        S = blk[2]
        pos = rng.randrange(len(S))
        new = rng.randrange(m)
        if new in S:
            continue
        old = S[pos]
        S[pos] = new
        c2 = _bi_cost(m, k, blocks)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = c2
        else:
            S[pos] = old
    return blocks if cost == 0 else None


def _bi_graph(m, k, blocks):
    """Explicit (n, edges) of the multi-orbit bi-Cayley graph."""
    E = set()
    for i, j, S in blocks:
        for s in S:
            for g in range(m):
                E.add((i * m + g, k * m + j * m + (g + s) % m))
    return 2 * k * m, sorted(E)


def _bi_orbit_search(d, best_n, deadline, rng):
    """Search k-orbit bi-Cayley graphs with order above best_n. Returns (n, edges) or None."""
    cap = lib.moore_bound(d, 3)
    targets = {k: best_n // (2 * k) + 1 for k in (1, 2, 3, 4)}
    ks = [2, 2, 3, 3, 4, 1]
    best = None
    best_n_loc = best_n
    while time.monotonic() < deadline:
        live = [k for k in ks if 2 * k * targets[k] <= cap]
        if not live:
            break
        k = rng.choice(live)
        m = targets[k]
        now = time.monotonic()
        slice_end = min(deadline, now + max(2.0, 0.2 * (deadline - now)))
        blocks = _bi_search(d, k, m, slice_end, rng)
        if blocks is not None:
            n, e = _bi_graph(m, k, blocks)
            if n > best_n_loc and lib.is_valid(n, e, d, 3):
                best_n_loc = n
                best = (n, e)
            targets[k] = max(targets[k], m + 1)
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(cand):
        nonlocal best, best_n
        if cand is None:
            return
        n, e = cand
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        arcs = _arc_extensions(d, start + 0.10 * time_limit,
                               random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for cand in arcs[:3]:
            consider(cand)

    if D == 3:
        try:
            consider(_bi_orbit_search(d, best_n, start + 0.85 * time_limit, rng))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
