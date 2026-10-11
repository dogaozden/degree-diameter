import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline A: arc-extended projective plane graphs (diameter 3).
#
# From PG(2, q) incidence with spare degree s = d - q - 1 on each vertex, pick a
# point set S where every line holds <= s points of S and every point lies on
# <= s lines indexed by S. Add an A-vertex per point of S and a B-vertex per
# line of S. Diameter stays 3. This is the safe fallback that already reaches
# the record for the target case.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


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
    """Randomized greedy load-bounded point set; returns the largest found."""
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


def _local_improve(m, s, point_lines, line_points, S, rng, deadline, iters):
    """Plateau-walking 1-swap local search growing a feasible load-bounded set."""
    cl = [0] * m
    cp = [0] * m
    inS = [False] * m

    def add(P):
        inS[P] = True
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1

    def rem(P):
        inS[P] = False
        for L in point_lines[P]:
            cl[L] -= 1
        for Q in line_points[P]:
            cp[Q] -= 1

    def fits(P):
        return (all(cl[L] < s for L in point_lines[P])
                and all(cp[Q] < s for Q in line_points[P]))

    cur = list(S)
    for P in cur:
        add(P)
    best = list(cur)
    for it in range(iters):
        if (it & 63) == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        if fits(P):
            add(P)
            cur.append(P)
            if len(cur) > len(best):
                best = list(cur)
            continue
        if not cur:
            continue
        idx = rng.randrange(len(cur))
        R = cur[idx]
        rem(R)
        if fits(P):
            add(P)
            cur[idx] = P
        else:
            add(R)
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
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
    """Return a list of (n, edges) candidates, one per prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index = _pg_data(q)
        cands = []
        if s >= 1:
            g = _greedy_arc(m, s, point_lines, line_points, rng, 40, deadline)
            g = _local_improve(m, s, point_lines, line_points, g, rng, deadline, 3000)
            cands.append(g)
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
# Main new construction: Haar graphs from difference covers.
#
# Let S be a k-subset of Z_m containing 0, with S - S = Z_m (a "difference
# cover"). The Haar graph on a_i, b_j with a_i ~ b_{i+s} (s in S) is bipartite,
# k-regular on 2m vertices, and has diameter <= 3:
#   - a-a and b-b pairs are at distance <= 2 because every difference lies in S-S;
#   - a-b pairs at distance <= 3 because x - s3 lies in S-S for any fixed s3 in S.
# Since |S-S| <= k(k-1)+1, we have m <= k(k-1)+1 (= 241 for k = 16, which is
# the Moore-type ceiling, 482 vertices). Record 394 corresponds to m = 197.
#
# We search for covers by simulated annealing on the number of uncovered
# nonzero residues, with targeted moves that cover a random uncovered residue.
# ----------------------------------------------------------------------------

_TEMP = 0.4


def _init_state(m, k, rng):
    """Random S containing 0, the ordered-difference counts cnt, and the uncovered count U."""
    S = [0] + rng.sample(range(1, m), k - 1)
    cnt = [0] * m
    for s in S:
        for t in S:
            if s != t:
                cnt[(s - t) % m] += 1
    U = sum(1 for x in range(1, m) if cnt[x] == 0)
    return S, cnt, U


def _move(m, S, cnt, i, new):
    """Replace S[i] by new, updating cnt in place; return the change in the uncovered count.

    Calling again with the old value undoes the move exactly.
    """
    old = S[i]
    delta = 0
    for j, t in enumerate(S):
        if j != i:
            for x in ((old - t) % m, (t - old) % m):
                cnt[x] -= 1
                if cnt[x] == 0:
                    delta += 1
    S[i] = new
    for j, t in enumerate(S):
        if j != i:
            for x in ((new - t) % m, (t - new) % m):
                if cnt[x] == 0:
                    delta -= 1
                cnt[x] += 1
    return delta


def _pick_uncovered(cnt, m, rng):
    """Return a random residue in 1..m-1 that is not yet a difference."""
    for _ in range(16):
        x = rng.randrange(1, m)
        if cnt[x] == 0:
            return x
    cands = [x for x in range(1, m) if cnt[x] == 0]
    return rng.choice(cands) if cands else rng.randrange(1, m)


def _search_cover(m, k, rng, deadline):
    """Anneal a k-element difference cover of Z_m containing 0; return it, or None on timeout."""
    S, cnt, U = _init_state(m, k, rng)
    best_U = U
    stall = 0
    it = 0
    while U > 0:
        it += 1
        if (it & 255) == 0 and time.monotonic() >= deadline:
            return None
        if stall > 50000:
            S, cnt, U = _init_state(m, k, rng)
            best_U = U
            stall = 0
            continue
        i = rng.randrange(1, k)  # keep 0 in S (translation invariance)
        if rng.random() < 0.7:
            x = _pick_uncovered(cnt, m, rng)
            t = S[rng.randrange(k)]
            new = (x + t) % m if rng.random() < 0.5 else (t - x) % m
        else:
            new = rng.randrange(1, m)
        if new in S:
            stall += 1
            continue
        old = S[i]
        delta = _move(m, S, cnt, i, new)
        if delta <= 0 or rng.random() < math.exp(-delta / _TEMP):
            U += delta
        else:
            _move(m, S, cnt, i, old)
        if U < best_U:
            best_U = U
            stall = 0
        else:
            stall += 1
    return list(S)


def _best_cover(k, deadline, rng):
    """Find the largest m (with a k-element difference cover) that the time budget allows.

    Works upward from a floor. Each round retries every m above the current best
    with a doubled per-attempt time slice, so the search climbs as far as it can.
    Returns (m, S) or None.
    """
    mmax = k * (k - 1) + 1
    lo = max(k, int(0.8 * mmax))
    best = None
    slc = 0.15
    while time.monotonic() < deadline:
        s0 = best[0] + 1 if best else lo
        if s0 > mmax:
            break
        for m in range(s0, mmax + 1):
            now = time.monotonic()
            if now >= deadline:
                break
            S = _search_cover(m, k, rng, min(deadline, now + slc))
            if S is not None:
                best = (m, S)
        slc = min(slc * 2, 8.0)
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2 or d < 2:
        return best
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Stage A: arc-extended projective plane (reaches the record baseline quickly).
    for n_c, e_c in _arc_extensions(d, start + 0.2 * time_limit,
                                    random.Random(seed * 7919 + d)):
        consider(n_c, e_c)

    # Stage B: Haar graph from a difference cover of Z_m with |S| = d.
    # Diameter 3 <= D, so this is valid for every D >= 3.
    res = _best_cover(d, deadline, rng)
    if res is not None:
        m, S = res
        n, e = lib.haar_graph(m, S)
        consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
