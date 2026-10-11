import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Floor construction (D = 3): arc-extended projective plane, PG(2,q) + A/B vertices.
# ----------------------------------------------------------------------------

def _loads_ok(S, s, m, pl, lp):
    """Every line holds <= s points of S and every point lies on <= s lines of S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, pl, lp, rng, trials, deadline):
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
            if all(cl[L] < s for L in pl[P]) and all(cp[Q] < s for Q in lp[P]):
                S.append(P)
                for L in pl[P]:
                    cl[L] += 1
                for Q in lp[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _arc_graph(m, edges, pl, lp, S):
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):          # new A-vertex per point of S, joined to its lines
        x = 2 * m + t
        for L in pl[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):          # new B-vertex per line of S, joined to its points
        b = 2 * m + k + t
        for Q in lp[j]:
            E.append((Q, b))
    return n, E


def _arc_candidates(d, deadline, rng):
    out = []
    for q in range(min(d - 1, 23), 1, -1):
        if time.monotonic() > deadline:
            break
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 1:
            continue
        pts = lib.projective_points(q)
        index = {p: i for i, p in enumerate(pts)}
        n2, edges = lib.projective_plane_incidence(q)
        m = n2 // 2
        pl = [[] for _ in range(m)]
        lp = [[] for _ in range(m)]
        for u, v in edges:
            pl[u].append(v - m)
            lp[v - m].append(u)
        cands = [_greedy_arc(m, s, pl, lp, rng, 30, deadline)]
        if q % 2 == 1 and s >= 2:
            F = lib.GF(q)
            cs = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
            cands.append(cs)
        S = max(cands, key=len)
        if not S or not _loads_ok(S, s, m, pl, lp):
            continue
        out.append(_arc_graph(m, edges, pl, lp, S))
    return out


# ----------------------------------------------------------------------------
# New bold family (D = 3): Haar graphs H(m, S) with |S| = d and S - S = Z_m.
#
# In H(m, S), A-A distances are even and equal the differences s_i - s_j, so
# diameter 3 holds exactly when the ordered differences of S cover Z_m \ {0}
# (A-B distances are then at most 3 because 0 is in S). Since |S|(|S|-1)
# differences exist, m <= 1 + d(d-1), which gives the Moore-type cap 2 + 2d(d-1).
# We search for difference covers by annealing on the number of uncovered residues.
# ----------------------------------------------------------------------------

def _replace(cnt, S, i, new, m):
    """Replace S[i] by new, updating ordered-difference counts; return the change in uncovered count."""
    old = S[i]
    dz = 0
    for j, x in enumerate(S):
        if j == i:
            continue
        for df in ((old - x) % m, (x - old) % m):
            cnt[df] -= 1
            if cnt[df] == 0:
                dz += 1
    for j, x in enumerate(S):
        if j == i:
            continue
        for df in ((new - x) % m, (x - new) % m):
            if cnt[df] == 0:
                dz -= 1
            cnt[df] += 1
    S[i] = new
    return dz


def _cover_search(d, m, rng, deadline):
    """Find S (size d, 0 in S) in Z_m whose ordered differences cover all nonzero residues."""
    S = [0] + rng.sample(range(1, m), d - 1)
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    zeros = sum(1 for r in range(1, m) if cnt[r] == 0)
    it = 0
    while zeros > 0:
        it += 1
        if (it & 127) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(1, d)
        new = rng.randrange(1, m)
        if new in S:
            continue
        old = S[i]
        dz = _replace(cnt, S, i, new, m)
        if dz <= 0 or rng.random() < math.exp(-dz / 0.8):
            zeros += dz
        else:
            _replace(cnt, S, i, old, m)
    return S


# ----------------------------------------------------------------------------
# Generic Haar hill-climb for D >= 4 (not the focus; kept as a safe secondary family).
# ----------------------------------------------------------------------------

def _haar_bad_search(d, D, m, rng, deadline, iters):
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    if D == 3:
        # Floor: arc-extended projective plane (already matches the record for d = 16).
        for n_c, e_c in _arc_candidates(d, start + 0.3 * time_limit, rng):
            consider(n_c, e_c)

        # New family: Haar graphs over Z_m with difference-covering connection sets.
        # Only orders above the current best matter, so start just above it.
        m = max(d + 1, best_n // 2 + 1)
        moore = 1 + d * (d - 1)
        while m <= moore and time.monotonic() < deadline:
            now = time.monotonic()
            slice_end = now + 0.5 * (deadline - now)
            S = _cover_search(d, m, rng, slice_end)
            if S is not None:
                n_c, e_c = lib.haar_graph(m, S)
                consider(n_c, e_c)
            m += 1
    else:
        m = d + 1
        cap = lib._moore_bound(d, D) // 2
        while m <= cap and time.monotonic() < deadline:
            now = time.monotonic()
            slice_end = now + 0.2 * (deadline - now)
            S = _haar_bad_search(d, D, m, rng, slice_end, 150)
            if S is not None:
                n_c, e_c = lib.haar_graph(m, S)
                consider(n_c, e_c)
            m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
