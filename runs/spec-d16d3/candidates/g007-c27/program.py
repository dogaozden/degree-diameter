import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane base and "cover families" for diameter-3 vertex extension.
#
# Base: incidence graph of PG(2, q): points 0..m-1, lines m..2m-1, degree q+1.
#
# Extension (new idea): add A-vertices on the point side and B-vertices on the
# line side.
#   * An A-vertex is joined to a set T of lines that covers every point, with
#     |T| <= d. Every line may lie in at most s = d-q-1 such sets (its spare
#     degree).
#   * Any two A-sets must share a line, so that two A-vertices are at distance 2.
#   * B-vertices are the exact dual: a set P of points covering every line,
#     pairwise sharing a point, each point used at most s times.
#
# Under these rules the diameter stays 3 for any choice of sets. Check:
#   point-point, line-line: distance 2 (as in PG(2,q)); point-line: 3.
#   A-A and B-B: distance 2 by the shared line/point.
#   A-point and B-line: 2 by covering.
#   A-line (not in T) and B-point (not in P): 3, via the covering property.
#   A-B: 3, since any line of T contains a point of P.
# Each side is independent (A uses only line spare, B only point spare), so the
# two families are optimised separately. The pencil-based "conic" family, the
# parent's arc extension in dual form, is kept as a fallback.
# ----------------------------------------------------------------------------


def _pg(q):
    """Return (m, edges, pl, lp): pl[P] = lines through point P, lp[L] = points on line L."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return m, edges, pl, lp


def _try_cover(cov, inc, full, ny, s, d, usage, members, nfam, rng):
    """Randomised greedy search for one set T (|T| <= d) covering all of `full`.

    cov[y] is a bitmask over the X side of the elements y covers.
    inc[x] lists the y containing x. T must meet every existing family set
    (members/unhit bookkeeping) and every y in T must have usage < s.
    Returns the list T, or None on failure.
    """
    unhit = set(range(nfam))
    chosen = []
    in_t = [False] * ny
    covered = 0

    # Sometimes seed with all usable elements through one random X element
    # (a "pencil" seed): this tends to produce perfect covers.
    if rng.random() < 0.5:
        x = rng.randrange(len(inc))
        for y in inc[x]:
            if usage[y] < s and len(chosen) < d:
                chosen.append(y)
                in_t[y] = True
                covered |= cov[y]
                for k in members[y]:
                    unhit.discard(k)

    while True:
        if covered == full and not unhit:
            return chosen
        if len(chosen) >= d:
            return None
        best, best_score = -1, -1.0
        for y in range(ny):
            if usage[y] >= s or in_t[y]:
                continue
            gain = (cov[y] & ~covered).bit_count()
            hit = 0
            for k in members[y]:
                if k in unhit:
                    hit += 1
            if gain == 0 and hit == 0:
                continue
            score = 20.0 * hit + gain + 2.0 * rng.random()
            if score > best_score:
                best_score = score
                best = y
        if best < 0:
            return None
        chosen.append(best)
        in_t[best] = True
        covered |= cov[best]
        for k in members[best]:
            unhit.discard(k)


def _family(cov, inc, m, s, d, deadline, rng):
    """Greedily build pairwise-intersecting covers, each element used at most s times."""
    full = (1 << m) - 1
    ny = len(cov)
    usage = [0] * ny
    members = [[] for _ in range(ny)]
    fam = []
    fails = 0
    while time.monotonic() < deadline and fails < 300:
        T = _try_cover(cov, inc, full, ny, s, d, usage, members, len(fam), rng)
        if T is None:
            fails += 1
            continue
        k = len(fam)
        fam.append(T)
        fails = 0
        for y in T:
            usage[y] += 1
            members[y].append(k)
    return fam


def _conic_family(q, pl, lp):
    """Pencils at a conic (plus nucleus for even q) and their duals: the parent's arc extension."""
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    fa = [list(pl[P]) for P in S]
    fb = [list(lp[L]) for L in S]
    return fa, fb


def _assemble(m, edges, fa, fb):
    """Base PG graph plus A-vertices (on the point side) and B-vertices (on the line side)."""
    n = 2 * m + len(fa) + len(fb)
    E = list(edges)
    for j, T in enumerate(fa):
        a = 2 * m + j
        E.extend((m + L, a) for L in T)
    base = 2 * m + len(fa)
    for i, T in enumerate(fb):
        b = base + i
        E.extend((P, b) for P in T)
    return n, E


def _build_for_q(q, s, d, deadline, rng, consider):
    """Run the cover-family search for PG(2, q) with spare capacity s on each vertex."""
    if s < 1:
        return
    m, edges, pl, lp = _pg(q)
    covA = [sum(1 << P for P in lp[L]) for L in range(m)]  # line L covers its points
    covB = [sum(1 << L for L in pl[P]) for P in range(m)]  # point P covers its lines
    fa_c, fb_c = _conic_family(q, pl, lp)
    best_fa, best_fb = fa_c, fb_c
    consider(*_assemble(m, edges, best_fa, best_fb))
    while time.monotonic() < deadline:
        dl = min(deadline, time.monotonic() + 4.0)
        f = _family(covA, pl, m, s, d, dl, rng)
        if len(f) > len(best_fa):
            best_fa = f
        dl = min(deadline, time.monotonic() + 4.0)
        g = _family(covB, lp, m, s, d, dl, rng)
        if len(g) > len(best_fb):
            best_fb = g
        consider(*_assemble(m, edges, best_fa, best_fb))


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D < 3:
        return best

    qs = [q for q in range(2, d) if lib.is_prime_power(q)]
    if not qs:
        return best

    # Plain projective plane for the largest usable prime power.
    qmax = max(qs)
    consider(*lib.projective_plane_incidence(qmax))

    jobs = []
    for q in qs:
        s = d - q - 1
        mm = q * q + q + 1
        bound = 2 * mm + (2 * (s * mm // (q + 1)) if s > 0 else 0)
        jobs.append((bound, q, s))
    jobs.sort(reverse=True)

    for idx, (bound, q, s) in enumerate(jobs):
        if bound <= best_n:
            continue
        now = time.monotonic()
        remaining = end - now
        if remaining <= 0.5:
            break
        left = sum(1 for b, _, _ in jobs[idx:] if b > best_n)
        dl = now + remaining / max(1, left)
        try:
            _build_for_q(q, s, d, dl, rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
