import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane arc-extension family (D = 3).
#
# PG(2, q) incidence plus spare degree s = d - q - 1. Choose a point set S
# (also used as a line set via the same vectors) with every line holding <= s
# points of S and every point on <= s lines of S. Add an A-vertex per point of S
# (joined to its q+1 lines) and a B-vertex per line of S (joined to its q+1
# points). Degrees stay <= d and the diameter stays 3.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return m, edges, pl, lp


def _loads_ok(S, s, m, pl, lp):
    """True if all line loads and point loads of S are <= s."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, pl, lp, rng, trials, deadline):
    """Randomized greedy S with all loads <= s; returns the largest found."""
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


def _conic(q, index):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _local_arc(m, s, pl, lp, S0, rng, deadline):
    """Iterated local search for a large feasible S, starting from feasible S0."""
    cl = [0] * m
    cp = [0] * m
    inS = [False] * m
    S = []

    def add(P):
        inS[P] = True
        S.append(P)
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1

    def remove(P):
        inS[P] = False
        S.remove(P)
        for L in pl[P]:
            cl[L] -= 1
        for Q in lp[P]:
            cp[Q] -= 1

    def blockers(P):
        satL = {L for L in pl[P] if cl[L] >= s}
        satQ = {Q for Q in lp[P] if cp[Q] >= s}
        if not satL and not satQ:
            return []
        return [R for R in S
                if any(L in satL for L in pl[R]) or any(Q in satQ for Q in lp[R])]

    for P in S0:
        add(P)
    best = list(S)
    it = 0
    while True:
        it += 1
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        B = blockers(P)
        if not B:
            add(P)
        elif len(B) == 1 or (len(B) == 2 and rng.random() < 0.05):
            for R in B:
                remove(R)
            add(P)
        else:
            continue
        if len(S) > len(best):
            best = list(S)
    return best


def _arc_graph(m, edges, pl, lp, S):
    """Incidence graph of PG(2,q) plus an A-vertex and a B-vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        a = 2 * m + t
        for L in pl[P]:
            E.append((a, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in lp[j]:
            E.append((Q, b))
    return n, E


def _arc_family(d, best_n, deadline, rng):
    """Build arc-extended PG(2,q) candidates, sharing the time budget across q."""
    qs = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 1:
            continue
        m = q * q + q + 1
        bound = 2 * m + 2 * (s * m // (q + 1))
        if bound > best_n:
            qs.append((bound, q, s))
    qs.sort(reverse=True)

    out = []
    for idx, (_bound, q, s) in enumerate(qs):
        now = time.monotonic()
        if now >= deadline:
            break
        share = (deadline - now) / (len(qs) - idx)
        qd = now + share
        m, edges, pl, lp = _pg_data(q)
        index = {p: i for i, p in enumerate(lib.projective_points(q))}
        cands = [_greedy_arc(m, s, pl, lp, rng, 30, now + 0.25 * share)]
        if s >= 2:
            cs = _conic(q, index)
            if _loads_ok(cs, s, m, pl, lp):
                cands.append(cs)
        S0 = max(cands, key=len)
        if not _loads_ok(S0, s, m, pl, lp):
            S0 = []
        S = _local_arc(m, s, pl, lp, S0, rng, qd)
        if S and _loads_ok(S, s, m, pl, lp):
            out.append(_arc_graph(m, edges, pl, lp, S))
    return out


# ----------------------------------------------------------------------------
# Haar graphs from difference covers (D = 3).
#
# H(m, S) with |S| = d is d-regular bipartite on 2m vertices. It has diameter 3
# whenever S - S = Z_m. We anneal over S to cover all nonzero differences, and
# climb m upward while covers are found.
# ----------------------------------------------------------------------------

def _cover_search(k, m, rng, deadline):
    """Find S subset of Z_m, |S| = k, with S - S = Z_m. Returns sorted S or None."""
    if m < k:
        return None
    S = rng.sample(range(m), k)
    in_s = set(S)
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    unc = sum(1 for g in range(1, m) if cnt[g] == 0)
    it = 0
    while unc > 0:
        it += 1
        if (it & 1023) == 0 and time.monotonic() > deadline:
            return None
        T = 0.4 * (0.1 ** ((it % 300000) / 300000.0))
        i = rng.randrange(k)
        x = S[i]
        y = rng.randrange(m)
        if y in in_s:
            continue
        others = S[:i] + S[i + 1:]
        delta = 0
        for s in others:
            g = (x - s) % m
            cnt[g] -= 1
            if cnt[g] == 0:
                delta += 1
            g = (s - x) % m
            cnt[g] -= 1
            if cnt[g] == 0:
                delta += 1
        for s in others:
            g = (y - s) % m
            if cnt[g] == 0:
                delta -= 1
            cnt[g] += 1
            g = (s - y) % m
            if cnt[g] == 0:
                delta -= 1
            cnt[g] += 1
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = y
            in_s.discard(x)
            in_s.add(y)
            unc += delta
        else:
            for s in others:
                cnt[(y - s) % m] -= 1
                cnt[(s - y) % m] -= 1
            for s in others:
                cnt[(x - s) % m] += 1
                cnt[(s - x) % m] += 1
    return sorted(S)


def _haar_search(k, rng, deadline):
    """Climb m upward from a moderate start, keeping the largest m with a difference cover."""
    if k < 2:
        return None
    mmax = k * (k - 1) + 1
    m = max(k, int(0.6 * mmax))
    best = None
    fails = 0
    while m <= mmax and time.monotonic() < deadline:
        rem = deadline - time.monotonic()
        S = _cover_search(k, m, rng, time.monotonic() + max(1.0, 0.3 * rem))
        if S is not None:
            best = (m, S)
            fails = 0
        else:
            fails += 1
            if fails >= 3:
                break
        m += 1
    return best


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D >= 4)
# ----------------------------------------------------------------------------

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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.8 * float(time_limit), 48.0)
    deadline = start + budget
    rng = random.Random(seed * 1000003 + 17 * d + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, list(E)

    if D == 3:
        # Arc-extended projective planes get an early share of the budget.
        arc_deadline = start + 0.3 * budget
        for n_c, E_c in _arc_family(d, best_n, arc_deadline, random.Random(seed * 7919 + d)):
            consider(n_c, E_c)
        # Haar graphs from difference covers get the rest.
        res = _haar_search(d, rng, deadline)
        if res is not None:
            m, S = res
            n, E = lib.haar_graph(m, S)
            consider(n, E)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
