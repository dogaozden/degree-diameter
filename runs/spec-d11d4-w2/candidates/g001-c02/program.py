import itertools
import random
import sys
import time

import lib


def _largest_prime_power_at_most(m):
    """Return the largest prime power q with 2 <= q <= m, or None."""
    for q in range(m, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _gq_incidence(q):
    """Incidence structure of the generalized quadrangle W(q), q odd or even.

    Points: projective points of PG(3, q). Lines: totally isotropic lines of the
    symplectic form x0*y1 - x1*y0 + x2*y3 - x3*y2. Returns (N, lines), where N is
    the number of points and lines is a list of sorted point-index lists.
    """
    F = lib.GF(q)
    vecs = [v for v in itertools.product(range(q), repeat=4)
            if any(v) and next(x for x in v if x) == 1]
    N = len(vecs)
    idx = {v: i for i, v in enumerate(vecs)}

    def point_of(v):
        c = next((x for x in v if x), 0)
        if c == 0:
            return None
        if c != 1:
            ci = F.inv(c)
            v = tuple(F.mul(ci, x) for x in v)
        return idx[v]

    def isotropic(x, y):
        s = F.add(F.mul(x[0], y[1]), F.mul(x[2], y[3]))
        t = F.add(F.mul(x[1], y[0]), F.mul(x[3], y[2]))
        return s == t

    covered = set()
    lines = []
    for i in range(N):
        x = vecs[i]
        for j in range(i + 1, N):
            if i * N + j in covered:
                continue
            y = vecs[j]
            if not isotropic(x, y):
                continue
            members = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    p = point_of(v)
                    if p is not None:
                        members.add(p)
            mem = sorted(members)
            for s in range(len(mem)):
                for t in range(s + 1, len(mem)):
                    covered.add(mem[s] * N + mem[t])
            lines.append(mem)
    return N, lines


def _augment(p, adj, seen, mL, mR):
    """Kuhn augmenting-path step for left vertex p."""
    for l in adj[p]:
        if not seen[l]:
            seen[l] = True
            if mR[l] == -1 or _augment(mR[l], adj, seen, mL, mR):
                mR[l] = p
                mL[p] = l
                return True
    return False


def _gq_with_extra(d):
    """W(q) incidence graph with q the largest prime power with q+1 <= d.

    It has diameter 4 and degree q+1. The remaining d-(q+1) degree is used by
    adding point-line matchings between non-incident pairs. Adding edges never
    increases distances, so the diameter stays 4 and bipartiteness is kept.
    """
    q = _largest_prime_power_at_most(d - 1)
    if q is None:
        return None
    N, lines = _gq_incidence(q)
    L = len(lines)
    edges = [(p, N + li) for li, mem in enumerate(lines) for p in mem]
    inc = [set() for _ in range(N)]
    for li, mem in enumerate(lines):
        for p in mem:
            inc[p].add(li)

    used = set()
    for _ in range(d - (q + 1)):
        adj = [[l for l in range(L) if l not in inc[p] and (p, l) not in used]
               for p in range(N)]
        mL = [-1] * N
        mR = [-1] * L
        for p in range(N):  # greedy initial matching
            for l in adj[p]:
                if mR[l] == -1:
                    mR[l] = p
                    mL[p] = l
                    break
        for p in range(N):  # augment the rest
            if mL[p] == -1:
                seen = [False] * L
                _augment(p, adj, seen, mL, mR)
        for p in range(N):
            if mL[p] != -1:
                edges.append((p, N + mL[p]))
                used.add((p, mL[p]))
    return N + L, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    sys.setrecursionlimit(max(10000, sys.getrecursionlimit()))
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    # Main construction for diameter >= 4: generalized quadrangle plus matchings.
    gq = None
    if D >= 4 and d >= 3:
        try:
            cand = _gq_with_extra(d)
            if cand is not None and lib.is_valid(cand[0], cand[1], d, D):
                gq = cand
        except Exception:
            gq = None
    if gq is not None and D == 4:
        return gq

    # Fallback: Haar-graph search (used for other diameters).
    rng = random.Random(seed)
    fallback = lib.haar_graph(d, range(d))  # K_{d,d}: always valid
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            fallback, misses = found, 0
        else:
            misses += 1
        m += 1

    if gq is not None and gq[0] >= fallback[0]:
        return gq
    return fallback
