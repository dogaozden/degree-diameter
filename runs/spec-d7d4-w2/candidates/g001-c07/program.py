import itertools
import random
import time

import lib

K = 7          # max degree for d = 7
Q = 5          # GQ(5,5) = W(5): degree q+1 = 6, spare degree 1 per vertex


def _gq_structure():
    """Incidence structure of the generalized quadrangle W(5): (points, lines, lines_on_point)."""
    q = Q
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    NP = len(pts)
    index = {v: i for i, v in enumerate(pts)}

    def form(x, y):
        return (x[0] * y[1] - x[1] * y[0] + x[2] * y[3] - x[3] * y[2]) % q

    def norm(v):
        f = next(c for c in v if c)
        inv = pow(f, q - 2, q)
        return tuple((c * inv) % q for c in v)

    found = set()
    for i in range(NP):
        x = pts[i]
        for j in range(i + 1, NP):
            y = pts[j]
            if form(x, y):
                continue
            span = set()
            for a in range(q):
                for b in range(q):
                    if a or b:
                        v = tuple((a * s + b * t) % q for s, t in zip(x, y))
                        span.add(index[norm(v)])
            found.add(tuple(sorted(span)))
    lines = sorted(found)
    if len(lines) != NP or any(len(L) != q + 1 for L in lines):
        return None
    lines_on_point = [[] for _ in range(NP)]
    for li, L in enumerate(lines):
        for p in L:
            lines_on_point[p].append(li)
    if any(len(x) != q + 1 for x in lines_on_point):
        return None
    return NP, lines, lines_on_point


def _dom_search(cover, avail, k, rng, iters, nitems):
    """Find k available items whose closed neighbourhood masks cover all nitems (local search)."""
    cands = [i for i in range(nitems) if avail[i]]
    if len(cands) < k:
        return None
    S = rng.sample(cands, k)

    def cov(sel):
        m = 0
        for i in sel:
            m |= cover[i]
        return m

    curc = nitems - cov(S).bit_count()
    for _ in range(iters):
        if curc == 0:
            return S
        j = rng.randrange(k)
        c = rng.choice(cands)
        if c in S:
            continue
        T = S[:]
        T[j] = c
        cc = nitems - cov(T).bit_count()
        if cc <= curc or rng.random() < 0.02:
            S, curc = T, cc
    return S if curc == 0 else None


def _gq_augment(seed, time_limit, start):
    """Incidence graph of W(5) (312 vertices, degree 6, diameter 4), then add new vertices
    using the one spare degree per vertex. Returns (n, edges) or None."""
    st = _gq_structure()
    if st is None:
        return None
    NP, lines, lon = st
    NL = NP
    N0 = 2 * NP
    base_edges = [(p, NP + li) for li, L in enumerate(lines) for p in L]
    if not lib.is_valid(N0, base_edges, K, 4):
        return None
    best = (N0, base_edges)

    cover_lines = []
    for L in lines:
        m = 0
        for p in L:
            for mm in lon[p]:
                m |= 1 << mm
        cover_lines.append(m)
    cover_points = []
    for p in range(NP):
        m = 0
        for li in lon[p]:
            for r in lines[li]:
                m |= 1 << r
        cover_points.append(m)
    linept = []
    for L in lines:
        m = 0
        for p in L:
            m |= 1 << p
        linept.append(m)

    rng = random.Random(seed)
    deadline = start + 0.6 * time_limit
    A, B = [], []                      # A: (line indices, point mask); B: (point indices, point mask)
    usedL = [False] * NL
    usedP = [False] * NP
    fails, turn = 0, 0
    while time.monotonic() < deadline and fails < 1500:
        turn += 1
        if turn % 2:
            avail = [not u for u in usedL]
            ch = _dom_search(cover_lines, avail, K, rng, 1500, NL)
            if ch is not None:
                pm = 0
                for li in ch:
                    pm |= linept[li]
                if all(pm & mb for _, mb in B):
                    for li in ch:
                        usedL[li] = True
                    A.append((ch, pm))
                    fails = 0
                    continue
        else:
            avail = [not u for u in usedP]
            ch = _dom_search(cover_points, avail, K, rng, 1500, NP)
            if ch is not None:
                mm = 0
                for p in ch:
                    mm |= 1 << p
                if all(pa & mm for _, pa in A):
                    for p in ch:
                        usedP[p] = True
                    B.append((ch, mm))
                    fails = 0
                    continue
        fails += 1

    if not A and not B:
        return best
    edges = list(base_edges)
    nA = len(A)
    for k, (ch, _) in enumerate(A):
        v = N0 + k
        for li in ch:
            edges.append((NP + li, v))
    for k, (ch, _) in enumerate(B):
        w = N0 + nA + k
        for p in ch:
            edges.append((p, w))
    n = N0 + nA + len(B)
    if lib.is_valid(n, edges, K, 4):
        return n, edges
    return best


def _parent(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))          # complete bipartite K_{d,d}: always valid
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
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d == 7 and D == 4:
        try:
            res = _gq_augment(seed, time_limit, start)
            if res is not None:
                return res
        except Exception:
            pass
    remaining = max(1.0, time_limit - (time.monotonic() - start))
    return _parent(d, D, seed, remaining)
