import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Algebraic starting graphs (d-regular bipartite).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); (q+1)-regular, diameter 4."""
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


def _kdd(d):
    """K_{d,d}: d-regular, diameter 2, always valid for D >= 2."""
    return 2 * d, [(2 * i, 2 * j + 1) for i in range(d) for j in range(d)]


def _to_state(n, edges, d):
    """Relabel a d-regular bipartite graph so left vertices are even ids, right vertices odd ids.

    Returns (N, E) with E a list of (left, right) pairs, or None if the graph does not fit.
    """
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != d for a in adj):
        return None
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    ids = [0] * n
    nl = nr = 0
    for v in range(n):
        if color[v] == 0:
            ids[v] = 2 * nl
            nl += 1
        else:
            ids[v] = 2 * nr + 1
            nr += 1
    if nl != nr:
        return None
    E = []
    for u, v in edges:
        if color[u] == 0:
            E.append((ids[u], ids[v]))
        else:
            E.append((ids[v], ids[u]))
    return 2 * nl, E


# ----------------------------------------------------------------------------
# Vertex-pair growth with edge-switch annealing.
#
# State: a d-regular bipartite graph on N vertices (left = even ids, right = odd ids)
# stored as an edge list E of (left, right) pairs.
# Growth step: pick d edges with pairwise distinct endpoints (a matching M),
# delete them, add a new left vertex x joined to the right ends and a new right
# vertex y joined to the left ends. Degrees are preserved, so the graph stays
# d-regular bipartite. Then anneal with double-edge switches that minimise the
# number of vertex pairs at distance > D.
# ----------------------------------------------------------------------------

def _build_adj(N, E):
    adj = [[] for _ in range(N)]
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _bad(N, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs included)."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        nxt = [0] * N
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt[v] = r
        reach = nxt
    return sum(N - r.bit_count() for r in reach) // 2


def _switch(E, eset, adj, i, j):
    """Double-edge switch: (a,b),(c,e) -> (a,e),(c,b). Involution: applying it again undoes it."""
    a, b = E[i]
    c, e = E[j]
    if a == c or b == e:
        return False
    if (a, e) in eset or (c, b) in eset:
        return False
    eset.discard((a, b))
    eset.discard((c, e))
    eset.add((a, e))
    eset.add((c, b))
    E[i] = (a, e)
    E[j] = (c, b)
    adj[a].remove(b)
    adj[a].append(e)
    adj[b].remove(a)
    adj[b].append(c)
    adj[c].remove(e)
    adj[c].append(b)
    adj[e].remove(c)
    adj[e].append(a)
    return True


def _extend(E, N, d, rng):
    """Add one left and one right vertex, keeping d-regularity. Returns (E2, N2) or None."""
    m = len(E)
    idx = list(range(m))
    rng.shuffle(idx)
    us, vs, pick = set(), set(), []
    for i in idx:
        u, v = E[i]
        if u in us or v in vs:
            continue
        us.add(u)
        vs.add(v)
        pick.append(i)
        if len(pick) == d:
            break
    if len(pick) < d:
        return None
    x, y = N, N + 1
    E2 = list(E)
    for i in pick:
        u, v = E2[i]
        E2[i] = (x, v)      # new left vertex x joined to right end v
        E2.append((u, y))   # new right vertex y joined to left end u
    return E2, N + 2


def _anneal(E, eset, adj, N, D, rng, deadline, iters):
    """Anneal double-edge switches until no bad pairs remain. Returns final bad-pair count."""
    cur = _bad(N, adj, D)
    m = len(E)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        if not _switch(E, eset, adj, i, j):
            continue
        c2 = _bad(N, adj, D)
        delta = c2 - cur
        T = 1.0 * (0.02 ** (it / iters))
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c2
        else:
            _switch(E, eset, adj, i, j)  # undo
    return cur


def _grow(E0, N0, d, D, deadline, rng, iters, tries):
    """Repeatedly grow by one vertex pair per side; returns the largest valid (N, E) reached."""
    E, N = list(E0), N0
    fails = 0
    while time.monotonic() < deadline and fails < tries:
        ext = _extend(E, N, d, rng)
        if ext is None:
            break
        E2, N2 = ext
        eset = set(E2)
        adj = _build_adj(N2, E2)
        budget = iters * (1 + fails)
        cur = _anneal(E2, eset, adj, N2, D, rng, deadline, budget)
        if cur == 0:
            E, N = E2, N2
            fails = 0
        else:
            fails += 1
    return N, E


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    fb_n, fb_e = _kdd(d)
    start_n, start_e = fb_n, fb_e

    # Algebraic candidates with degree d; keep the largest that validates.
    q = d - 1
    if lib.is_prime_power(q):
        cands = []
        if D >= 4 and q <= 9:
            cands.append(_gq_w(q))
        if D >= 3:
            cands.append(lib.projective_plane_incidence(q))
        for n_c, e_c in cands:
            if n_c > start_n and lib.is_valid(n_c, e_c, d, D):
                start_n, start_e = n_c, e_c

    # Moore-bound graphs need no search.
    if start_n >= lib._moore_bound(d, D):
        return start_n, start_e

    st = _to_state(start_n, start_e, d)
    if st is None:
        return fb_n, fb_e
    N, E = st

    grown_N, grown_E = N, E
    stalls = 0
    while time.monotonic() < deadline and stalls < 4:
        N2, E2 = _grow(grown_E, grown_N, d, D, deadline, rng, 1500, 5)
        if N2 > grown_N:
            grown_N, grown_E = N2, E2
            stalls = 0
        else:
            stalls += 1

    out_edges = [(int(u), int(v)) for u, v in grown_E]
    if grown_N > start_n and lib.is_valid(grown_N, out_edges, d, D):
        return grown_N, out_edges

    if lib.is_valid(start_n, start_e, d, D):
        return start_n, start_e
    return fb_n, fb_e
