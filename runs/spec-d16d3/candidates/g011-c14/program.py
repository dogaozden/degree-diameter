import math
import random
import time

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Base family: PG(2, q) incidence graph plus an arc-extension on spare degree.
# ----------------------------------------------------------------------------

def _loads_ok(S, s, m, pl, lp):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, pl, lp, rng, trials):
    """Randomized greedy arc with all loads <= s; returns the largest set found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
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


def _conic_set(q, index):
    """Conic (plus nucleus for even q) as point indices."""
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, pl, lp, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in pl[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in lp[j]:
            E.append((Q, b))
    return n, E


def _pg_arc_best(d):
    """Largest valid PG(2,q)+arc graph with degree <= d, or None."""
    rng = random.Random(12345)
    best = None
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 0:
            continue
        n2, edges = lib.projective_plane_incidence(q)
        m = n2 // 2
        cand = (n2, edges)
        if s >= 1:
            pl = [[] for _ in range(m)]
            lp = [[] for _ in range(m)]
            for u, v in edges:
                pl[u].append(v - m)
                lp[v - m].append(u)
            pts = lib.projective_points(q)
            index = {p: i for i, p in enumerate(pts)}
            arcs = []
            g = _greedy_arc(m, s, pl, lp, rng, 40)
            arcs.append(g)
            if s >= 2:
                cs = _conic_set(q, index)
                arcs.append(cs)
            for S in arcs:
                if S and _loads_ok(S, s, m, pl, lp):
                    n_c, e_c = _arc_graph(m, edges, pl, lp, S)
                    if n_c > cand[0]:
                        cand = (n_c, e_c)
        if lib.is_valid(cand[0], cand[1], d, 3):
            if best is None or cand[0] > best[0]:
                best = cand
    return best


# ----------------------------------------------------------------------------
# Grow-and-anneal search for diameter 3: add one vertex per side, then
# anneal with degree-preserving edge switches and edge additions.
# ----------------------------------------------------------------------------

def _bad(n, adj):
    """Number of unordered pairs at distance > 3."""
    B = [1 << v for v in range(n)]
    for _ in range(3):
        nb = []
        for v in range(n):
            x = B[v]
            for u in adj[v]:
                x |= B[u]
            nb.append(x)
        B = nb
    return sum(n - b.bit_count() for b in B) // 2


def _colors(n, adj):
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        st = [s]
        while st:
            u = st.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    st.append(v)
    return color


def _extend_pair(n, adj, color, d, rng):
    """Copy the graph and add one vertex on each side, rewiring full neighbours to make room."""
    adj2 = [set(s) for s in adj] + [set(), set()]
    color2 = list(color) + [0, 1]
    for v in (n, n + 1):
        c = color2[v]
        others = [u for u in range(n) if color2[u] == 1 - c]
        rng.shuffle(others)
        others.sort(key=lambda u: len(adj2[u]))
        for u in others[:d]:
            if len(adj2[u]) >= d:
                w = rng.choice(list(adj2[u]))
                adj2[u].discard(w)
                adj2[w].discard(u)
            adj2[v].add(u)
            adj2[u].add(v)
    L = [v for v in range(n + 2) if color2[v] == 0 and len(adj2[v]) < d]
    R = [v for v in range(n + 2) if color2[v] == 1 and len(adj2[v]) < d]
    pairs = [(a, b) for a in L for b in R if b not in adj2[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj2[a]) < d and len(adj2[b]) < d and b not in adj2[a]:
            adj2[a].add(b)
            adj2[b].add(a)
    return n + 2, adj2, color2


def _anneal(n, adj, color, d, deadline, rng, iters):
    """Anneal the bipartite graph toward diameter 3. Returns True on success (adj mutated in place)."""
    left = [v for v in range(n) if color[v] == 0]
    right = [v for v in range(n) if color[v] == 1]
    cur = _bad(n, adj)
    T = 1.5
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        T = max(0.15, T * 0.998)
        if rng.random() < 0.4:
            l = rng.choice(left)
            r = rng.choice(right)
            if len(adj[l]) >= d or len(adj[r]) >= d or r in adj[l]:
                continue
            adj[l].add(r)
            adj[r].add(l)
            c2 = _bad(n, adj)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c2
            else:
                adj[l].discard(r)
                adj[r].discard(l)
        else:
            l1 = rng.choice(left)
            if not adj[l1]:
                continue
            r1 = rng.choice(list(adj[l1]))
            l2 = rng.choice(left)
            if l2 == l1 or not adj[l2]:
                continue
            r2 = rng.choice(list(adj[l2]))
            if r2 in adj[l1] or r1 in adj[l2]:
                continue
            adj[l1].discard(r1); adj[r1].discard(l1)
            adj[l2].discard(r2); adj[r2].discard(l2)
            adj[l1].add(r2); adj[r2].add(l1)
            adj[l2].add(r1); adj[r1].add(l2)
            c2 = _bad(n, adj)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c2
            else:
                adj[l1].discard(r2); adj[r2].discard(l1)
                adj[l2].discard(r1); adj[r1].discard(l2)
                adj[l1].add(r1); adj[r1].add(l1)
                adj[l2].add(r2); adj[r2].add(l2)
    return cur == 0


def _grow(n0, E0, d, D, deadline, rng):
    """Repeatedly add a vertex pair and anneal; keep the largest valid graph found."""
    adj = [set() for _ in range(n0)]
    for u, v in E0:
        adj[u].add(v)
        adj[v].add(u)
    color = _colors(n0, adj)
    best = (n0, list(E0))
    cn, cadj, ccol = n0, adj, color
    while time.monotonic() < deadline:
        n2, a2, c2 = _extend_pair(cn, cadj, ccol, d, rng)
        if _anneal(n2, a2, c2, d, deadline, rng, 1500):
            edges = [(u, v) for u in range(n2) for v in a2[u] if u < v]
            if lib.is_valid(n2, edges, d, D):
                best = (n2, edges)
                cn, cadj, ccol = n2, a2, c2
    return best


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    if D >= 3:
        try:
            base = _pg_arc_best(d)
        except Exception:
            base = None
        if base is not None and lib.is_valid(base[0], base[1], d, D):
            if base[0] > best[0]:
                best = base
            if D == 3:
                try:
                    res = _grow(base[0], base[1], d, D, deadline, rng)
                    if res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
                        best = res
                except Exception:
                    pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
