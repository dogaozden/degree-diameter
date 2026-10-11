import random
import time

import lib


# ----------------------------------------------------------------------------
# Generic graph utilities.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
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
    return color


def _ball_masks(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


# ----------------------------------------------------------------------------
# Base family: projective plane PG(2, q) with spare degree s = d - q - 1.
#
# Helper "two-sided load arcs" (new): choose a point set S and a line set T
# independently. Each new A-vertex (one per point of S) is a twin-like vertex
# joined to the q+1 lines through its point; each new B-vertex (one per line
# of T) is joined to the q+1 points on its line. Loads on original lines come
# only from S and loads on original points come only from T, each capped at s.
# Diameter stays 3 for ANY S and T, because every new vertex reaches every
# old vertex within 3 steps through a line/point pencil argument.
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, pl, lp, index, pts) for PG(2, q); pl[P] = lines through P, lp[L] = points on L."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, pl, lp, index, pts


def _max_load(X, inc, m):
    """Largest number of elements of X hitting a single target, where inc[x] lists targets of x."""
    cnt = [0] * m
    for x in X:
        for t in inc[x]:
            cnt[t] += 1
    return max(cnt, default=0)


def _greedy_load(m, s, inc, rng, trials, deadline):
    """Randomized greedy set X with every target loaded by at most s elements; keeps the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        X = []
        for x in order:
            if all(load[t] < s for t in inc[x]):
                X.append(x)
                for t in inc[x]:
                    load[t] += 1
        if len(X) > len(best):
            best = X
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q): an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph_st(m, edges, S, T, pl, lp):
    """PG incidence plus one A-vertex per point of S and one B-vertex per line of T."""
    k, l = len(S), len(T)
    n = 2 * m + k + l
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in pl[P]:
            E.append((x, m + L))
    for t, j in enumerate(T):
        y = 2 * m + k + t
        for Q in lp[j]:
            E.append((Q, y))
    return n, E


def _families(d, rng, deadline):
    """Candidate graphs: the PG base and two-sided arc extensions, for each usable prime power q."""
    out = []
    qs = [q for q in range(min(d - 1, 23), 1, -1) if lib.is_prime_power(q)]
    for q in qs:
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, pl, lp, index, pts = _pg_data(q)
        out.append((2 * m, list(edges)))
        if s < 1:
            continue
        Sopts = [X for X in [_greedy_load(m, s, pl, rng, 12, deadline)] if X]
        Topts = [X for X in [_greedy_load(m, s, lp, rng, 12, deadline)] if X]
        if s >= 2:
            C = _conic_set(q, index, lib.GF(q))
            if _max_load(C, pl, m) <= s:
                Sopts.append(C)
            if _max_load(C, lp, m) <= s:
                Topts.append(C)
        made = 0
        for S in Sopts:
            for T in Topts:
                if made >= 6:
                    break
                out.append(_arc_graph_st(m, edges, S, T, pl, lp))
                made += 1
    return out


# ----------------------------------------------------------------------------
# New helper: spare-degree cover extension.
#
# A new vertex v of colour 1-c joined to a set N of colour-c vertices (each
# with spare degree) is within distance D of every old vertex iff the radius
# (D-1) balls of N cover the whole graph. This is an exact check, and it never
# shortens or breaks existing distances, so validity is preserved.
# The cover is found by randomized swap local search with a fixed size,
# rather than plain greedy, so it can escape the overlapping choices greedy makes.
# ----------------------------------------------------------------------------

def _find_cover(cands, ball, full, k, rng, iters):
    """Find a set of at most k candidates whose balls cover `full`, or None."""
    if not cands:
        return None
    k = min(k, len(cands))
    sel = rng.sample(cands, k)

    def score(X):
        mask = 0
        for x in X:
            mask |= ball[x]
        return (full & ~mask).bit_count()

    cur = score(sel)
    for _ in range(iters):
        if cur == 0:
            return sel
        i = rng.randrange(k)
        x = cands[rng.randrange(len(cands))]
        if x in sel:
            continue
        trial = sel[:]
        trial[i] = x
        sc = score(trial)
        if sc <= cur or rng.random() < 0.03:
            sel, cur = trial, sc
    return sel if cur == 0 else None


def _cover_grow(n, edges, d, D, deadline, rng, attempts=60, iters=1000):
    """Repeatedly add a vertex whose neighbourhood covers the graph within radius D-1."""
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _ball_masks(n, adj, D - 1)
        full = (1 << n) - 1
        placed = False
        colours = [0, 1]
        rng.shuffle(colours)
        for c in colours:
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            for _ in range(attempts):
                if time.monotonic() >= deadline:
                    break
                sel = _find_cover(cands, ball, full, d, rng, iters)
                if sel is not None:
                    v = n
                    n += 1
                    color.append(1 - c)
                    adj.append([])
                    deg.append(0)
                    for s in sel:
                        edges.append((s, v))
                        adj[s].append(v)
                        adj[v].append(s)
                        deg[s] += 1
                        deg[v] += 1
                    placed = True
                    break
            if placed:
                break
        if not placed:
            break
    return n, edges


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, bipartite with diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    # D >= 3: projective-plane families, then cover-growth within time slices.
    graphs = _families(d, rng, start + 0.25 * time_limit)
    graphs.sort(key=lambda g: -g[0])
    graphs = graphs[:16]
    for idx, (n, e) in enumerate(graphs):
        consider(n, e)
        now = time.monotonic()
        if now >= deadline:
            break
        share = (deadline - now) / (len(graphs) - idx)
        gn, ge = _cover_grow(n, e, d, D, now + share, rng)
        consider(gn, ge)

    return best
