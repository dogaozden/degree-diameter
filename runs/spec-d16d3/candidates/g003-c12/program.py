import random
import time

import lib


def _adjacency(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _colors(n, adj):
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


def _balls(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return ball


def _bits(x):
    out = []
    while x:
        low = x & -x
        out.append(low.bit_length() - 1)
        x ^= low
    return out


def _union(chosen, ball):
    u = 0
    for s in chosen:
        u |= ball[s]
    return u


def _cover_attempt(elig, ball, full, d, rng, iters):
    """Find <= d eligible vertices whose radius-(D-1) balls cover all vertices.

    Randomized greedy start, then a min-conflicts local search that targets
    a random uncovered vertex. Returns the chosen list or None.
    """
    chosen = []
    cs = set()
    covered = 0
    while len(chosen) < d and covered != full:
        best_list, bg = [], 0
        for s in elig:
            if s in cs:
                continue
            g = (ball[s] & ~covered).bit_count()
            if g > bg:
                bg, best_list = g, [s]
            elif g == bg and g > 0:
                best_list.append(s)
        if bg == 0:
            break
        s = rng.choice(best_list)
        chosen.append(s)
        cs.add(s)
        covered |= ball[s]
    if covered == full:
        return chosen

    cov = _union(chosen, ball)
    unc = (full & ~cov).bit_count()
    for _ in range(iters):
        if unc == 0:
            return chosen
        x = rng.choice(_bits(full & ~cov))
        cands = [s for s in elig if s not in cs and (ball[s] >> x) & 1]
        if not cands:
            continue
        s = rng.choice(cands)
        if len(chosen) < d:
            new = chosen + [s]
        else:
            new = chosen[:]
            new[rng.randrange(len(new))] = s
        ncov = _union(new, ball)
        nunc = (full & ~ncov).bit_count()
        if nunc <= unc or rng.random() < 0.02:
            chosen, cs, cov, unc = new, set(new), ncov, nunc
    return chosen if unc == 0 else None


def _grow(n, edges, color, d, D, deadline, rng, iters):
    """Repeatedly add a vertex whose neighbourhood covers every vertex within D-1.

    A new vertex v of colour c joins vertices of colour 1-c. Distances between old
    vertices can only shrink, and v reaches x within D exactly when some neighbour t
    of v lies within D-1 of x. So a cover of all vertices by radius-(D-1) balls of
    eligible vertices keeps the graph valid by construction.
    """
    edges = list(edges)
    adj = _adjacency(n, edges)
    deg = [len(a) for a in adj]
    color = list(color)
    while time.monotonic() < deadline:
        ball = _balls(n, adj, D - 1)
        full = (1 << n) - 1
        sides = [0, 1]
        rng.shuffle(sides)
        added = False
        for c in sides:
            elig = [s for s in range(n) if color[s] == 1 - c and deg[s] < d]
            if not elig:
                continue
            chosen = None
            for _ in range(3):
                if time.monotonic() >= deadline:
                    break
                chosen = _cover_attempt(elig, ball, full, d, rng, iters)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                adj.append([])
                deg.append(0)
                color.append(c)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    n0, e0 = lib.haar_graph(d, range(d))
    best_n, best_e = n0, e0
    if not lib.is_valid(best_n, best_e, d, D):
        return 1, []

    # Bases: incidence graphs of projective planes with q + 1 <= d (largest few),
    # then K_{d,d}. Spare degree d - q - 1 is filled by cover-based growth.
    bases = []
    if D >= 3:
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
        for q in qs:
            n, e = lib.projective_plane_incidence(q)
            bases.append((n, e))
    bases.append((n0, e0))

    prepared = []
    for n, e in bases:
        col = _colors(n, _adjacency(n, e))
        prepared.append((n, e, col))

    rng = random.Random(seed * 7919 + 13 * d + D)
    attempt = 0
    while time.monotonic() < deadline:
        if attempt < len(prepared):
            idx = attempt
        else:
            idx = rng.randrange(max(1, len(prepared) - 1))
        n, e, col = prepared[idx]
        n2, e2 = _grow(n, e, col, d, D, deadline, rng, 400)
        if n2 > best_n and lib.is_valid(n2, e2, d, D):
            best_n, best_e = n2, e2
        attempt += 1

    return best_n, best_e
