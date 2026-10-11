import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q): incidence graph, diameter 4, degree q+1.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of W(q). Points are 0..P-1, lines P..2P-1."""
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


# ----------------------------------------------------------------------------
# Bipartite graph as two lists of neighbour sets: nbrA[a] subset of B-indices,
# nbrB[b] subset of A-indices. Both sides have h vertices.
# Output vertex ids: A index a -> a, B index b -> h + b.
# ----------------------------------------------------------------------------

def _to_edges(h, nbrA):
    return 2 * h, [(a, h + b) for a in range(h) for b in nbrA[a]]


def _adj(h, nbrA, nbrB):
    adj = [None] * (2 * h)
    for a in range(h):
        adj[a] = [h + b for b in nbrA[a]]
    for b in range(h):
        adj[h + b] = list(nbrB[b])
    return adj


def _bad(adj, n, D):
    """Number of unordered vertex pairs at distance more than D (bitmask BFS)."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return sum(n - b.bit_count() for b in ball) // 2


def _swap(nbrA, nbrB, a1, b1, a2, b2):
    """Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1). Degrees are preserved."""
    nbrA[a1].discard(b1)
    nbrA[a1].add(b2)
    nbrA[a2].discard(b2)
    nbrA[a2].add(b1)
    nbrB[b1].discard(a1)
    nbrB[b1].add(a2)
    nbrB[b2].discard(a2)
    nbrB[b2].add(a1)


def _perfect_matching_avoid(h, nbrA, rng):
    """Perfect matching between A and B avoiding existing edges (Kuhn augmenting paths)."""
    cand = []
    for a in range(h):
        c = [b for b in range(h) if b not in nbrA[a]]
        rng.shuffle(c)
        cand.append(c)
    match_b = [-1] * h

    def aug(a, seen):
        for b in cand[a]:
            if not seen[b]:
                seen[b] = True
                if match_b[b] == -1 or aug(match_b[b], seen):
                    match_b[b] = a
                    return True
        return False

    for a in range(h):
        if not aug(a, [False] * h):
            return None
    return [(match_b[b], b) for b in range(h)]


def _insert(h, nbrA, nbrB, d, rng):
    """Add one A-vertex and one B-vertex, each of degree d, by removing d edges and reconnecting.

    Existing degrees are unchanged. Returns copied structures (h+1, nA, nB) or None.
    """
    if d > h:
        return None
    nA = [set(s) for s in nbrA] + [set()]
    nB = [set(s) for s in nbrB] + [set()]
    new = h
    As = rng.sample(range(h), d)
    used_b = set()
    pairs = []
    for a in As:
        cands = [b for b in nA[a] if b not in used_b]
        if not cands:
            return None
        b = rng.choice(cands)
        used_b.add(b)
        pairs.append((a, b))
    for a, b in pairs:
        nA[a].discard(b)
        nB[b].discard(a)
        nA[a].add(new)      # a -- new B vertex
        nB[new].add(a)
        nA[new].add(b)      # new A vertex -- b
        nB[b].add(new)
    return h + 1, nA, nB


def _anneal(h, nbrA, nbrB, D, rng, deadline, iters, T0):
    """Simulated annealing over 2-switches, cost = bad pairs. Returns True if cost reached 0."""
    n = 2 * h
    cost = _bad(_adj(h, nbrA, nbrB), n, D)
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        a1 = rng.randrange(h)
        a2 = rng.randrange(h)
        if a1 == a2:
            continue
        b1 = rng.choice(list(nbrA[a1]))
        b2 = rng.choice(list(nbrA[a2]))
        if b1 == b2 or b2 in nbrA[a1] or b1 in nbrA[a2]:
            continue
        _swap(nbrA, nbrB, a1, b1, a2, b2)
        c2 = _bad(_adj(h, nbrA, nbrB), n, D)
        T = T0 * (1.0 - it / iters) + 0.02
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            _swap(nbrA, nbrB, a1, b2, a2, b1)  # undo
    return cost == 0


def _grow(h, nbrA, nbrB, d, D, rng, deadline, consider, iters=400):
    """Repeatedly insert two vertices and repair the diameter by annealing; keep successes."""
    while time.monotonic() < deadline:
        ins = _insert(h, nbrA, nbrB, d, rng)
        if ins is None:
            break
        nh, nA, nB = ins
        if _anneal(nh, nA, nB, D, rng, deadline, iters, 1.0):
            h, nbrA, nbrB = nh, nA, nB
            consider(*_to_edges(h, nbrA))


# ----------------------------------------------------------------------------
# Driver.
# D = 3: projective plane incidence (calibration, optimal when d-1 is a prime power).
# D >= 4: W(q) base with extra perfect matchings up to degree d, then
#         insertion-and-anneal growth. Every accepted graph is verified.
# Fallback: K_{d,d}.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.85 * time_limit - 1.0)
    deadline = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if best[0] >= lib._moore_bound(d, D):
        return best

    try:
        if D == 3:
            for q in range(d - 1, 1, -1):
                if lib.is_prime_power(q):
                    n0, e0 = lib.projective_plane_incidence(q)
                    consider(n0, e0)
                    break
        elif D >= 4:
            q = next((x for x in range(d - 1, 1, -1) if lib.is_prime_power(x)), None)
            if q is not None:
                n0, e0 = _gq_w(q)
                consider(n0, e0)
                P = n0 // 2
                nbrA = [set() for _ in range(P)]
                nbrB = [set() for _ in range(P)]
                for u, v in e0:
                    nbrA[u].add(v - P)
                    nbrB[v - P].add(u)
                # Adding edges across the bipartition never increases distances.
                for _ in range(d - (q + 1)):
                    if time.monotonic() > start + 0.2 * total:
                        break
                    M = _perfect_matching_avoid(P, nbrA, rng)
                    if M is None:
                        break
                    for a, b in M:
                        nbrA[a].add(b)
                        nbrB[b].add(a)
                consider(*_to_edges(P, nbrA))
                _grow(P, nbrA, nbrB, d, D, rng, deadline, consider)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
