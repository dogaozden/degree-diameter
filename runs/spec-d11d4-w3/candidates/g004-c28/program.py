import itertools
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bases.
# ----------------------------------------------------------------------------

def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq(q):
    """Point-line incidence graph of the symplectic generalized quadrangle W(q).

    Points are 0..P-1, lines are P..P+L-1. Every point lies on q+1 lines, every
    line has q+1 points, and the incidence graph has diameter 4.
    """
    F = lib.GF(q)
    A = F.add_table.tolist()
    M = F.mul_table.tolist()
    NEG = [F.neg(a) for a in range(q)]
    INV = [0] + [F.inv(a) for a in range(1, q)]
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    P = len(pts)
    index = {v: i for i, v in enumerate(pts)}

    def norm(v):
        c = next(x for x in v if x)
        ic = INV[c]
        return tuple(M[ic][x] for x in v)

    covered = [bytearray(P) for _ in range(P)]
    lines = []
    for i in range(P):
        x = pts[i]
        ci = covered[i]
        for j in range(i + 1, P):
            if ci[j]:
                continue
            y = pts[j]
            # Symplectic form x0*y1 - x1*y0 + x2*y3 - x3*y2.
            t = A[M[x[0]][y[1]]][NEG[M[x[1]][y[0]]]]
            s = A[M[x[2]][y[3]]][NEG[M[x[3]][y[2]]]]
            if A[t][s] != 0:
                continue
            L = set()
            for a in range(q):
                ax = [M[a][x[k]] for k in range(4)]
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(A[ax[k]][M[b][y[k]]] for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                cp = covered[p]
                for r in L:
                    cp[r] = 1
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return P + len(lines), edges


# ----------------------------------------------------------------------------
# Twin blow-up (from the parent): a base graph of degree d-1 whose vertices in
# a distance-2-free set S are doubled. Conflicts stay inside colour classes, so
# the two sides are solved independently with a local-search independent set.
# ----------------------------------------------------------------------------

def _independent_set(N, nb, rng, nprng, deadline):
    """Iterated local search for a large set of vertices with no conflicting pair."""
    if N == 0:
        return []
    nbn = [np.asarray(x, dtype=np.int64) for x in nb]
    cnt = np.zeros(N, dtype=np.int64)
    inS = np.zeros(N, dtype=bool)
    tabu = np.zeros(N, dtype=np.int64)
    S = []
    conf = 0
    best = []
    best_size = 0
    it = 0
    last_best_it = 0

    def add(v):
        nonlocal conf
        conf += int(cnt[v])
        if len(nbn[v]):
            cnt[nbn[v]] += 1
        inS[v] = True
        S.append(v)

    def remove(u):
        nonlocal conf
        conf -= int(cnt[u])
        if len(nbn[u]):
            cnt[nbn[u]] -= 1
        inS[u] = False
        S.remove(u)

    def pick():
        score = cnt + nprng.random(N)
        score[inS] = np.inf
        score[tabu > it] = np.inf
        return int(np.argmin(score))

    while True:
        it += 1
        if (it & 63) == 0 and time.monotonic() >= deadline:
            break
        if conf == 0:
            if len(S) > best_size:
                best = list(S)
                best_size = len(S)
                last_best_it = it
            add(pick())
        else:
            conflicting = [u for u in S if cnt[u] > 0]
            u = conflicting[rng.randrange(len(conflicting))]
            remove(u)
            tabu[u] = it + 5 + rng.randrange(8)
            add(pick())
        if S and it - last_best_it > 15000:
            u = S[rng.randrange(len(S))]
            remove(u)
            tabu[u] = it + 5
            last_best_it = it
    if conf == 0 and len(S) > best_size:
        best = list(S)
    return best


def _sides(n0, adj):
    """Two-colour the base graph (it is bipartite); return the two colour classes."""
    color = [-1] * n0
    for s in range(n0):
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
    classes = [[], []]
    for v in range(n0):
        classes[max(color[v], 0)].append(v)
    return classes


def _solve_side(side, nb, rng, nprng, deadline):
    loc = {v: i for i, v in enumerate(side)}
    lnb = [[loc[w] for w in nb[v] if w in loc] for v in side]
    sol = _independent_set(len(side), lnb, rng, nprng, deadline)
    return [side[i] for i in sol]


def _blow(n0, edges0, S):
    """Blow up each vertex of S into two twin copies (same neighbourhood)."""
    extra = {}
    for v in S:
        extra[v] = n0 + len(extra)
    copies = [[v] + ([extra[v]] if v in extra else []) for v in range(n0)]
    edges = []
    for u, v in edges0:
        for a in copies[u]:
            for b in copies[v]:
                edges.append((a, b))
    return n0 + len(extra), edges


def _blowup(n0, edges0, d, deadline, rng, nprng):
    """Twin blow-up of a base graph of degree d-1 by a large distance-2-free set."""
    adj = [[] for _ in range(n0)]
    for u, v in edges0:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != d - 1 for a in adj):
        return None
    cs = [set() for _ in range(n0)]
    for w in range(n0):
        a = adj[w]
        for i in range(len(a)):
            for j in range(i + 1, len(a)):
                x, y = a[i], a[j]
                cs[x].add(y)
                cs[y].add(x)
    nb = [sorted(s) for s in cs]
    sides = _sides(n0, adj)
    S = []
    now = time.monotonic()
    span = max(0.0, deadline - now)
    k = len(sides)
    for idx, side in enumerate(sides):
        if not side:
            continue
        sub_deadline = now + span * (idx + 1) / k
        S.extend(_solve_side(side, nb, rng, nprng, sub_deadline))
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------
# NEW construction: diameter-preserving greedy vertex augmentation.
#
# Adding a vertex w of colour c joined to a set N of opposite-colour vertices
# with spare degree keeps the graph bipartite, keeps every old distance (adding
# vertices only shortens paths), and gives w eccentricity <= D exactly when the
# radius-(D-1) balls of N cover all old vertices (dist(w,x) = 1 + dist(y,x)).
# So we repeatedly add vertices by greedy max-coverage over spare vertices,
# which uses up spare degree on the base graph and grows the order.
# Every step is exact, so the result stays valid; lib.is_valid checks at the end.
# ----------------------------------------------------------------------------

def _colour(n, adj):
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
                elif col[v] == col[u]:
                    return None
    return col


def _balls(n, adj, R):
    """Bitmask of all vertices within distance R, per vertex."""
    reach = [1 << v for v in range(n)]
    for _ in range(R):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _augment(n0, edges0, d, D, deadline, rng):
    """Greedily add vertices while diameter and degree stay valid. Returns (n, edges)."""
    if D < 2 or n0 < 1:
        return n0, edges0
    n = n0
    adj = [[] for _ in range(n)]
    for u, v in edges0:
        adj[u].append(v)
        adj[v].append(u)
    colour = _colour(n, adj)
    if colour is None:
        return n0, edges0
    R = D - 1
    while time.monotonic() < deadline:
        balls = _balls(n, adj, R)
        target = (1 << n) - 1
        placed = False
        sides = [0, 1]
        rng.shuffle(sides)
        for c in sides:
            cands = [y for y in range(n) if colour[y] != c and len(adj[y]) < d]
            if not cands:
                continue
            rng.shuffle(cands)
            cov = 0
            chosen = []
            while cov != target and len(chosen) < d:
                best_y = -1
                best_g = 0
                for y in cands:
                    g = (balls[y] & ~cov).bit_count()
                    if g > best_g:
                        best_g = g
                        best_y = y
                if best_y < 0:
                    break
                chosen.append(best_y)
                cov |= balls[best_y]
            if cov == target and chosen:
                w = n
                adj.append(list(chosen))
                for y in chosen:
                    adj[y].append(w)
                colour.append(c)
                n += 1
                placed = True
                break
        if not placed:
            break
    edges = [(u, v) for u in range(n) for v in adj[u] if u < v]
    return n, edges


def _augment_restarts(base, d, D, until, rng, consider):
    """Repeat randomized augmentation from a base graph until the deadline."""
    n0, e0 = base
    zero_runs = 0
    while time.monotonic() < until:
        n, e = _augment(n0, e0, d, D, until, rng)
        if n == n0:
            zero_runs += 1
            if zero_runs >= 3:
                break
        else:
            zero_runs = 0
            consider(n, e)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(0.5, 0.8 * time_limit - 2.0)
    deadline = start + total
    rng = random.Random(seed)
    nprng = np.random.default_rng(abs(int(seed)) % (2 ** 32))

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

    if D == 2:
        return best

    pg = _pg(d)
    if pg is not None:
        consider(pg[0], pg[1])

    # Base of degree exactly d-1 with q = d-2 a prime power.
    q = d - 2
    raw = None
    if 2 <= q <= 11 and lib.is_prime_power(q):
        if D >= 4:
            raw = _gq(q)
        elif D == 3:
            raw = lib.projective_plane_incidence(q)
    if raw is not None:
        consider(raw[0], raw[1])

    # Phase A: twin blow-up of the base (the parent's route).
    blow = None
    if raw is not None and time.monotonic() < start + 0.3 * total:
        blow = _blowup(raw[0], raw[1], d, start + 0.3 * total, rng, nprng)
        if blow is not None:
            consider(blow[0], blow[1])

    # Phase B: greedy augmentation of the blow-up result.
    if blow is not None:
        _augment_restarts(blow, d, D, start + 0.55 * total, rng, consider)

    # Phase C: greedy augmentation of the raw base (every vertex starts with spare degree).
    if raw is not None:
        _augment_restarts(raw, d, D, start + 0.85 * total, rng, consider)

    # Phase D: greedy augmentation of the projective-plane base, if any.
    if pg is not None:
        _augment_restarts(pg, d, D, start + 0.95 * total, rng, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
