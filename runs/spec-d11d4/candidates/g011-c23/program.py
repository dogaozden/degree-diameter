import itertools
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bases (unchanged from the parent).
# ----------------------------------------------------------------------------

def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq(q):
    """Point-line incidence graph of the symplectic generalized quadrangle W(q)."""
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
# Twin blow-up (unchanged from the parent).
# ----------------------------------------------------------------------------

def _independent_set(N, nb, rng, nprng, deadline):
    """Iterated local search for a large set of vertices with no conflicting pair."""
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
        cnt[nbn[v]] += 1
        inS[v] = True
        S.append(v)

    def remove(u):
        nonlocal conf
        conf -= int(cnt[u])
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
    if n0 <= 60:
        deadline = min(deadline, time.monotonic() + 2.0)
    S = _independent_set(n0, nb, rng, nprng, deadline)
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------
# NEW ROUTE: monotone vertex extension by set cover.
#
# Adding a vertex never lengthens an existing shortest path, so an extended
# graph stays diameter-<=D as long as each new vertex w reaches every vertex
# within distance D. For w attached to a set N of vertices on the opposite side,
# that holds iff the radius-(D-1) balls of the members of N cover all vertices.
# So each new vertex is a set-cover problem over spare-degree vertices.
# Several randomized greedy trials are run and the largest result is kept.
# ----------------------------------------------------------------------------

def _balls(n, adj, R):
    """Per vertex, a bitmask of the vertices within distance R (R >= 0)."""
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


def _two_color(n, adj):
    """Proper 2-colouring of adj, or None if the graph is not bipartite."""
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
    return color


def _extend_once(n0, adj0, color0, d, R, rng, deadline):
    """One randomized greedy run: add vertices while some set cover of spare-degree neighbours exists."""
    n = n0
    adj = [list(a) for a in adj0]
    color = list(color0)
    while time.monotonic() < deadline:
        reach = _balls(n, adj, R)
        full = (1 << n) - 1
        placed = False
        sides = [0, 1]
        rng.shuffle(sides)
        for c in sides:
            cands = [x for x in range(n) if color[x] == c and len(adj[x]) < d]
            if not cands:
                continue
            uncovered = full
            chosen = []
            used = set()
            while uncovered and len(chosen) < d:
                rng.shuffle(cands)
                best = -1
                bestg = 0
                for x in cands:
                    if x in used:
                        continue
                    g = (reach[x] & uncovered).bit_count()
                    if g > bestg:
                        bestg = g
                        best = x
                if best < 0:
                    break
                used.add(best)
                chosen.append(best)
                uncovered &= ~reach[best]
            if uncovered == 0 and chosen:
                w = n
                adj.append(list(chosen))
                color.append(1 - c)
                for x in chosen:
                    adj[x].append(w)
                n += 1
                placed = True
                break
        if not placed:
            break
    return n, adj


def _extend(n0, edges0, d, D, deadline, rng):
    """Randomized extension trials on a base graph; returns the best (n, edges) or None."""
    adj0 = [[] for _ in range(n0)]
    for u, v in edges0:
        adj0[u].append(v)
        adj0[v].append(u)
    color0 = _two_color(n0, adj0)
    if color0 is None:
        return None
    best_adj = None
    best_n = n0
    trials = 0
    while time.monotonic() < deadline and trials < 60:
        trials += 1
        n, adj = _extend_once(n0, adj0, color0, d, D - 1, rng, deadline)
        if n > best_n:
            best_n = n
            best_adj = adj
    if best_adj is None:
        return None
    edges = [(u, v) for u in range(best_n) for v in best_adj[u] if u < v]
    return best_n, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget_end = start + max(1.0, min(0.8 * time_limit, time_limit - 8.0))
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

    # Blow-up route, using half of the budget.
    blow_deadline = start + 0.5 * (budget_end - start)
    q = d - 2
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < blow_deadline - 2.0:
        n0, e0 = 0, []
        if D >= 4:
            n0, e0 = _gq(q)
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
        if n0 > 0:
            consider(n0, e0)
            try:
                res = _blowup(n0, e0, d, blow_deadline, rng, nprng)
                if res is not None:
                    consider(res[0], res[1])
            except Exception:
                pass

    # Extension route: grow the current best graph by set-cover vertex additions.
    try:
        ext = _extend(best[0], best[1], d, D, budget_end, rng)
        if ext is not None:
            consider(ext[0], ext[1])
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
