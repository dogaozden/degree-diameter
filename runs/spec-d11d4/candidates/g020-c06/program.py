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
# Twin blow-up with a distance-2-free vertex set (inherited from the parent).
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
# NEW IDEA: slack-cover augmentation.
#
# After a construction, vertices of degree < d have spare degree. A new vertex x
# on one side, joined to a set T of at most d spare vertices on the other side,
# keeps the graph bipartite and degree-valid. Distances between old vertices do
# not grow. The new vertex is within distance D of everything iff every vertex v
# satisfies min_{t in T} dist(t, v) <= D-1. So for each vertex we store the
# bitmask of its radius-(D-1) ball, and we search for a set T whose balls
# jointly cover the whole vertex set. This is a bounded min-conflicts local
# search (swap one member of T for a candidate that covers more of what is
# still uncovered). Each success adds one vertex and we repeat on the new graph.
# ----------------------------------------------------------------------------

def _ball_masks(n, adj, R):
    """Bitmask per vertex of all vertices within distance R."""
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


def _two_colour(n, adj):
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
    return col


def _find_cover(masks, cands, k, full, rng, until):
    """Find T (|T| <= k, from cands) whose masks jointly cover full, or None by time `until`."""
    k = min(k, len(cands))
    if k <= 0:
        return None
    while True:
        if time.monotonic() >= until:
            return None
        # Greedy start with random tie-breaking.
        T = []
        U = 0
        pool = list(cands)
        for _ in range(k):
            bi = -1
            bg = -1.0
            for idx, c in enumerate(pool):
                g = (masks[c] & ~U).bit_count() + rng.random() * 0.5
                if g > bg:
                    bg = g
                    bi = idx
            c = pool.pop(bi)
            T.append(c)
            U |= masks[c]
        tabu = {}
        for step in range(3000):
            unc = full & ~U
            if not unc:
                return T
            if (step & 63) == 0 and time.monotonic() >= until:
                return None
            Tset = set(T)
            bc = -1
            bkey = -1.0
            for c in cands:
                if c in Tset or tabu.get(c, -1) > step:
                    continue
                g = (masks[c] & unc).bit_count() + rng.random() * 0.5
                if g > bkey:
                    bkey = g
                    bc = c
            if bc < 0:
                break
            # Choose which member of T to drop: the one leaving the fewest uncovered.
            bi = -1
            bres = None
            for i in range(len(T)):
                others = 0
                for j, s in enumerate(T):
                    if j != i:
                        others |= masks[s]
                left = (full & ~(others | masks[bc])).bit_count() + rng.random() * 0.5
                if bres is None or left < bres:
                    bres = left
                    bi = i
            if rng.random() < 0.05:
                bi = rng.randrange(len(T))
            tabu[T[bi]] = step + 5 + rng.randrange(6)
            T[bi] = bc
            U = 0
            for s in T:
                U |= masks[s]
        # Restart from a fresh greedy solution.


def _augment(n, edges, d, D, deadline, rng):
    """Greedily add vertices joined to spare-degree vertices while the diameter holds."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    chunk = 2.0
    while time.monotonic() < deadline:
        col = _two_colour(n, adj)
        masks = _ball_masks(n, adj, D - 1)
        full = (1 << n) - 1
        progress = False
        sides = [0, 1]
        rng.shuffle(sides)
        for s in sides:
            cands = [v for v in range(n) if col[v] == s and len(adj[v]) < d]
            if not cands:
                continue
            until = min(deadline, time.monotonic() + chunk)
            T = _find_cover(masks, cands, d, full, rng, until)
            if T is not None:
                x = n
                n += 1
                adj.append(list(T))
                for t in T:
                    adj[t].append(x)
                progress = True
                break
        if not progress and time.monotonic() >= deadline:
            break
    out = []
    for u in range(n):
        for v in adj[u]:
            if u < v:
                out.append((u, v))
    return n, out


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    hard_end = start + max(1.0, 0.85 * time_limit - 2.0)
    mis_end = start + max(0.5, 0.5 * time_limit)
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

    # Blow-up route: base of degree exactly d-1 with q = d-2 a prime power.
    q = d - 2
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < mis_end - 2.0:
        if D >= 4:
            n0, e0 = _gq(q)
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
        else:
            n0, e0 = 0, []
        if n0 > 0:
            consider(n0, e0)
            res = _blowup(n0, e0, d, mis_end, rng, nprng)
            if res is not None:
                consider(res[0], res[1])

    # Spend the remaining budget on slack-cover augmentation of the best graph.
    if D >= 3 and time.monotonic() < hard_end - 1.0:
        n2, e2 = _augment(best[0], list(best[1]), d, D, hard_end, rng)
        if n2 > best_n:
            consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
