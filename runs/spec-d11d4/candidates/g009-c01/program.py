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
    Returns (n, edges, P).
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
    return P + len(lines), edges, P


# ----------------------------------------------------------------------------
# Helpers: bipartition colouring and bitmask balls.
# ----------------------------------------------------------------------------

def _two_color(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for w in adj[u]:
                if col[w] == -1:
                    col[w] = 1 - col[u]
                    stack.append(w)
    return col


def _balls(n, adj, R):
    """Bitmask per vertex of all vertices within distance R."""
    cur = [1 << v for v in range(n)]
    for _ in range(R):
        nxt = [0] * n
        for v in range(n):
            x = cur[v]
            for u in adj[v]:
                x |= cur[u]
            nxt[v] = x
        cur = nxt
    return cur


# ----------------------------------------------------------------------------
# Greedy augmentation using spare degree.
#
# A new vertex x on side k joined to a set A (all on side 1-k, degree < d) keeps
# the diameter <= D iff every vertex lies within distance D-1 of some a in A.
# Such x never shortens or breaks existing distances, so the check is exact.
# Each step greedily set-covers with balls of radius D-1 and adds one vertex.
# ----------------------------------------------------------------------------

def _augment(n0, edges0, color0, d, D, deadline, rng):
    adj = [[] for _ in range(n0)]
    for u, v in edges0:
        adj[u].append(v)
        adj[v].append(u)
    n = n0
    color = list(color0)
    deg = [len(a) for a in adj]
    R = D - 1
    while time.monotonic() < deadline:
        B = _balls(n, adj, R)
        made = False
        sides = [0, 1]
        rng.shuffle(sides)
        for k in sides:
            cands = [a for a in range(n) if color[a] == 1 - k and deg[a] < d]
            if not cands:
                continue
            rng.shuffle(cands)
            uncovered = (1 << n) - 1
            chosen = []
            while uncovered and len(chosen) < d and cands:
                bi, bg = -1, 0
                for idx, a in enumerate(cands):
                    g = (B[a] & uncovered).bit_count()
                    if g > bg:
                        bg, bi = g, idx
                if bi < 0:
                    break
                a = cands.pop(bi)
                chosen.append(a)
                uncovered &= ~B[a]
            if uncovered == 0 and chosen:
                x = n
                n += 1
                color.append(k)
                adj.append(list(chosen))
                deg.append(len(chosen))
                for a in chosen:
                    adj[a].append(x)
                    deg[a] += 1
                made = True
                break
        if not made:
            break
    edges = [(u, v) for u in range(n) for v in adj[u] if u < v]
    return n, edges


# ----------------------------------------------------------------------------
# Twin blow-up with a distance-2-free vertex set.
#
# If every vertex of a base graph G has degree d-1, replace some vertices v by
# two copies sharing the same neighbourhood. Each copy of u then has degree
# sum_{v in N(u)} m_v, which stays <= d iff u has at most one neighbour in S.
# ----------------------------------------------------------------------------

def _independent_set(N, nb, allowed, rng, nprng, deadline):
    """Iterated local search for a large conflict-free set among `allowed` vertices."""
    nbn = [np.asarray(x, dtype=np.int64) for x in nb]
    cnt = np.zeros(N, dtype=np.int64)
    inS = np.zeros(N, dtype=bool)
    tabu = np.zeros(N, dtype=np.int64)
    blocked = ~allowed
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
        score[blocked] = np.inf
        score[tabu > it] = np.inf
        v = int(np.argmin(score))
        return v if np.isfinite(score[v]) else -1

    while True:
        it += 1
        if (it & 63) == 0 and time.monotonic() >= deadline:
            break
        if conf == 0:
            if len(S) > best_size:
                best = list(S)
                best_size = len(S)
                last_best_it = it
            v = pick()
            if v < 0:
                if (tabu > it).any():
                    tabu[:] = 0
                    continue
                break
            add(v)
        else:
            conflicting = [u for u in S if cnt[u] > 0]
            u = conflicting[rng.randrange(len(conflicting))]
            remove(u)
            tabu[u] = it + 5 + rng.randrange(8)
            v = pick()
            if v >= 0:
                add(v)
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


def _blowup(n0, edges0, d, split, deadline, rng, nprng):
    """Twin blow-up of a base graph of degree d-1 (vertices < split form one side)."""
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

    side_a = np.zeros(n0, dtype=bool)
    side_a[:split] = True
    side_b = ~side_a

    now = time.monotonic()
    mid = now + (deadline - now) / 2.0
    S_a = _independent_set(n0, nb, side_a, rng, nprng, mid)
    S_b = _independent_set(n0, nb, side_b, rng, nprng, deadline)
    return _blow(n0, edges0, S_a + S_b)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, 0.85 * time_limit - 2.0)
    deadline = start + budget
    rng = random.Random(seed)
    nprng = np.random.default_rng(abs(int(seed)) % (2 ** 32))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    pg = _pg(d)
    if pg is not None:
        consider(pg[0], pg[1])

    # Base of degree d-1 with q = d-2 a prime power: W(q) for D >= 4, PG(2,q) for D = 3.
    q = d - 2
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < deadline - 2.0:
        if D >= 4:
            n0, e0, split = _gq(q)
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
            split = n0 // 2
        else:
            n0, e0, split = 0, [], 0
        if n0 > 0:
            consider(n0, e0)

            # Route A: greedy augmentation directly on the base graph.
            col0 = [0 if v < split else 1 for v in range(n0)]
            dl_a = start + 0.2 * budget
            n1, e1 = _augment(n0, e0, col0, d, D, dl_a, rng)
            consider(n1, e1)

            # Route B: twin blow-up, then greedy augmentation on the spare slots.
            mid = start + 0.5 * budget
            res = _blowup(n0, e0, d, split, mid, rng, nprng)
            if res is not None:
                nb_, eb_ = res
                consider(nb_, eb_)
                colb = _two_color(nb_, eb_)
                n2, e2 = _augment(nb_, eb_, colb, d, D, deadline, rng)
                consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
