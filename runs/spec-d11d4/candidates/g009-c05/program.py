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
    return P + len(lines), edges, P


# ----------------------------------------------------------------------------
# Twin blow-up with a distance-2-free vertex set.
#
# If every vertex of a base graph G has degree d-1, replace some vertices v by
# two copies (v, v') that share the same neighbourhood. Each copy of u then has
# degree sum_{v in N(u)} m_v with m_v in {1, 2}; since |N(u)| = d-1 the degree
# stays <= d iff u has at most one neighbour in S = {v : m_v = 2}. So S must
# have no two vertices at distance 2. Blow-ups keep bipartiteness and diameter.
#
# Distance-2 conflicts only join vertices of the same side, so the conflict
# graph splits into a point part and a line part. Their independent sets can be
# chosen independently and unioned, so we search each side separately.
# ----------------------------------------------------------------------------

def _independent_set(N, nb, allowed, rng, nprng, deadline):
    """(1,2)-swap local search with perturbation for a large conflict-free set.

    Invariant: the chosen set S is always independent in the conflict graph nb.
    A (1,2)-swap removes x from S and inserts two non-adjacent vertices whose
    only conflict inside S is x. When no swap helps, a random vertex is forced
    in (evicting its conflicts) and the set is refilled greedily.
    """
    nbs = [set(x) for x in nb]
    ok = [bool(x) for x in allowed]
    cnt = [0] * N              # number of chosen conflict-neighbours
    inS = [False] * N
    tabu = [0] * N
    S = set()

    def add(v):
        inS[v] = True
        S.add(v)
        for u in nb[v]:
            cnt[u] += 1

    def remove(v):
        inS[v] = False
        S.discard(v)
        for u in nb[v]:
            cnt[u] -= 1

    def fill():
        free = [v for v in range(N) if ok[v] and not inS[v] and cnt[v] == 0]
        rng.shuffle(free)
        for v in free:
            if not inS[v] and cnt[v] == 0:
                add(v)

    best = []
    it = 0
    fill()
    while True:
        it += 1
        if (it & 15) == 0 and time.monotonic() >= deadline:
            break

        # Look for an improving (1,2)-swap.
        improved = False
        xs = list(S)
        rng.shuffle(xs)
        for x in xs:
            L = [v for v in nb[x] if ok[v] and not inS[v] and cnt[v] == 1]
            if len(L) < 2:
                continue
            pair = None
            for i in range(len(L)):
                a = L[i]
                na = nbs[a]
                for j in range(i + 1, len(L)):
                    if L[j] not in na:
                        pair = (a, L[j])
                        break
                if pair is not None:
                    break
            if pair is not None:
                remove(x)
                add(pair[0])
                add(pair[1])
                fill()
                improved = True
                break
        if improved:
            if len(S) > len(best):
                best = list(S)
            continue

        # Local optimum: record it, then perturb by forcing a random vertex in.
        if len(S) > len(best):
            best = list(S)
        v = -1
        for _ in range(64):
            w = rng.randrange(N)
            if ok[w] and not inS[w] and tabu[w] <= it:
                v = w
                break
        if v < 0:
            cands = [w for w in range(N) if ok[w] and not inS[w] and tabu[w] <= it]
            if not cands:
                break
            v = rng.choice(cands)
        for u in nb[v]:
            if inS[u]:
                remove(u)
                tabu[u] = it + 3 + rng.randrange(7)
        add(v)
        fill()

    if len(S) > len(best):
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
    """Twin blow-up of a base graph of degree d-1.

    Vertices 0..split-1 form one side and split..n0-1 the other; conflicts only
    occur within a side, so each side is searched separately with half of the
    remaining time each.
    """
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
    deadline = start + max(0.5, 0.85 * time_limit - 2.0)
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
            res = _blowup(n0, e0, d, split, deadline, rng, nprng)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
