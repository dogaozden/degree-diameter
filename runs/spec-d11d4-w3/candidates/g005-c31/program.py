import itertools
import math
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
# Twin blow-up with a distance-2-free vertex set.
#
# If every vertex of a base graph G has degree d-1, replace some vertices v by
# two copies (v, v') that share the same neighbourhood. Each copy of u then has
# degree sum_{v in N(u)} m_v = (d-1) + |N(u) ∩ S| where S = {v : m_v = 2}. So S
# must have no two vertices with a common neighbour. The two colour classes of a
# bipartite base are independent subproblems, solved separately.
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
    """Maximum-ish conflict-free subset of one colour class (conflicts stay inside the class)."""
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
    if n0 <= 60:
        deadline = min(deadline, time.monotonic() + 2.0)

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
# NEW: cyclic Haar graph search for diameter 4.
#
# Haar graph H(Z_m, S): a_i ~ b_{i+s} for s in S, |S| = d, so it is d-regular
# and bipartite with 2m vertices. For diameter 4 it suffices that
#   (odd)  S - S + S covers Z_m  (every a-b pair within distance 3), and
#   (even) (S - S) + (S - S) covers Z_m  (every a-a pair within distance 4).
# We search S by simulated annealing, minimising the number of uncovered
# residues, and aim for m = best_n // 2 + 1 so the result beats the parent.
# Every candidate is still checked with lib.is_valid before use.
# ----------------------------------------------------------------------------

def _haar_cost(S, m):
    """Number of residues not covered by the odd and even sumset conditions."""
    Sa = np.asarray(S, dtype=np.int64)
    diff = (Sa[:, None] - Sa[None, :]) % m
    dv = np.unique(diff)
    odd = np.zeros(m, dtype=bool)
    odd[((dv[:, None] + Sa[None, :]) % m).ravel()] = True
    even = np.zeros(m, dtype=bool)
    even[((dv[:, None] + dv[None, :]) % m).ravel()] = True
    return int((~odd).sum()) + int((~even).sum())


def _haar_search(d, m, rng, deadline):
    """Anneal a connection set S (size d, containing 0) in Z_m with full diameter-4 cover."""
    if m < 2 * d or d < 2:
        return None
    S = [0] + rng.sample(range(1, m), d - 1)
    cur = _haar_cost(S, m)
    best_cost, best_S = cur, list(S)
    T = 0.7
    since = 0
    while cur > 0:
        if time.monotonic() >= deadline:
            break
        since += 1
        i = rng.randrange(1, d)
        x = rng.randrange(1, m)
        if x in S:
            continue
        T2 = list(S)
        T2[i] = x
        c = _haar_cost(T2, m)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            S, cur = T2, c
            if cur < best_cost:
                best_cost, best_S = cur, list(S)
                since = 0
        if since > 20000:
            # Restart from a fresh random set after a long stall.
            S = [0] + rng.sample(range(1, m), d - 1)
            cur = _haar_cost(S, m)
            since = 0
    if cur == 0:
        return S
    if best_cost == 0:
        return best_S
    return None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    avail = max(0.5, 0.85 * time_limit - 4.0)
    deadline = start + avail
    mid = start + 0.5 * avail
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
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < mid - 2.0:
        if D >= 4:
            n0, e0 = _gq(q)
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
        else:
            n0, e0 = 0, []
        if n0 > 0:
            consider(n0, e0)
            res = _blowup(n0, e0, d, mid, rng, nprng)
            if res is not None:
                consider(res[0], res[1])

    # NEW route: cyclic Haar graph that tries to beat the current best for D = 4.
    if D == 4 and d >= 4 and time.monotonic() < deadline - 1.0:
        m = best_n // 2 + 1
        S = _haar_search(d, m, rng, deadline)
        if S is not None:
            n, e = lib.haar_graph(m, S)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
