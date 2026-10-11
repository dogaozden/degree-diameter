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

    Points are 0..P-1, lines are P..P+L-1. Returns (n, edges, P).
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
# Twin blow-up of a base graph of degree d-1 by a set S of base vertices with
# no two sharing a neighbour (distance-2-free). Copies keep degree <= d,
# bipartiteness and diameter.
#
# NEW HELPER: exact-cover spread search. For W(q) the line side of S must be a
# set of pairwise disjoint lines (a partial spread). A full spread covers every
# point exactly once, so we search for it by randomized DFS with
# minimum-remaining-values branching over uncovered points, using a
# per-line "covered point count" so that each line-freeness test is O(1).
# Restarts with node limits give diverse attempts. The best partial spread
# found seeds the independent-set local search.
# ----------------------------------------------------------------------------

def _spread(h, adj, rng, deadline, target, node_limit=800):
    """Randomized exact-cover search for up to `target` pairwise disjoint lines.

    Points are 0..h-1; lines are the vertices >= h. Returns the best packing found.
    """
    n0 = len(adj)
    cov = bytearray(n0)
    cnt = [0] * n0
    chosen = []
    best = []
    state = {"nodes": 0, "abort": False}

    def take(M):
        for p in adj[M]:
            cov[p] = 1
            for X in adj[p]:
                cnt[X] += 1
        chosen.append(M)

    def untake(M):
        chosen.pop()
        for p in adj[M]:
            cov[p] = 0
            for X in adj[p]:
                cnt[X] -= 1

    def dfs():
        nonlocal best
        if len(chosen) > len(best):
            best = list(chosen)
        if len(chosen) >= target:
            return True
        state["nodes"] += 1
        if state["nodes"] > node_limit or time.monotonic() > deadline:
            state["abort"] = True
            return False
        bc = None
        for p in range(h):
            if cov[p]:
                continue
            c = [M for M in adj[p] if cnt[M] == 0]
            if bc is None or len(c) < len(bc):
                bc = c
                if len(c) <= 1:
                    break
        if not bc:
            return False
        rng.shuffle(bc)
        for M in bc:
            take(M)
            if dfs():
                return True
            untake(M)
            if state["abort"]:
                return False
        return False

    while time.monotonic() < deadline and len(best) < target:
        state["nodes"] = 0
        state["abort"] = False
        if dfs():
            break
    return best


def _independent_set(N, nb, rng, nprng, deadline, init=(), forbid=None):
    """Iterated local search for a large set of vertices with no conflicting pair."""
    nbn = [np.asarray(x, dtype=np.int64) for x in nb]
    cnt = np.zeros(N, dtype=np.int64)
    inS = np.zeros(N, dtype=bool)
    tabu = np.zeros(N, dtype=np.int64)
    if forbid is not None:
        tabu[forbid] = 1 << 60
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

    for v in init:
        add(v)

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


def _blowup(n0, edges0, h, d, deadline, rng, nprng):
    """Twin blow-up: spread-seeded search on the line side, ILS on the point side."""
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

    now = time.monotonic()
    tot = max(0.0, deadline - now)
    target = h // (d - 1)
    spread = _spread(h, adj, rng, now + 0.35 * tot, target)
    lines_S = list(spread)
    if len(spread) < target:
        forbid_pts = np.zeros(n0, dtype=bool)
        forbid_pts[:h] = True
        now2 = time.monotonic()
        lines_S = _independent_set(n0, nb, rng, nprng,
                                   now2 + 0.3 * max(0.0, deadline - now2),
                                   init=spread, forbid=forbid_pts)
    forbid_lines = np.zeros(n0, dtype=bool)
    forbid_lines[h:] = True
    pts_S = _independent_set(n0, nb, rng, nprng, deadline,
                             init=(), forbid=forbid_lines)
    return _blow(n0, edges0, list(lines_S) + list(pts_S))


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.8 * time_limit - 3.0)
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

    q = d - 2
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < deadline - 2.0:
        n0 = 0
        if D >= 4:
            n0, e0, h0 = _gq(q)
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
            h0 = n0 // 2
        if n0 > 0:
            consider(n0, e0)
            res = _blowup(n0, e0, h0, d, deadline, rng, nprng)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
