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
# NEW helper: spread search by randomized exact cover.
#
# A spread of a generalized quadrangle W(q) is a set of q^2+1 pairwise disjoint
# lines covering every point. Two disjoint lines are never concurrent, so a
# spread is a conflict-free set for the line side of the twin blow-up, and it
# has the maximum possible size. Local search rarely reaches it, so we search
# for an exact cover directly (Algorithm X style: branch on the point with the
# fewest still-available lines, random tie-breaking, restarts with a node-time
# cap).
# ----------------------------------------------------------------------------

def _find_spread(P, lines, deadline, rng):
    """Return indices of a spread of the lines (exact cover of 0..P-1), or None."""
    k = len(lines[0])
    if P % k != 0:
        return None
    target = P // k
    pl = [[] for _ in range(P)]
    for j, L in enumerate(lines):
        for p in L:
            pl[p].append(j)

    while time.monotonic() < deadline:
        attempt_end = min(deadline, time.monotonic() + 6.0)
        used = bytearray(P)
        chosen = []
        state = {"abort": False, "nodes": 0}

        def dfs():
            if len(chosen) == target:
                return True
            state["nodes"] += 1
            if (state["nodes"] & 7) == 0 and time.monotonic() > attempt_end:
                state["abort"] = True
                return False
            best = None
            for p in range(P):
                if used[p]:
                    continue
                opts = [j for j in pl[p] if all(not used[x] for x in lines[j])]
                if not opts:
                    return False
                if best is None or len(opts) < len(best):
                    best = opts
                    if len(opts) == 1:
                        break
            rng.shuffle(best)
            for j in best:
                for x in lines[j]:
                    used[x] = 1
                chosen.append(j)
                if dfs():
                    return True
                chosen.pop()
                for x in lines[j]:
                    used[x] = 0
                if state["abort"]:
                    return False
            return False

        if dfs():
            spread = sorted(chosen)
            # Verify: pairwise disjoint and covering.
            cov = set()
            for j in spread:
                for x in lines[j]:
                    if x in cov:
                        return None
                    cov.add(x)
            if len(cov) == P:
                return spread
            return None
    return None


# ----------------------------------------------------------------------------
# Twin blow-up with a distance-2-free vertex set.
#
# If every vertex of a base graph G has degree d-1, replace some vertices v by
# two copies (v, v') that share the same neighbourhood. Each copy of u then has
# degree sum_{v in N(u)} m_v with m_v in {1, 2}; since |N(u)| = d-1 the degree
# stays <= d iff u has at most one neighbour in S = {v : m_v = 2}. So S must
# have no two vertices at distance 2. Blow-ups keep bipartiteness and diameter.
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


def _blowup(n0, edges0, d, split, deadline, rng, nprng, fixed_b=None):
    """Twin blow-up of a base graph of degree d-1.

    Vertices 0..split-1 form one side and split..n0-1 the other; conflicts only
    occur within a side. If fixed_b is given (a conflict-free set on side B,
    e.g. a spread), it is used for side B and only side A is searched.
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

    if fixed_b is not None:
        S_a = _independent_set(n0, nb, side_a, rng, nprng, deadline)
        S_b = list(fixed_b)
    else:
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
            fixed = None
            if D >= 4:
                # Line side: a spread (q^2+1 disjoint lines) is the largest
                # conflict-free set there. Give the search a share of the time.
                lines = [[] for _ in range(n0 - split)]
                for u, v in e0:
                    lines[v - split].append(u)
                now = time.monotonic()
                sp_deadline = now + 0.45 * (deadline - now)
                sp = _find_spread(split, lines, sp_deadline, rng)
                if sp is not None:
                    fixed = [split + j for j in sp]
            res = _blowup(n0, e0, d, split, deadline, rng, nprng, fixed)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
