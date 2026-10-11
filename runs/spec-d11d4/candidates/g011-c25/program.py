import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bases (parent construction, kept as the safe route).
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
# Twin blow-up with a distance-2-free vertex set, searched side by side.
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

    if N == 0:
        return []

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


def _side_search(V, cs, rng, nprng, deadline):
    """Large conflict-free subset of one side V, using local conflict lists cs."""
    idx = {v: i for i, v in enumerate(V)}
    nb_local = [[idx[w] for w in cs[v] if w in idx] for v in V]
    res = _independent_set(len(V), nb_local, rng, nprng, deadline)
    return [V[i] for i in res]


def _two_colour(n, edges):
    """Return a 0/1 colouring of a bipartite graph (vertices in each component start at 0)."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if color[y] == -1:
                    color[y] = 1 - color[x]
                    stack.append(y)
    return color


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
    """Twin blow-up of a base graph of degree d-1, searching each side separately."""
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
    if n0 <= 60:
        deadline = min(deadline, time.monotonic() + 2.0)
    color = _two_colour(n0, edges0)
    sides = [[v for v in range(n0) if color[v] == c] for c in (0, 1)]

    now = time.monotonic()
    total = max(0.0, deadline - now)
    S = []
    S += _side_search(sides[0], cs, rng, nprng, now + 0.5 * total)
    S += _side_search(sides[1], cs, rng, nprng, deadline)
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------
# New route: bi-Cayley graphs over small groups.
#
# Vertices are A = {0..M-1} and B = {M..2M-1}, with a_x ~ b_{x*s} for s in S,
# |S| = d. Left multiplication is an automorphism that is transitive on each
# side, so diameter <= D holds iff every vertex lies within distance D of a_e
# and of b_e. The search is simulated annealing over S that minimises the
# number of unreached vertices from those two sources. Any result is still
# checked with lib.is_valid before use.
# ----------------------------------------------------------------------------

def _groups_of_order(M):
    """Return (mul, inv) pairs for Z_M and for semidirect products Z_m x| Z_k with m*k = M."""
    groups = [lib.cyclic_group(M)[1:]]
    for k in range(2, M):
        if M % k:
            continue
        m = M // k
        if m < 3:
            continue
        rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
        for r in rs[:3]:
            groups.append(lib.semidirect_group(m, k, r)[1:])
    return groups


def _bicayley_cost(M, pairs, mul, D):
    """Count vertices not within distance D of a_e or of b_e (pairs = [(s, s^-1)])."""
    n = 2 * M
    total = 0
    for src in (0, M):
        seen = bytearray(n)
        seen[src] = 1
        frontier = [src]
        reached = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < M:
                    for s, _si in pairs:
                        w = M + mul(v, s)
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    y = v - M
                    for _s, si in pairs:
                        w = mul(y, si)
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            reached += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += n - reached
    return total


def _search_bicayley(M, d, D, mul, inv, deadline, rng):
    """Anneal a connection set S of size d in the group of order M; return S or None."""
    if d > M:
        return None

    def cost(S):
        return _bicayley_cost(M, [(s, inv(s)) for s in S], mul, D)

    while time.monotonic() < deadline:
        cur = rng.sample(range(M), d)
        c = cost(cur)
        T = 1.5
        stall = 0
        while c > 0 and stall < 1500 and time.monotonic() < deadline:
            i = rng.randrange(d)
            g = rng.randrange(M)
            if g in cur:
                stall += 1
                continue
            new = cur[:]
            new[i] = g
            c2 = cost(new)
            if c2 < c:
                stall = 0
            else:
                stall += 1
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
                cur, c = new, c2
            T = max(0.2, T * 0.998)
        if c == 0:
            return cur
    return None


def _bicayley_route(d, D, best_n, deadline, rng):
    """Try bi-Cayley graphs of order 2M for M just above best_n / 2. Return (n, edges) or None."""
    best = None
    for M in range(best_n // 2 + 1, best_n // 2 + 1 + 40):
        now = time.monotonic()
        if now >= deadline:
            break
        cap = min(deadline, now + 8.0)
        groups = _groups_of_order(M)
        found = None
        for idx, (mul, inv) in enumerate(groups):
            now = time.monotonic()
            if now >= cap:
                break
            end = now + (cap - now) / (len(groups) - idx)
            S = _search_bicayley(M, d, D, mul, inv, end, rng)
            if S is not None:
                found = (mul, S)
                break
        if found is None:
            continue
        mul, S = found
        n, e = lib.group_lift(2, [(0, 1, s) for s in S], M, mul)
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
    return best


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, 0.8 * time_limit - 4.0)
    deadline = start + budget
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

    bic_on = (D == 4 and d >= 6)
    parent_deadline = start + (0.5 * budget if bic_on else budget)

    pg = _pg(d)
    if pg is not None:
        consider(pg[0], pg[1])

    # Blow-up route: base of degree exactly d-1 with q = d-2 a prime power.
    q = d - 2
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < parent_deadline - 2.0:
        if D >= 4:
            n0, e0 = _gq(q)
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
        else:
            n0, e0 = 0, []
        if n0 > 0:
            consider(n0, e0)
            res = _blowup(n0, e0, d, parent_deadline, rng, nprng)
            if res is not None:
                consider(res[0], res[1])

    # New route: bi-Cayley lifts over small groups, aimed past the current best.
    if bic_on and time.monotonic() < deadline - 3.0:
        try:
            res = _bicayley_route(d, D, best_n, deadline - 1.0, rng)
            if res is not None:
                consider(res[0], res[1])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
