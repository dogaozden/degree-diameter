import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) as a point/line list (table-based, pure Python).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Return (P, lines): points of W(q) indexed 0..P-1 and each totally isotropic line as a sorted point list."""
    F = lib.GF(q)
    mul = F.mul_table.tolist()
    add = F.add_table.tolist()
    neg = [next(b for b in range(q) if add[a][b] == 0) for a in range(q)]
    inv = [0] * q
    for a in range(1, q):
        inv[a] = next(b for b in range(1, q) if mul[a][b] == 1)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        ic = inv[c]
        return tuple(mul[ic][x] for x in v)

    def form(x, y):
        t = add[mul[x[0]][y[1]]][neg[mul[x[1]][y[0]]]]
        u = add[mul[x[2]][y[3]]][neg[mul[x[3]][y[2]]]]
        return add[t][u]

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i * P + j) in covered:
                continue
            y = pts[j]
            if form(x, y):
                continue
            Lset = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(add[mul[a][x[k]]][mul[b][y[k]]] for k in range(4))
                    if any(v):
                        Lset.add(index[norm(v)])
            Ls = sorted(Lset)
            lines.append(Ls)
            for p in Ls:
                for r in Ls:
                    if p < r:
                        covered.add(p * P + r)
    return P, lines


def _gq_incidence(q):
    """Incidence graph of W(q): (n, edges), points 0..P-1, lines P..P+L-1; degree q+1, diameter 4."""
    P, lines = _gq_w(q)
    L = len(lines)
    return P + L, [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]


# ----------------------------------------------------------------------------
# Maximum independent set by k-fixed tabu search (pure Python).
# ----------------------------------------------------------------------------

def _mis(n, adj, deadline, rng):
    """Return a large independent set of the graph (n vertices, adj neighbour lists) found before deadline."""
    inS = [False] * n
    c = [0] * n
    S = []

    def add(v):
        inS[v] = True
        S.append(v)
        for w in adj[v]:
            c[w] += 1

    def remove(u):
        inS[u] = False
        S.remove(u)
        for w in adj[u]:
            c[w] -= 1

    order = list(range(n))
    rng.shuffle(order)
    for v in order:
        if c[v] == 0:
            add(v)
    best = list(S)
    tab_add = [0] * n
    tab_rem = [0] * n
    it = 0
    stuck = 0
    while time.monotonic() < deadline:
        it += 1
        cost = sum(c[v] for v in S)
        if cost == 0:
            if len(S) > len(best):
                best = list(S)
                stuck = 0
            cands = [v for v in range(n) if not inS[v] and tab_add[v] <= it] \
                or [v for v in range(n) if not inS[v]]
            if not cands:
                break
            mn = min(c[v] for v in cands)
            add(rng.choice([v for v in cands if c[v] == mn]))
            continue
        stuck += 1
        if stuck > 3000:
            for v in list(S):
                remove(v)
            for v in best:
                add(v)
            stuck = 0
            continue
        ok = [u for u in S if tab_rem[u] <= it] or list(S)
        mx = max(c[u] for u in ok)
        u = rng.choice([x for x in ok if c[x] == mx])
        remove(u)
        tab_add[u] = it + rng.randint(5, 15)
        cands = [v for v in range(n) if not inS[v] and tab_add[v] <= it] \
            or [v for v in range(n) if not inS[v]]
        mn = min(c[v] for v in cands)
        v = rng.choice([x for x in cands if c[x] == mn])
        add(v)
        tab_rem[v] = it + rng.randint(5, 15)
    return best


# ----------------------------------------------------------------------------
# Twin construction on W(q), degree q+2 (for d = q+2, D = 4).
# ----------------------------------------------------------------------------

def _twin_graph(q, deadline, rng):
    P, lines = _gq_w(q)
    L = len(lines)
    pl = [[] for _ in range(P)]
    for j, Ls in enumerate(lines):
        for p in Ls:
            pl[p].append(j)
    padj = [set() for _ in range(P)]
    for Ls in lines:
        for p in Ls:
            for r in Ls:
                if p != r:
                    padj[p].add(r)
    ladj = [set() for _ in range(L)]
    for p in range(P):
        for a in pl[p]:
            for b in pl[p]:
                if a != b:
                    ladj[a].add(b)

    now = time.monotonic()
    mid = now + (deadline - now) / 2.0
    I = _mis(P, [sorted(s) for s in padj], mid, rng)
    J = _mis(L, [sorted(s) for s in ladj], deadline, rng)

    edges = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
    n = P + L
    for p in I:
        for j in pl[p]:
            edges.append((n, P + j))
        n += 1
    for j in J:
        for p in lines[j]:
            edges.append((p, n))
        n += 1
    return n, edges


# ----------------------------------------------------------------------------
# Greedy set-cover vertex extension for diameter 4.
# ----------------------------------------------------------------------------

NOISE = 0.25


def _ball3(n, adj):
    """Return per-vertex bitmasks of all vertices within distance 3."""
    reach = [1 << v for v in range(n)]
    for _ in range(3):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _pick(pool, reach, unc, rng):
    """Choose the next cover vertex from pool: best gain, or a random useful one with prob NOISE."""
    if rng.random() < NOISE:
        useful = [v for v in pool if reach[v] & unc]
        if useful:
            return rng.choice(useful)
        return -1
    best, bv = 0, -1
    for v in pool:
        g = (reach[v] & unc).bit_count()
        if g > best:
            best, bv = g, v
    return bv


def _extend(n, edges, d, deadline, rng):
    """Greedily add vertices while keeping max degree d and diameter 4; return (n, edges)."""
    edges = list(edges)
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
            u = stack.pop()
            for w in adj[u]:
                if color[w] == -1:
                    color[w] = 1 - color[u]
                    stack.append(w)

    MAX_FAILS = 20000
    fails = 0
    while time.monotonic() < deadline:
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        grown = False
        while time.monotonic() < deadline:
            spare = [v for v in range(n) if len(adj[v]) < d]
            if not spare:
                return n, edges
            if fails >= MAX_FAILS:
                return n, edges
            s0 = rng.choice(spare)
            pool = [v for v in spare if color[v] == color[s0] and v != s0]
            S = [s0]
            unc = full & ~reach[s0]
            while unc and len(S) < d and pool:
                bv = _pick(pool, reach, unc, rng)
                if bv < 0:
                    break
                S.append(bv)
                unc &= ~reach[bv]
                pool.remove(bv)
            if unc:
                fails += 1
                continue
            x = n
            n += 1
            for s in S:
                edges.append((s, x))
                adj[s].append(x)
            adj.append(list(S))
            color.append(1 - color[s0])
            fails = 0
            grown = True
            break
        if not grown:
            break
    return n, edges


# ----------------------------------------------------------------------------
# NEW: Cayley-type bipartite lifts over non-abelian groups Z_m x|_r Z_k.
#
# Graph: side A and side B each carry the group G (order N). A-vertex x is
# adjacent to B-vertex y iff x^{-1} y lies in a connection set S of size d.
# Left multiplication is an automorphism that is transitive on each side, so
# diameter <= D holds iff BFS from A-identity and from B-identity both reach
# every vertex within D steps. Each check costs O(N d), so search is cheap.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect products Z_m x|_r Z_k of order N (element code a*k+b); non-abelian preferred."""
    allg, nonab = [], []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                allg.append((m, k, r))
                if r % m != 1 % m:
                    nonab.append((m, k, r))
    return nonab or allg


def _table(m, k, r):
    """Multiplication and inverse tables for Z_m x|_r Z_k as Python lists."""
    N = m * k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    X = np.arange(N, dtype=np.int64)
    a = X // k
    b = X % k
    T = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    invT = np.argmax(T == 0, axis=1)
    return T.tolist(), invT.tolist()


def _score(N, D, Tl, S, invS):
    """Number of (start, target) pairs left unreached within D steps, summed over both identity starts."""
    total = 0
    for start_side in (0, 1):
        visA = bytearray(N)
        visB = bytearray(N)
        if start_side == 0:
            visA[0] = 1
            side = 0
        else:
            visB[0] = 1
            side = 1
        cur = [0]
        for _ in range(D):
            nxt = []
            if side == 0:
                for x in cur:
                    row = Tl[x]
                    for s in S:
                        y = row[s]
                        if not visB[y]:
                            visB[y] = 1
                            nxt.append(y)
                side = 1
            else:
                for y in cur:
                    row = Tl[y]
                    for t in invS:
                        x = row[t]
                        if not visA[x]:
                            visA[x] = 1
                            nxt.append(x)
                side = 0
            cur = nxt
            if not cur:
                break
        total += (N - sum(visA)) + (N - sum(visB))
    return total


def _climb(N, d, D, Tl, invT, rng, deadline):
    """Hill-climb a connection set S (size d) to minimise unreached pairs; return (S, score)."""
    def fresh():
        S = rng.sample(range(N), d)
        invS = [invT[s] for s in S]
        return S, invS, _score(N, D, Tl, S, invS)

    S, invS, sc = fresh()
    stall = 0
    while sc > 0 and time.monotonic() < deadline:
        i = rng.randrange(d)
        Sset = set(S)
        g = rng.randrange(N)
        while g in Sset:
            g = rng.randrange(N)
        S2 = S[:]
        S2[i] = g
        invS2 = invS[:]
        invS2[i] = invT[g]
        sc2 = _score(N, D, Tl, S2, invS2)
        if sc2 <= sc:
            stall = 0 if sc2 < sc else stall + 1
            S, invS, sc = S2, invS2, sc2
        else:
            stall += 1
        if stall > 400:
            S, invS, sc = fresh()
            stall = 0
    return S, sc


def _find_cayley(N, d, D, rng, deadline):
    """Try random groups of order N until a valid lift is found; return (n, edges) or None."""
    if N <= d:
        return None
    groups = _groups(N)
    if not groups:
        return None
    while time.monotonic() < deadline:
        m, k, r = rng.choice(groups)
        Tl, invT = _table(m, k, r)
        climb_end = min(deadline, time.monotonic() + 1.5)
        S, sc = _climb(N, d, D, Tl, invT, rng, climb_end)
        if sc == 0:
            edges = []
            for x in range(N):
                row = Tl[x]
                for s in S:
                    edges.append((x, N + row[s]))
            n = 2 * N
            if lib.is_valid(n, edges, d, D):
                return n, edges
    return None


def _lift_search(d, D, N_start, N_lo, N_max, rng, deadline):
    """Search upward from N_start for the largest feasible group order; return (n, edges) or None."""
    best = None
    N = min(N_start, N_max)
    while time.monotonic() < deadline and N_lo <= N <= N_max:
        now = time.monotonic()
        remaining = deadline - now
        slice_end = min(deadline, now + max(1.0, 0.35 * remaining))
        res = _find_cayley(N, d, D, rng, slice_end)
        if res is not None:
            best = res
            N += 1
        elif best is not None:
            break
        else:
            N -= 4
    return best


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    # Stage 1: Cayley-type lift search over non-abelian groups (new construction).
    if D >= 2 and d >= 2:
        try:
            Nmax = lib.moore_bound(d, D) // 2
            N_lo = max(d + 1, best[0] // 2 + 1)
            if N_lo <= Nmax:
                N_start = max(N_lo, int(0.75 * Nmax))
                res = _lift_search(d, D, N_start, N_lo, Nmax, rng,
                                   t0 + 0.45 * budget)
                if res is not None:
                    consider(*res)
        except Exception:
            pass

    # Stage 2: parent constructions with the remaining time.
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            now = time.monotonic()
            twin_deadline = now + 0.5 * max(0.0, deadline - now)
            n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
            consider(n2, e2)
            n3, e3 = _extend(n2, e2, d, deadline, rng)
            consider(n3, e3)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
