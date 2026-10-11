import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Parent construction (kept as the safe baseline).
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


def _symplectic_quadrangle(q):
    """Return (npts, lines, spread) for W(q) built from F_{q^2}^2, or None."""
    Q = q * q
    F = lib.GF(Q)
    mul, add, sub = F.mul, F.add, F.sub
    subfield = [x for x in range(Q) if F.pow(x, q) == x]
    if len(subfield) != q:
        return None
    scal = [x for x in subfield if x]
    tr = [add(z, F.pow(z, q)) for z in range(Q)]
    delta = 1

    pid = [-1] * (Q * Q)
    reps = []
    for a in range(Q):
        for b in range(Q):
            if (a or b) and pid[a * Q + b] < 0:
                k = len(reps)
                reps.append((a, b))
                for l in scal:
                    pid[mul(l, a) * Q + mul(l, b)] = k
    npts = len(reps)
    if npts != (Q * Q - 1) // (q - 1):
        return None

    def collinear(x, y):
        det = sub(mul(x[0], y[1]), mul(x[1], y[0]))
        return tr[mul(delta, det)] == 0

    covered = [set() for _ in range(npts)]
    lines = []
    for i in range(npts):
        x = reps[i]
        for j in range(i + 1, npts):
            if j in covered[i]:
                continue
            y = reps[j]
            if not collinear(x, y):
                continue
            L = set()
            for a in subfield:
                ax0, ax1 = mul(a, x[0]), mul(a, x[1])
                for b in subfield:
                    if a == 0 and b == 0:
                        continue
                    v0 = add(ax0, mul(b, y[0]))
                    v1 = add(ax1, mul(b, y[1]))
                    L.add(pid[v0 * Q + v1])
            if len(L) != q + 1:
                return None
            for p in L:
                covered[p] |= L
            lines.append(sorted(L))

    pdeg = [0] * npts
    for L in lines:
        for p in L:
            pdeg[p] += 1
    if any(c != q + 1 for c in pdeg):
        return None

    line_idx = {frozenset(L): j for j, L in enumerate(lines)}
    spread = []
    for v0, v1 in [(1, t) for t in range(Q)] + [(0, 1)]:
        key = frozenset(pid[mul(l, v0) * Q + mul(l, v1)] for l in range(1, Q))
        j = line_idx.get(key)
        if j is None:
            return None
        spread.append(j)
    if len(set(spread)) != Q + 1:
        return None
    return npts, lines, spread


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


def _ovoid_search(npts, lines, rng, nprng, deadline):
    """Large partial ovoid of the points: pairwise non-collinear point set."""
    nb = [set() for _ in range(npts)]
    for L in lines:
        for p in L:
            nb[p].update(L)
    nbl = []
    for p in range(npts):
        s = nb[p]
        s.discard(p)
        nbl.append(sorted(s))
    return _independent_set(npts, nbl, rng, nprng, deadline)


def _side_search(V, cs, rng, nprng, deadline):
    """Large conflict-free subset of one side V, using local conflict lists cs."""
    idx = {v: i for i, v in enumerate(V)}
    nb_local = [[idx[w] for w in cs[v] if w in idx] for v in V]
    res = _independent_set(len(V), nb_local, rng, nprng, deadline)
    return [V[i] for i in res]


def _two_colour(n, edges):
    """Return a 0/1 colouring of a bipartite graph."""
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


def _parent_build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.85 * time_limit - 3.0)
    rng = random.Random(seed)
    nprng = np.random.default_rng(abs(int(seed)) % (2 ** 32))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

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
        done = False
        if D >= 4:
            try:
                geo = _symplectic_quadrangle(q)
                if geo is not None:
                    npts, lines, spread = geo
                    n0 = npts + len(lines)
                    edges0 = [(p, npts + j) for j, L in enumerate(lines) for p in L]
                    consider(n0, edges0)
                    O = _ovoid_search(npts, lines, rng, nprng, deadline)
                    S = list(O) + [npts + j for j in spread]
                    n, e = _blow(n0, edges0, S)
                    consider(n, e)
                    done = True
            except Exception:
                done = False

        if not done:
            if D >= 4:
                n0, e0 = _gq(q)
            elif D == 3:
                n0, e0 = lib.projective_plane_incidence(q)
            else:
                n0, e0 = 0, []
            if n0 > 0:
                consider(n0, e0)
                res = _blowup(n0, e0, d, deadline, rng, nprng)
                if res is not None:
                    consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best


# ----------------------------------------------------------------------------
# New construction: bi-Cayley (Haar-type) graphs over finite groups.
#
# Group G = Z_m semidirect Z_k (element (a,b) coded as a*k+b, mult
# (a,b)(c,d) = (a + r^b c, b + d), needs r^k = 1 mod m), or cyclic if k = 1.
# Vertices a_x and b_y (x,y in G); a_x ~ b_{x s} for s in S, |S| = d.
# Left translations are automorphisms and fix the sides, so the diameter is
# checked by two BFS runs from a_e and b_e. Here S is a set of d elements with
# e in S (WLOG by relabelling B). Local search minimises the number of vertices
# not reached within distance D. A zero-cost S gives a valid graph with 2|G|
# vertices. The search tries group orders above the current best, ascending.
# ----------------------------------------------------------------------------

def _tables(m, k, r):
    """Multiplication and inverse tables of Z_m x|_r Z_k, or None if inconsistent."""
    M = m * k
    idx = np.arange(M, dtype=np.int64)
    a = idx // k
    b = idx % k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    T = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + ((b[:, None] + b[None, :]) % k)
    nb = (-b) % k
    inv = ((-(pw[nb] * a)) % m) * k + nb
    if not np.array_equal(T[idx, inv], np.zeros(M, dtype=np.int64)):
        return None
    return T, inv


def _groups(M):
    """All (m, k, r) with m*k = M giving groups of order M (cyclic when k = 1)."""
    out = []
    for m in range(2, M + 1):
        if M % m:
            continue
        k = M // m
        if k == 1:
            out.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                out.append((m, k, r))
    return out


def _cost(T, S, invS, D, M):
    """Total number of vertices at distance > D from a_e and from b_e."""
    total = 0
    for src in (0, 1):
        visA = np.zeros(M, dtype=bool)
        visB = np.zeros(M, dtype=bool)
        front = np.array([0], dtype=np.int64)
        if src == 0:
            visA[0] = True
            side = 0
        else:
            visB[0] = True
            side = 1
        for _ in range(D):
            if side == 0:
                cand = T[np.ix_(front, S)].ravel()
                new = cand[~visB[cand]]
                visB[new] = True
                side = 1
            else:
                cand = T[np.ix_(front, invS)].ravel()
                new = cand[~visA[cand]]
                visA[new] = True
                side = 0
            if new.size == 0:
                break
            front = np.unique(new)
        total += (M - int(visA.sum())) + (M - int(visB.sum()))
    return total


def _search(T, inv, M, d, D, deadline, rng):
    """Local search for a set S (|S| = d, 0 in S) with zero cost. Returns array or None."""
    while time.monotonic() < deadline:
        S = [0] + rng.sample(range(1, M), d - 1)
        arr = np.array(S, dtype=np.int64)
        cur = _cost(T, arr, inv[arr], D, M)
        best = cur
        stagn = 0
        while time.monotonic() < deadline:
            if cur == 0:
                return np.array(S, dtype=np.int64)
            if stagn > 3000:
                break
            pos = rng.randrange(1, d)
            g = rng.randrange(1, M)
            if g in S:
                continue
            new = S[:]
            new[pos] = g
            arr = np.array(new, dtype=np.int64)
            c = _cost(T, arr, inv[arr], D, M)
            if c <= cur or rng.random() < math.exp(-(c - cur) / 0.6):
                S, cur = new, c
            if cur < best:
                best = cur
                stagn = 0
            else:
                stagn += 1
    return None


def _haar_group_graph(T, S, M, d):
    """Bipartite graph on 2M vertices: a_x ~ b_{x s} for s in S."""
    Tl = T[:, S]
    edges = [(x, M + int(Tl[x, j])) for x in range(M) for j in range(d)]
    return 2 * M, edges


def _group_search(d, D, base, end, rng):
    """Try ascending group orders above the current best; return the best valid graph."""
    best_n = base[0]
    best = base
    M = best_n // 2 + 1
    M_hi = lib.moore_bound(d, D) // 2
    while M <= M_hi and time.monotonic() < end - 0.2:
        groups = _groups(M)
        rng.shuffle(groups)
        found = None
        if not groups:
            break
        while found is None and time.monotonic() < end:
            for g in groups:
                now = time.monotonic()
                if now >= end:
                    break
                tab = _tables(*g)
                if tab is None:
                    continue
                T, inv = tab
                budget = min(end, now + 0.8)
                S = _search(T, inv, M, d, D, budget, rng)
                if S is not None:
                    found = (T, S)
                    break
        if found is None:
            break
        T, S = found
        n, e = _haar_group_graph(T, S, M, d)
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
        M += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + max(0.5, 0.85 * time_limit - 2.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    try:
        base = _parent_build(d, D, seed, 0.5 * time_limit)
    except Exception:
        base = None
    if base is None or not lib.is_valid(base[0], base[1], d, D):
        base = lib.haar_graph(d, range(d))

    if d >= 4 and D >= 3 and time.monotonic() < end - 0.5:
        try:
            cand = _group_search(d, D, base, end, rng)
            if cand[0] > base[0] and lib.is_valid(cand[0], cand[1], d, D):
                base = cand
        except Exception:
            pass

    if not lib.is_valid(base[0], base[1], d, D):
        base = lib.haar_graph(d, range(d))
    return base
