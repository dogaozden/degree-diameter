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


def _cover_attempt(s0, pool_all, reach, full, d, rng, noise):
    """Cover all vertices using R3(s0) plus up to d-1 pool vertices; return the chosen set S or None."""
    S = [s0]
    unc = full & ~reach[s0]
    pool = [v for v in pool_all if v != s0]
    while unc and len(S) < d and pool:
        gains = [(reach[v] & unc).bit_count() for v in pool]
        best = max(gains)
        if best <= 0:
            break
        if noise > 0.0 and rng.random() < noise:
            thresh = max(1, int(best * 0.8))
            choices = [i for i, g in enumerate(gains) if g >= thresh]
            i = rng.choice(choices)
        else:
            top = [i for i, g in enumerate(gains) if g == best]
            i = rng.choice(top)
        bv = pool[i]
        S.append(bv)
        unc &= ~reach[bv]
        pool[i] = pool[-1]
        pool.pop()
    if unc:
        return None
    return S


def _extend(n, edges, d, deadline, rng, max_fails):
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

    fails = 0
    while time.monotonic() < deadline and fails < max_fails:
        spare = [v for v in range(n) if len(adj[v]) < d]
        if not spare:
            break
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        s0 = rng.choice(spare)
        pool_all = [v for v in spare if color[v] == color[s0]]
        S = None
        for attempt in range(4):
            noise = 0.0 if attempt == 0 else rng.choice([0.2, 0.35, 0.5])
            S = _cover_attempt(s0, pool_all, reach, full, d, rng, noise)
            if S is not None:
                break
        if S is None:
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
    return n, edges


# ----------------------------------------------------------------------------
# NEW: bi-Cayley (group-lift) search for diameter 4.
#
# Graph: side A = G, side B = G, a_x ~ b_{x*g} for g in S (|S| = d).
# Left multiplication is an automorphism acting transitively on each side, so
# the diameter is at most 4 iff every vertex is within distance 4 of a_e and of
# b_e. The group is Z_m x|_r Z_k (lib-compatible coding a*k+b), with a numpy
# multiplication table. Search over S by hill climbing on the number of
# vertices left uncovered.
# ----------------------------------------------------------------------------

def _semidirect_table(m, k, r):
    """Return (MT, inv): MT[x, y] = x*y and inv[x] = x^{-1} for Z_m x|_r Z_k, codes a*k+b, identity 0."""
    N = m * k
    codes = np.arange(N, dtype=np.int64)
    A = codes // k
    B = codes % k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    MT = ((A[:, None] + pw[B][:, None] * A[None, :]) % m) * k + (B[:, None] + B[None, :]) % k
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def _pick_group(N, rng):
    """Return (m, k, r) with m*k = N, preferring non-abelian Z_m x|_r Z_k (r != 1 of order dividing k)."""
    divs = [k for k in range(2, min(N, 40) + 1) if N % k == 0]
    rng.shuffle(divs)
    for k in divs:
        m = N // k
        if m < 3:
            continue
        cands = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
        if cands:
            return m, k, rng.choice(cands)
    return N, 1, 1


def _score(MT, inv, S, N):
    """Number of vertices not within distance 4 of a_e plus those not within distance 4 of b_e."""
    Sinv = inv[S]
    total = 0
    for start_a in (True, False):
        visA = np.zeros(N, dtype=bool)
        visB = np.zeros(N, dtype=bool)
        if start_a:
            visA[0] = True
        else:
            visB[0] = True
        side_a = start_a
        fr = np.array([0], dtype=np.int64)
        for _ in range(4):
            mark = np.zeros(N, dtype=bool)
            if side_a:
                mark[MT[np.ix_(fr, S)].ravel()] = True
                new = mark & ~visB
                visB |= new
            else:
                mark[MT[np.ix_(fr, Sinv)].ravel()] = True
                new = mark & ~visA
                visA |= new
            fr = np.nonzero(new)[0]
            side_a = not side_a
            if fr.size == 0:
                break
        total += 2 * N - int(visA.sum()) - int(visB.sum())
    return total


def _bicayley_search(d, N, deadline, rng):
    """Hill-climb a connection set S of size d in a group of order N; return (S, MT) on success, else None."""
    m, k, r = _pick_group(N, rng)
    MT, inv = _semidirect_table(m, k, r)
    S = np.array(rng.sample(range(N), d), dtype=np.int64)
    f = _score(MT, inv, S, N)
    stall = 0
    it = 0
    while f > 0:
        it += 1
        if (it & 31) == 0 and time.monotonic() >= deadline:
            return None
        if stall > 2500:
            S = np.array(rng.sample(range(N), d), dtype=np.int64)
            f = _score(MT, inv, S, N)
            stall = 0
            continue
        pos = rng.randrange(d)
        c = rng.randrange(N)
        if (S == c).any():
            continue
        S2 = S.copy()
        S2[pos] = c
        f2 = _score(MT, inv, S2, N)
        if f2 < f:
            stall = 0
        else:
            stall += 1
        if f2 <= f or rng.random() < 0.02:
            S, f = S2, f2
    return S, MT


def _bicayley_edges(N, MT, S, d):
    """Return (2N, edges) for the bi-Cayley graph: a_x = x, b_y = N + y."""
    X = np.repeat(np.arange(N, dtype=np.int64), d)
    Y = MT[:, S].ravel()
    return 2 * N, list(zip(X.tolist(), (N + Y).tolist()))


# ----------------------------------------------------------------------------
# Parent pipeline (twin graph + set-cover extension), unchanged logic.
# ----------------------------------------------------------------------------

def _better(best, n, edges, d, D):
    """Return (n, edges) if it is larger than best and valid, else best."""
    if n > best[0] and lib.is_valid(n, edges, d, D):
        return (n, edges)
    return best


def _parent(d, D, rng, deadline, best):
    """Projective plane, GQ, and twin-graph extension pipeline; returns the best valid graph found."""
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            best = _better(best, *lib.projective_plane_incidence(d - 1), d, D)
        except Exception:
            pass

    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            best = _better(best, *_gq_incidence(d - 1), d, D)
        except Exception:
            pass

    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        base = None
        try:
            now = time.monotonic()
            base = _twin_graph(d - 2, now + 0.35 * (deadline - now), rng)
            best = _better(best, base[0], base[1], d, D)
        except Exception:
            base = None

        if base is not None and lib.is_valid(base[0], base[1], d, D):
            ext_best = base
            stagnant = 0
            while time.monotonic() < deadline - 0.5 and stagnant < 6:
                now = time.monotonic()
                remaining = deadline - now
                run_end = min(deadline, now + max(2.0, remaining / 3.0))
                if rng.random() < 0.5:
                    start = ext_best
                else:
                    start = base
                try:
                    n3, e3 = _extend(start[0], start[1], d, run_end, rng, 3000)
                except Exception:
                    stagnant += 1
                    continue
                if n3 > ext_best[0] and lib.is_valid(n3, e3, d, D):
                    ext_best = (n3, e3)
                    best = _better(best, n3, e3, d, D)
                    stagnant = 0
                else:
                    stagnant += 1
    return best


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    # Bold phase (targets d=11, D=4): bi-Cayley group-lift search with a
    # ratcheting lower bound on the group order.
    if D == 4 and d == 11:
        bc_deadline = t0 + 0.3 * budget
        while time.monotonic() < bc_deadline - 0.5:
            Nmin = best[0] // 2 + 1
            if 2 * Nmin > lib.moore_bound(d, D):
                break
            N = rng.randint(Nmin, Nmin + 40)
            now = time.monotonic()
            slice_end = min(bc_deadline, now + max(3.0, (bc_deadline - now) / 2.0))
            try:
                res = _bicayley_search(d, N, slice_end, rng)
                if res is not None:
                    S, MT = res
                    n2, e2 = _bicayley_edges(N, MT, S, d)
                    best = _better(best, n2, e2, d, D)
            except Exception:
                pass

    # Parent pipeline with the remaining time.
    best = _parent(d, D, rng, deadline, best)

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
