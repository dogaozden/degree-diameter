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
# Maximum independent set by iterated local search with (1,2)-swaps.
# ----------------------------------------------------------------------------

def _mis(n, adj, deadline, rng):
    """Return a large independent set of the graph (n vertices, adj neighbour lists) found before deadline."""
    if n == 0:
        return []
    inS = [False] * n
    c = [0] * n
    S = set()
    adjset = [set(a) for a in adj]

    def add(v):
        inS[v] = True
        S.add(v)
        for w in adj[v]:
            c[w] += 1

    def remove(u):
        inS[u] = False
        S.discard(u)
        for w in adj[u]:
            c[w] -= 1

    def local_search():
        while True:
            changed = False
            free = [v for v in range(n) if not inS[v] and c[v] == 0]
            rng.shuffle(free)
            for v in free:
                if not inS[v] and c[v] == 0:
                    add(v)
                    changed = True
            for x in list(S):
                if not inS[x]:
                    continue
                one = [u for u in adj[x] if c[u] == 1]
                if len(one) < 2:
                    continue
                rng.shuffle(one)
                pair = None
                for i in range(len(one)):
                    for j in range(i + 1, len(one)):
                        if one[j] not in adjset[one[i]]:
                            pair = (one[i], one[j])
                            break
                    if pair is not None:
                        break
                if pair is not None:
                    remove(x)
                    add(pair[0])
                    add(pair[1])
                    changed = True
            if not changed:
                break

    order = list(range(n))
    rng.shuffle(order)
    for v in order:
        if not inS[v] and c[v] == 0:
            add(v)
    local_search()
    best = list(S)
    stale = 0

    while time.monotonic() < deadline:
        cand = [v for v in range(n) if not inS[v]]
        if not cand:
            break
        v = rng.choice(cand)
        for w in adj[v]:
            if inS[w]:
                remove(w)
        add(v)
        local_search()
        if len(S) > len(best):
            best = list(S)
            stale = 0
        else:
            stale += 1
        if len(S) < len(best) - 1 or stale > 300:
            for u in list(S):
                remove(u)
            for u in best:
                add(u)
            stale = 0
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
# Randomized greedy set-cover vertex extension for diameter 4.
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
    """Choose the next cover vertex: best gain, or a random useful one with prob NOISE."""
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
# NEW: orbit-reduced bi-Cayley search over finite groups.
#
# Group G (order N, identity coded 0) acts on bi-Cayley graph
#   A_x ~ B_{x*s} for s in S  (|S| = d, distinct),
# by left multiplication, which is an automorphism and is transitive on each
# side. So diameter <= R holds iff eccentricities of A_0 and B_0 are <= R.
# We search connection sets S by simulated-annealing on the number of vertices
# left outside radius R of A_0 and B_0, using vectorised numpy BFS.
# Groups: Z_m x|_r Z_k (r^k = 1 mod m), covering cyclic and abelian cases too.
# ----------------------------------------------------------------------------

def _group_order_candidates(N):
    """All (m, k, r) with m*k = N giving Z_m x|_r Z_k (r^k = 1 mod m, gcd(r, m) = 1)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m == 1:
            out.append((1, k, 0))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _mul_table(m, k, r):
    """Full multiplication table (int64) of Z_m x|_r Z_k, element (a, b) coded as a*k + b."""
    N = m * k
    pw = np.array([pow(r, b, m) if m > 1 else 0 for b in range(k)], dtype=np.int64)
    x = np.arange(N, dtype=np.int64)
    a = x // k
    b = x % k
    A1, B1 = a[:, None], b[:, None]
    A2, B2 = a[None, :], b[None, :]
    return ((A1 + pw[B1] * A2) % m) * k + (B1 + B2) % k


def _score(MT, IV, S, R, N):
    """Vertices outside radius R of A_0 plus of B_0 for bi-Cayley graph with connection set S (list)."""
    Sarr = np.array(S, dtype=np.int64)
    Sinv = IV[Sarr]
    empty = np.empty(0, dtype=np.int64)
    bad = 0
    for start in (0, 1):
        visA = np.zeros(N, dtype=bool)
        visB = np.zeros(N, dtype=bool)
        if start == 0:
            visA[0] = True
            fA, fB = np.array([0], dtype=np.int64), empty
        else:
            visB[0] = True
            fA, fB = empty, np.array([0], dtype=np.int64)
        for _ in range(R):
            if fA.size == 0 and fB.size == 0:
                break
            if fA.size:
                cB = np.unique(MT[np.ix_(fA, Sarr)])
                cB = cB[~visB[cB]]
            else:
                cB = empty
            if fB.size:
                cA = np.unique(MT[np.ix_(fB, Sinv)])
                cA = cA[~visA[cA]]
            else:
                cA = empty
            visB[cB] = True
            visA[cA] = True
            fA, fB = cA, cB
        bad += (N - int(visA.sum())) + (N - int(visB.sum()))
    return bad


def _hill(MT, IV, d, R, N, deadline, rng):
    """Anneal a connection set of size d; return it if diameter <= R is reached before deadline."""
    if d > N:
        return None
    S = rng.sample(range(N), d)
    f = _score(MT, IV, S, R, N)
    best_f, best_S = f, list(S)
    t_start = time.monotonic()
    span = max(1e-3, deadline - t_start)
    while f > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - t_start) / span
        T = 0.6 * (1.0 - frac) + 0.05
        i = rng.randrange(d)
        c = rng.randrange(N)
        if c in S:
            continue
        S2 = list(S)
        S2[i] = c
        f2 = _score(MT, IV, S2, R, N)
        if f2 <= f or rng.random() < math.exp(-(f2 - f) / T):
            S, f = S2, f2
            if f < best_f:
                best_f, best_S = f, list(S)
    return best_S if best_f == 0 else None


def _bicayley_graph(MT, S, N):
    """Build (2N, edges): A_x = x, B_y = N + y, A_x ~ B_{x*s}."""
    edges = []
    for x in range(N):
        for y in MT[x, S].tolist():
            edges.append((x, N + y))
    return 2 * N, edges


def _group_search(d, D, N_start, N_max, deadline, rng, consider):
    """Scan group orders N from N_start upward, annealing bi-Cayley connection sets; feed hits to consider."""
    N = N_start
    while N <= N_max and time.monotonic() < deadline - 0.2:
        cands = _group_order_candidates(N)
        rng.shuffle(cands)
        for (m, k, r) in cands[:10]:
            if time.monotonic() >= deadline - 0.2:
                break
            MT = _mul_table(m, k, r)
            IV = np.argmax(MT == 0, axis=1)
            slice_end = min(deadline, time.monotonic() + 1.0)
            S = _hill(MT, IV, d, D, N, slice_end, rng)
            if S is not None:
                n, edges = _bicayley_graph(MT, S, N)
                if consider(n, edges):
                    break
        N += 1


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
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
            return True
        return False

    # Parent pipeline gets half the budget; group search gets the rest.
    pb = 0.5 * budget
    pdl = t0 + pb

    try:
        # Projective plane incidence graph: degree d, diameter 3.
        if D >= 3 and lib.is_prime_power(d - 1):
            try:
                consider(*lib.projective_plane_incidence(d - 1))
            except Exception:
                pass

        # Generalized quadrangle W(d-1): degree d, diameter 4.
        if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
            try:
                consider(*_gq_incidence(d - 1))
            except Exception:
                pass

        # Twin graph on W(d-2), then randomized set-cover extensions.
        if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
            try:
                twin_deadline = t0 + 0.35 * pb
                n2, e2 = _twin_graph(d - 2, twin_deadline, rng)
                consider(n2, e2)
                attempts = 3
                for a in range(attempts):
                    now = time.monotonic()
                    if now >= pdl - 0.5:
                        break
                    slice_end = now + (pdl - now) / (attempts - a)
                    n3, e3 = _extend(n2, e2, d, min(slice_end, pdl), rng)
                    consider(n3, e3)
            except Exception:
                pass
    except Exception:
        pass

    # New route: orbit-reduced bi-Cayley search over groups, targeting orders above current best.
    if D >= 4 and d >= 3:
        try:
            moore = lib._moore_bound(d, D)
            N_max = min(moore // 2, 1600)
            N_start = best[0] // 2 + 1
            if N_start <= N_max:
                _group_search(d, D, N_start, N_max, t0 + budget, rng, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
