import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _bipartition(n, adj):
    """Return the 2-colouring of the graph, or None if it is not bipartite."""
    color = [-1] * n
    for s in range(n):
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
                elif color[v] == color[u]:
                    return None
    return color


# ----------------------------------------------------------------------------
# NEW: abelian bi-Cayley (Haar-type) search.
#
# Group G = Z_a x Z_b (order m = a*b, element (i, j) coded as i*b + j).
# Connection set S = {s_1..s_d} distinct in G. Graph: A_x ~ B_{x+s} for s in S.
# This is d-regular, bipartite, simple, on 2m vertices. Translations by G are
# automorphisms and act transitively on each side, so the diameter is <= D iff
# BFS from A_0 and from B_0 both reach every vertex within D steps. One cheap
# vectorised cost (count of unreached vertices) drives simulated annealing over S.
# Every success is still checked with lib.is_valid before it is accepted.
# ----------------------------------------------------------------------------

_GROUP_CACHE = {}


def _group_tables(a, b):
    """Return (Mm, neg): Mm[t][y] = index of y - t, neg[t] = index of -t, for Z_a x Z_b."""
    key = (a, b)
    if key in _GROUP_CACHE:
        return _GROUP_CACHE[key]
    if len(_GROUP_CACHE) > 40:
        _GROUP_CACHE.clear()
    m = a * b
    idx = np.arange(m, dtype=np.int64)
    ci, cj = idx // b, idx % b
    Mm = (((ci[None, :] - ci[:, None]) % a) * b
          + (cj[None, :] - cj[:, None]) % b).astype(np.int64)
    neg = (((-ci) % a) * b + ((-cj) % b)).astype(np.int64)
    _GROUP_CACHE[key] = (Mm, neg)
    return Mm, neg


def _haar_cost(S, Mm, neg, m, D):
    """Total unreached (vertex, start) pairs from A_0 and B_0 within D steps; 0 iff diameter <= D."""
    maps = [(Mm[s], Mm[neg[s]]) for s in S]
    cost = 0
    for start in (0, 1):
        A = np.zeros(m, dtype=bool)
        B = np.zeros(m, dtype=bool)
        if start == 0:
            A[0] = True
        else:
            B[0] = True
        for _ in range(D):
            nB = B.copy()
            nA = A.copy()
            for fb, fa in maps:
                nB |= A[fb]   # B_y reached if A_{y-s} reached
                nA |= B[fa]   # A_x reached if B_{x+s} reached
            if np.array_equal(nA, A) and np.array_equal(nB, B):
                break
            A, B = nA, nB
        cost += (m - int(A.sum())) + (m - int(B.sum()))
    return cost


def _anneal_haar(d, D, a, b, rng, deadline, iters, patience):
    """Anneal a connection set S of size d in Z_a x Z_b. Returns S (list of indices) or None."""
    m = a * b
    if d > m or m < 2:
        return None
    Mm, neg = _group_tables(a, b)
    S = rng.sample(range(m), d)
    cost = _haar_cost(S, Mm, neg, m, D)
    c0 = float(max(cost, 1))
    best = cost
    last = 0
    for t in range(iters):
        if cost == 0:
            break
        if t - last > patience or time.monotonic() > deadline:
            break
        temp = max(0.5, 0.02 * c0 * (1.0 - t / iters))
        i = rng.randrange(d)
        cand = rng.randrange(m)
        if cand in S:
            continue
        old = S[i]
        S[i] = cand
        c2 = _haar_cost(S, Mm, neg, m, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
            if cost < best:
                best, last = cost, t
        else:
            S[i] = old
    return list(S) if cost == 0 else None


def _haar_graph_from(S, Mm, neg, m):
    """Edges of the bi-Cayley graph: A_x (id x) ~ B_{x+s} (id m + index)."""
    edges = []
    for s in S:
        cols = Mm[neg[s]]  # cols[x] = index of x + s
        for x in range(m):
            edges.append((x, m + int(cols[x])))
    return 2 * m, edges


# ----------------------------------------------------------------------------
# Double-vertex insertion, 2-switch repair, and 2-switch kicks (from parent).
#
# For a d-regular bipartite graph, pick a matching M = {(a_i, b_i)} of size d.
# Delete M, add a B-vertex w joined to all a_i and an A-vertex w' joined to all
# b_i. Degrees stay d, bipartiteness stays, order grows by 2. Pairs at distance
# > D are then removed by annealed degree-preserving 2-switches.
# ----------------------------------------------------------------------------

def _ball_bad(nbr, D):
    """Ordered pairs (u, v) with distance > D (unreachable counted); 0 iff diameter <= D."""
    n = nbr.shape[0]
    R = np.eye(n, dtype=bool)
    for _ in range(D):
        R2 = R | R[nbr].any(axis=1)
        if np.array_equal(R2, R):
            break
        R = R2
    return n * n - int(R.sum())


def _insert_pair(nbr, color, d, rng):
    """Insert one B-vertex and one A-vertex via a random d-matching; returns (nbr, color) or None."""
    n = nbr.shape[0]
    A = [a for a in range(n) if color[a] == 0]
    edges = [(a, int(nbr[a, j])) for a in A for j in range(d)]
    rng.shuffle(edges)
    usedA, usedB, match = set(), set(), []
    for a, b in edges:
        if a not in usedA and b not in usedB:
            match.append((a, b))
            usedA.add(a)
            usedB.add(b)
            if len(match) == d:
                break
    if len(match) < d:
        return None
    w = n
    wp = n + 1
    new = np.empty((n + 2, d), dtype=np.int64)
    new[:n] = nbr
    new[w] = [a for a, _ in match]
    new[wp] = [b for _, b in match]
    for a, b in match:
        row = new[a]
        row[np.flatnonzero(row == b)[0]] = w
        row = new[b]
        row[np.flatnonzero(row == a)[0]] = wp
    return new, list(color) + [1, 0]


def _kick(nbr, A, d, rng, steps):
    """Apply up to `steps` random 2-switches in place; keeps regularity and bipartiteness."""
    done = 0
    tries = 0
    while done < steps and tries < steps * 20:
        tries += 1
        a1 = A[rng.randrange(len(A))]
        a2 = A[rng.randrange(len(A))]
        if a1 == a2:
            continue
        j1 = rng.randrange(d)
        j2 = rng.randrange(d)
        b1 = int(nbr[a1, j1])
        b2 = int(nbr[a2, j2])
        if b1 == b2 or b2 in nbr[a1] or b1 in nbr[a2]:
            continue
        nbr[a1, j1] = b2
        nbr[a2, j2] = b1
        row = nbr[b1]
        row[np.flatnonzero(row == a1)[0]] = a2
        row = nbr[b2]
        row[np.flatnonzero(row == a2)[0]] = a1
        done += 1
    return done


def _repair(nbr, A, d, D, rng, iters, deadline):
    """Anneal degree-preserving 2-switches to remove pairs at distance > D. Returns (best_nbr, best_bad)."""
    cur = nbr.copy()
    cur_bad = _ball_bad(cur, D)
    best, best_bad = cur.copy(), cur_bad
    T = 2.0
    for _ in range(iters):
        if best_bad == 0 or time.monotonic() > deadline:
            break
        a1 = A[rng.randrange(len(A))]
        a2 = A[rng.randrange(len(A))]
        if a1 == a2:
            continue
        j1 = rng.randrange(d)
        j2 = rng.randrange(d)
        b1 = int(cur[a1, j1])
        b2 = int(cur[a2, j2])
        if b1 == b2 or b2 in cur[a1] or b1 in cur[a2]:
            continue
        cand = cur.copy()
        cand[a1, j1] = b2
        cand[a2, j2] = b1
        row = cand[b1]
        row[np.flatnonzero(row == a1)[0]] = a2
        row = cand[b2]
        row[np.flatnonzero(row == a2)[0]] = a1
        c = _ball_bad(cand, D)
        if c <= cur_bad or rng.random() < math.exp(-(c - cur_bad) / T):
            cur, cur_bad = cand, c
            if c < best_bad:
                best, best_bad = cand.copy(), c
    return best, best_bad


def _grow_regular(n, edges, d, D, rng, deadline):
    """Insert vertex pairs, repair, and kick on stagnation; return the largest valid (n, edges) found, or None."""
    adj = lib.adjacency(n, edges)
    if any(len(a) != d for a in adj):
        return None
    color = _bipartition(n, adj)
    if color is None:
        return None
    cur = np.array(adj, dtype=np.int64)
    ccol = color
    result = None
    fails = 0
    while time.monotonic() < deadline:
        ins = _insert_pair(cur, ccol, d, rng)
        if ins is None:
            A0 = [i for i, c in enumerate(ccol) if c == 0]
            _kick(cur, A0, d, rng, 20)
            continue
        new, ncol = ins
        A = [i for i, c in enumerate(ncol) if c == 0]
        bn, bb = _repair(new, A, d, D, rng, 400, deadline)
        if bb == 0:
            cur, ccol = bn, ncol
            fails = 0
            N = len(ncol)
            result = (N, [(a, int(b)) for a in range(N) if ncol[a] == 0 for b in bn[a]])
        else:
            fails += 1
            if fails % 8 == 0:
                A0 = [i for i, c in enumerate(ccol) if c == 0]
                _kick(cur, A0, d, rng, 30)
    return result


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (from parent).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                r = None
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e))."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex over representative blocks within distance D."""
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _unreached(k, N, reach):
    """Number of unreached (representative, vertex) pairs."""
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing with stagnation restarts. Returns (n, edges) or None."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    reach = _reach(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))
    best_cost = cost
    last_improve = 0

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last_improve > patience:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
                if cost < best_cost:
                    best_cost, last_improve = cost, t
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
            l = rng.randrange(d)
            if block < k:
                i = block
            else:
                i = layers[l].index(block - k)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        r2 = _reach(k, G, D, nbr, d)
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
            if cost < best_cost:
                best_cost, last_improve = cost, t
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    search_deadline = start + max(1.0, min(0.6 * time_limit, time_limit - 8.0))
    final_deadline = start + max(1.0, time_limit - 4.0)
    rng = random.Random(seed)

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
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < search_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # NEW stage A: abelian bi-Cayley (Haar-type) annealing, climbing the group order.
    if d >= 2 and D >= 2:
        ab_deadline = start + 0.5 * (search_deadline - start)
        m_cur = best_n // 2
        while time.monotonic() < ab_deadline:
            m = m_cur + 1 + rng.randrange(3)
            divs = [x for x in range(1, m + 1) if m % x == 0]
            a = rng.choice(divs)
            b = m // a
            try:
                res = _anneal_haar(d, D, a, b, rng, ab_deadline, 2500, 700)
            except Exception:
                res = None
            if res is not None:
                Mm, neg = _group_tables(a, b)
                n_new, e_new = _haar_graph_from(res, Mm, neg, m)
                if consider(n_new, e_new):
                    m_cur = max(m_cur, m)

    # Stage B: parent's semidirect-product bi-Cayley search.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < search_deadline:
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, search_deadline, 4000, 1200)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Stage C: insert vertex pairs into the best regular graph, repair, kick on stagnation.
    if d >= 3 and time.monotonic() < final_deadline - 1.0:
        try:
            ext = _grow_regular(best[0], best[1], d, D, rng, final_deadline - 1.0)
        except Exception:
            ext = None
        if ext is not None:
            consider(ext[0], ext[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
