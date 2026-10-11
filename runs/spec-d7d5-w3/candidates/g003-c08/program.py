import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Baseline: incidence graph of PG(2, q), used whenever it is the best safe option.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _bipartition(n, adj):
    """Return a 2-colouring of the graph, or None if it is not bipartite."""
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


_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)
_PENALTY = 1000
_KS = (1, 2, 3, 4)


# ----------------------------------------------------------------------------
# Phase 1: bi-Cayley lifts over Z_m x| Z_k2 (kept from the parent, as a seed).
# ----------------------------------------------------------------------------

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
    """Simulated annealing over bi-Cayley lifts with stagnation stop. Returns (n, edges) or None."""
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
# Phase 2 (new, bold): unstructured search on a d-regular bipartite graph.
#
# The graph is no longer forced to have a group symmetry. Reachability is
# held as bit-packed rows (uint64), so one full diameter check on ~1200
# vertices is a few vectorised gathers. We grow the graph by inserting a
# vertex pair, guided by unreached counts, then anneal with degree-preserving
# bipartite 2-switches, targeting pairs at distance > D. Failed attempts are
# discarded, so the best valid graph is always kept.
# ----------------------------------------------------------------------------

def _packed_reach(nbr, D):
    """Bit-packed reach matrix R: bit v of row u is set iff dist(u, v) <= D."""
    n, d = nbr.shape
    W = (n + 63) // 64
    R = np.zeros((n, W), dtype=np.uint64)
    idx = np.arange(n)
    R[idx, idx // 64] = np.left_shift(np.uint64(1), (idx % 64).astype(np.uint64))
    for _ in range(D):
        R2 = R | np.bitwise_or.reduce(R[nbr], axis=1)
        if np.array_equal(R2, R):
            break
        R = R2
    return R


def _bad_and_unr(R, n):
    """Return (ordered bad pairs, per-vertex unreached counts) from a packed reach matrix."""
    rowcnt = _POP8[R.view(np.uint8)].sum(axis=1)
    return n * n - int(rowcnt.sum()), n - rowcnt


def _as_regular(n, edges, d):
    """Return (nbr, color) if the graph is d-regular and bipartite, else None."""
    adj = lib.adjacency(n, edges)
    if any(len(a) != d for a in adj):
        return None
    color = _bipartition(n, adj)
    if color is None:
        return None
    return np.array(adj, dtype=np.int64), color


def _to_edges(nbr, color):
    """Convert a bipartite neighbour array into (n, edges)."""
    n = nbr.shape[0]
    edges = []
    for a in range(n):
        if color[a] == 0:
            for b in nbr[a]:
                edges.append((a, int(b)))
    return n, edges


def _insert(nbr, color, d, rng, unr):
    """Insert a B-vertex w and an A-vertex wp via an unreached-guided d-matching of A-B edges."""
    n = nbr.shape[0]
    cand = []
    for a in range(n):
        if color[a] != 0:
            continue
        ua = float(unr[a])
        for j in range(d):
            b = int(nbr[a, j])
            cand.append((ua + 0.5 * float(unr[b]) + rng.random(), a, b))
    cand.sort(reverse=True)
    usedA, usedB, match = set(), set(), []
    for _, a, b in cand:
        if a in usedA or b in usedB:
            continue
        match.append((a, b))
        usedA.add(a)
        usedB.add(b)
        if len(match) == d:
            break
    if len(match) < d:
        return None
    w, wp = n, n + 1
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


def _anneal(nbr, color, d, D, rng, iters, deadline):
    """Anneal degree-preserving bipartite 2-switches to remove pairs at distance > D."""
    cur = nbr.copy()
    n = cur.shape[0]
    col = np.array(color)
    A = np.flatnonzero(col == 0)
    cur_bad, unr = _bad_and_unr(_packed_reach(cur, D), n)
    T = 2.0
    for _ in range(iters):
        if cur_bad == 0 or time.monotonic() > deadline:
            break
        if rng.random() < 0.5:
            hot = np.flatnonzero((unr > 0) & (col == 0))
            if hot.size:
                a1 = int(hot[rng.randrange(hot.size)])
            else:
                a1 = int(A[rng.randrange(A.size)])
        else:
            a1 = int(A[rng.randrange(A.size)])
        a2 = int(A[rng.randrange(A.size)])
        if a1 == a2:
            continue
        j1 = rng.randrange(d)
        j2 = rng.randrange(d)
        b1 = int(cur[a1, j1])
        b2 = int(cur[a2, j2])
        if b1 == b2 or np.any(cur[a1] == b2) or np.any(cur[a2] == b1):
            continue
        cand = cur.copy()
        cand[a1, j1] = b2
        cand[a2, j2] = b1
        cand[b1, int(np.flatnonzero(cand[b1] == a1)[0])] = a2
        cand[b2, int(np.flatnonzero(cand[b2] == a2)[0])] = a1
        c, unr2 = _bad_and_unr(_packed_reach(cand, D), n)
        if c <= cur_bad or rng.random() < math.exp(-(c - cur_bad) / T):
            cur, cur_bad, unr = cand, c, unr2
    return cur, cur_bad


def _grow(nbr, color, d, D, rng, deadline):
    """Repeatedly insert a vertex pair and anneal; keep only valid results. Returns (nbr, color) or None."""
    cur, col = nbr, list(color)
    best = None
    fails = 0
    while time.monotonic() < deadline and fails < 6:
        n = cur.shape[0]
        _, unr = _bad_and_unr(_packed_reach(cur, D), n)
        ins = _insert(cur, col, d, rng, unr)
        if ins is None:
            break
        new, ncol = ins
        sol, bad = _anneal(new, ncol, d, D, rng, 300, deadline)
        if bad == 0:
            cur, col = sol, ncol
            best = (cur, col)
            fails = 0
        else:
            fails += 1
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    tl = float(time_limit)
    search_deadline = start + max(0.3, min(0.3 * tl, tl - 12.0))
    final_deadline = start + max(0.5, tl - 6.0)
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if d < 3 or D < 3:
        return best

    try:
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
    except Exception:
        pass

    # Phase 2: unstructured growth and annealing from the best regular graph.
    try:
        if time.monotonic() < final_deadline - 1.0:
            reg = _as_regular(best[0], best[1], d)
            if reg is not None:
                nbr, col = reg
                res = _grow(nbr, col, d, D, rng, final_deadline - 1.0)
                if res is not None:
                    n2, e2 = _to_edges(res[0], res[1])
                    consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
