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


# ----------------------------------------------------------------------------
# D = 3: Araujo-Pardo--Lopez base graphs plus a greedy pair-extension (unchanged).
# ----------------------------------------------------------------------------

def _adjacency(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _sides(n, adj):
    """Two-colour a bipartite graph (sides 0/1). Unreached vertices default to 0."""
    side = [-1] * n
    for s in range(n):
        if side[s] != -1:
            continue
        side[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if side[v] == -1:
                    side[v] = 1 - side[u]
                    stack.append(v)
    return [x if x != -1 else 0 for x in side]


def _cover(cands, need, adj, d, budget, rng):
    """Greedy set cover: choose <= budget candidates with spare degree whose neighbourhoods cover need."""
    uncovered = set(need)
    pool = [c for c in cands if len(adj[c]) < d]
    rng.shuffle(pool)
    chosen = []
    while uncovered:
        if len(chosen) >= budget:
            return None
        best, best_gain = None, 0
        for c in pool:
            g = len(adj[c] & uncovered)
            if g > best_gain:
                best, best_gain = c, g
        if best is None:
            return None
        chosen.append(best)
        pool.remove(best)
        uncovered -= adj[best]
    return chosen


def _extend(n, edges, d, D, rng, deadline):
    """Repeatedly add a new A-B vertex pair while the result stays valid. Requires D == 3."""
    edges = list(edges)
    fails = 0
    while time.monotonic() < deadline and fails < 40:
        adj = _adjacency(n, edges)
        side = _sides(n, adj)
        A = [x for x in range(n) if side[x] == 0]
        B = [x for x in range(n) if side[x] == 1]
        S = _cover(B, A, adj, d, d - 1, rng)
        T = _cover(A, B, adj, d, d - 1, rng)
        if S is None or T is None:
            fails += 1
            continue
        u, v = n, n + 1
        new_edges = edges + [(u, s) for s in S] + [(v, t) for t in T] + [(u, v)]
        if lib.is_valid(n + 2, new_edges, d, D):
            n, edges = n + 2, new_edges
            fails = 0
        else:
            fails += 1
    return n, edges


def _d3_bases(d):
    """Strong D = 3 bases: PG(2,q) with q+1 <= d, and the Araujo-Pardo--Lopez graph with q+2 <= d."""
    out = []
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            out.append(lib.projective_plane_incidence(q))
            break
    for q in range(d - 2, 2, -1):
        if lib.is_prime_power(q):
            try:
                out.append(lib.araujo_lopez_graph(q))
            except Exception:
                pass
            break
    return out


# ----------------------------------------------------------------------------
# New approach for D >= 4 (and as an extra attempt for D = 3):
# bi-Cayley voltage lifts over semidirect products Z_m x| Z_k2, searched by
# simulated annealing with a vectorized (numpy) reachability cost.
#
# Vertices: A_i,g = i*G + g and B_j,h = (k+j)*G + h, with G = |group|.
# Layer l is a perfect matching: A_i,g -- B_{perm_l[i]}, g * s_{l,i}.
# Degree d is the number of layers. Left multiplication by any element is an
# automorphism, so the diameter is <= D iff every representative (A_i,e and
# B_j,e) reaches all vertices within D steps. The cost counts unreached pairs
# plus a heavy penalty for duplicate darts.
# ----------------------------------------------------------------------------

class _Group:
    """Z_m x| Z_k2, element (a, b) coded as a*k2 + b, with (a,b)(c,d) = (a + r^b c, b + d)."""

    def __init__(self, m, k2, r):
        self.m = m
        self.k2 = k2
        self.order = m * k2
        self.pw = np.array([pow(r, b, m) for b in range(k2)], dtype=np.int64)
        X = np.arange(self.order, dtype=np.int64)
        self.ea = X // k2
        self.eb = X % k2

    def rperm(self, s):
        """Array g -> g * s over all group elements g."""
        c, dd = divmod(s, self.k2)
        return ((self.ea + self.pw[self.eb] * c) % self.m) * self.k2 + (self.eb + dd) % self.k2

    def inv(self, s):
        """Inverse of element s."""
        a, b = divmod(s, self.k2)
        nb = (-b) % self.k2
        return ((-int(self.pw[nb]) * a) % self.m) * self.k2 + nb


def _random_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G (r = 1 gives an abelian group)."""
    opts = [k2 for k2 in range(1, 13) if G % k2 == 0 and G // k2 >= 2]
    if not opts:
        return None
    k2 = rng.choice(opts)
    m = G // k2
    if k2 == 1 or rng.random() < 0.25:
        r = 1
    else:
        cands = [x for x in range(2, m) if math.gcd(x, m) == 1 and pow(x, k2, m) == 1 % m]
        r = rng.choice(cands) if cands else 1
    return _Group(m, k2, r)


def _build_adj(grp, k, perms, volts, d):
    """Adjacency matrix (N x d): column l is the perfect matching of layer l."""
    G = grp.order
    N = 2 * k * G
    adj = np.zeros((N, d), dtype=np.int64)
    for l in range(d):
        perm = perms[l]
        vol = volts[l]
        inv_perm = [0] * k
        for i, j in enumerate(perm):
            inv_perm[j] = i
        for i in range(k):
            adj[i * G:(i + 1) * G, l] = (k + perm[i]) * G + grp.rperm(vol[i])
        for j in range(k):
            i = inv_perm[j]
            adj[(k + j) * G:(k + j + 1) * G, l] = i * G + grp.rperm(grp.inv(vol[i]))
    return adj


def _reach_cost(adj, k, G, D):
    """Number of (representative, vertex) pairs not reached within D steps. Zero means diameter <= D."""
    N, d = adj.shape
    R = np.zeros((2 * k, N), dtype=bool)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    R[np.arange(2 * k), reps] = True
    for _ in range(D):
        NR = R.copy()
        for l in range(d):
            NR |= R[:, adj[:, l]]
        if np.array_equal(NR, R):
            break
        R = NR
    return 2 * k * N - int(R.sum())


def _dup_count(perms, volts, d, k):
    """Number of repeated darts (i, j, s); each would create a duplicate edge."""
    seen = set()
    dups = 0
    for l in range(d):
        for i in range(k):
            key = (i, perms[l][i], volts[l][i])
            if key in seen:
                dups += 1
            else:
                seen.add(key)
    return dups


def _anneal(d, D, k, grp, rng, deadline):
    """Simulated annealing over voltages and layer permutations. Returns adjacency on success, else None."""
    G = grp.order
    perms = []
    volts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        perms.append(p)
        volts.append([rng.randrange(G) for _ in range(k)])

    adj = _build_adj(grp, k, perms, volts, d)
    cost = _reach_cost(adj, k, G, D) + 1000 * _dup_count(perms, volts, d, k)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = 1.5 * (1.0 - (now - t0) / span) + 0.05
        l = rng.randrange(d)
        i = rng.randrange(k)
        i2 = i
        kind = 'v'
        old_v = volts[l][i]
        if k == 1 or rng.random() < 0.6:
            volts[l][i] = rng.randrange(G)
        else:
            i2 = rng.randrange(k)
            if i2 == i:
                continue
            kind = 'p'
            perms[l][i], perms[l][i2] = perms[l][i2], perms[l][i]

        new_adj = _build_adj(grp, k, perms, volts, d)
        new_cost = _reach_cost(new_adj, k, G, D) + 1000 * _dup_count(perms, volts, d, k)
        delta = new_cost - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new_cost
            adj = new_adj
        else:
            if kind == 'v':
                volts[l][i] = old_v
            else:
                perms[l][i], perms[l][i2] = perms[l][i2], perms[l][i]

    return adj if cost == 0 else None


def _edges_from(adj, k, G, d):
    """Edge list of the lift: A-side indices 0..kG-1 joined to B-side column entries."""
    n_a = k * G
    E = []
    for l in range(d):
        E.extend(zip(range(n_a), adj[:n_a, l].tolist()))
    return 2 * k * G, E


def _lift_search(d, D, best_n, rng, deadline, consider):
    """Repeatedly anneal lifts of random sizes near the current best; feed valid results to consider."""
    if d < 3:
        return
    cur = best_n
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 0.8:
            break
        k = rng.choice([1, 1, 2, 2, 3, 4])
        half = max(2, cur // (2 * k))
        G = half + rng.randrange(0, max(2, half // 10) + 1)
        grp = _random_group(G, rng)
        if grp is None:
            continue
        chunk = min(remaining, max(1.0, min(5.0, remaining / 3)))
        adj = _anneal(d, D, k, grp, rng, time.monotonic() + chunk)
        if adj is not None:
            n, e = _edges_from(adj, k, grp.order, d)
            if consider(n, e):
                cur = max(cur, n)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.75 * time_limit, time_limit - 5.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = list(lib.haar_graph(d, range(d)))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = [n, e]
            return True
        return False

    if D == 3:
        bases = _d3_bases(d)
        for bn, be in bases:
            consider(bn, be)
        ext_end = start + 0.35 * (deadline - start)
        for idx, (bn, be) in enumerate(bases):
            now = time.monotonic()
            share = max(0.0, ext_end - now) / (len(bases) - idx)
            n2, e2 = _extend(bn, be, d, D, rng, now + share)
            consider(n2, e2)
    else:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if D >= 4 and time.monotonic() < deadline:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])

    # Main search: annealed bi-Cayley lifts over semidirect products.
    _lift_search(d, D, best[0], rng, deadline, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best[0], best[1]
