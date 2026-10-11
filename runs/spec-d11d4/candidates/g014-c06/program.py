import itertools
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q): points, and totally isotropic lines as point lists.
# ----------------------------------------------------------------------------

def _gq_lines(q):
    """Return (P, lines): P points of W(q) indexed 0..P-1, and each line as a sorted point list."""
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
            # Symplectic form x0*y1 - x1*y0 + x2*y3 - x3*y2 must vanish.
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
    return P, lines


def _gq_incidence(q):
    """Incidence graph of W(q): (n, edges), degree q+1, diameter 4."""
    P, lines = _gq_lines(q)
    return P + len(lines), [(p, P + j) for j, L in enumerate(lines) for p in L]


def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _conflicts(P, lines):
    """Point collinearity graph and line concurrency graph of a GQ given by its lines."""
    pl = [[] for _ in range(P)]
    for j, L in enumerate(lines):
        for p in L:
            pl[p].append(j)
    pc = [set() for _ in range(P)]
    for L in lines:
        for p in L:
            pc[p].update(L)
    for p in range(P):
        pc[p].discard(p)
    lc = [set() for _ in range(len(lines))]
    for p in range(P):
        ls = pl[p]
        for a in ls:
            lc[a].update(ls)
    for j in range(len(lines)):
        lc[j].discard(j)
    return [sorted(s) for s in pc], [sorted(s) for s in lc]


# ----------------------------------------------------------------------------
# Iterated local search for a large set with no conflicting pair.
# ----------------------------------------------------------------------------

def _mis(N, nb, rng, nprng, deadline):
    """Return a large independent set of the conflict graph (N vertices, neighbour lists nb)."""
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


# ----------------------------------------------------------------------------
# Twin blow-up: copies of a vertex share its neighbourhood. Doubling a set D is
# valid when every vertex has at most one neighbour in D (for a degree-(d-1)
# base). In W(q) that means: doubled points pairwise non-collinear (partial
# ovoid), doubled lines pairwise non-concurrent (partial spread), independently.
# ----------------------------------------------------------------------------

def _blow(n0, edges0, S):
    """Blow up each vertex of S into two twin copies with the same neighbourhood."""
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


# ----------------------------------------------------------------------------
# Greedy set-cover vertex extension for diameter 4.
# A new vertex x joined to S (spare-degree vertices on one side) keeps diameter
# <= 4 iff the union of radius-3 balls of S covers every vertex.
# ----------------------------------------------------------------------------

def _ball3(n, adj):
    """Per-vertex bitmasks of all vertices within distance 3."""
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

    fails = 0
    while time.monotonic() < deadline and fails < 3000:
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        grown = False
        while time.monotonic() < deadline and fails < 3000:
            spare = [v for v in range(n) if len(adj[v]) < d]
            if not spare:
                return n, edges
            s0 = rng.choice(spare)
            pool = [v for v in spare if color[v] == color[s0] and v != s0]
            S = [s0]
            unc = full & ~reach[s0]
            while unc and len(S) < d and pool:
                best, bv = 0, -1
                for v in pool:
                    g = (reach[v] & unc).bit_count()
                    if g > best:
                        best, bv = g, v
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

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = random.Random(seed)
    nprng = np.random.default_rng(abs(int(seed)) % (2 ** 32))

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

    if D == 2:
        return best

    # Projective plane incidence (diameter 3, degree d).
    try:
        pg = _pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    except Exception:
        pass

    if D >= 4:
        # W(d-1) incidence: degree d, diameter 4.
        if 2 <= d - 1 <= 11 and lib.is_prime_power(d - 1):
            try:
                consider(*_gq_incidence(d - 1))
            except Exception:
                pass

        # Main pipeline: W(q), q = d-2, degree q+1 = d-1, then twin blow-up
        # (partial ovoid on points + partial spread on lines, searched
        # independently), then greedy extension using the spare degree.
        q = d - 2
        if 2 <= q <= 11 and lib.is_prime_power(q):
            try:
                P, lines = _gq_lines(q)
                n0 = P + len(lines)
                edges0 = [(p, P + j) for j, L in enumerate(lines) for p in L]
                consider(n0, edges0)

                pc, lc = _conflicts(P, lines)
                I = _mis(P, pc, rng, nprng, t0 + 0.55 * budget)
                T = _mis(len(lines), lc, rng, nprng, t0 + 0.70 * budget)
                S = list(I) + [P + j for j in T]
                n1, e1 = _blow(n0, edges0, S)
                consider(n1, e1)

                n2, e2 = _extend(n1, e1, d, deadline, rng)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
