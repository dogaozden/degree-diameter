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
# Exact symplectic spread of W(q) built from F_{q^2}^2.
#
# Let Q = q^2 and view F_Q^2 as a 4-dimensional F_q-space. The form
#   f(v, w) = Tr_{F_Q/F_q}(delta * (v0 w1 - v1 w0))
# is F_q-bilinear, alternating and nondegenerate, so the points of PG(3, q) with
# the totally isotropic lines of f form W(q). For any v, the F_Q-line {lambda v}
# is a totally isotropic 2-dim F_q-subspace, and these q^2+1 subspaces partition
# the points: they are an exact spread.
# ----------------------------------------------------------------------------

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

    # Points: F_q-orbits of nonzero vectors (a, b) of F_Q^2, indexed by a*Q+b.
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

    # Lines are the totally isotropic 2-dim subspaces; enumerate each once.
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

    # Spread: the F_Q-lines {lambda * v}, v in PG(1, Q).
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


# ----------------------------------------------------------------------------
# Twin blow-up with a distance-2-free vertex set.
# ----------------------------------------------------------------------------

def _independent_set(N, nb, rng, nprng, deadline):
    """Iterated local search for a large set of vertices with no conflicting pair."""
    nbn = [np.asarray(x, dtype=np.int64) for x in nb]
    cnt = np.zeros(N, dtype=np.int64)     # number of chosen conflict-neighbours
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
        score = cnt + nprng.random(N)     # random tie-breaking
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
# NEW: slack augmentation by vertex insertion.
#
# After blow-up, some vertices have degree below d ("slack"). Add a new vertex w
# on side S whose neighbourhood N is a set of slack vertices on the other side.
# A vertex x is within distance D of w iff some b in N has dist(b, x) <= D-1.
# So w is admissible iff the radius-(D-1) balls of N cover the whole graph.
# Adding a vertex never creates a pair farther than D, so the diameter and
# bipartiteness are preserved. Balls are bitmasks, and the cover is found by
# randomised greedy set cover. Each insertion grows n by one.
# ----------------------------------------------------------------------------

def _ball_masks(n, adj, R):
    """Bitmask per vertex of all vertices within distance R."""
    reach = [1 << v for v in range(n)]
    for _ in range(R):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return reach


def _cover(cands, reach, full, d, rng):
    """Pick at most d candidates whose balls cover `full`; None if the greedy fails."""
    for attempt in range(4):
        uncovered = full
        chosen = []
        pool = list(cands)
        while uncovered and len(chosen) < d and pool:
            best_gain = 0
            best_list = []
            for c in pool:
                g = (reach[c] & uncovered).bit_count()
                if g > best_gain:
                    best_gain = g
                    best_list = [c]
                elif g == best_gain and g > 0:
                    best_list.append(c)
            if best_gain == 0:
                break
            c = best_list[rng.randrange(len(best_list))]
            chosen.append(c)
            uncovered &= ~reach[c]
            pool.remove(c)
        if uncovered == 0:
            return chosen
    return None


def _augment(n, edges, d, D, deadline, rng):
    """Greedily add vertices whose neighbourhoods are slack vertices covering all within D-1."""
    R = D - 1
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _two_colour(n, edges)
    reach = None
    fails = 0
    while time.monotonic() < deadline and fails < 60:
        if reach is None:
            reach = _ball_masks(n, adj, R)
        full = (1 << n) - 1
        sides = [0, 1]
        rng.shuffle(sides)
        placed = False
        for side in sides:
            cands = [v for v in range(n) if color[v] != side and len(adj[v]) < d]
            if not cands:
                continue
            N = _cover(cands, reach, full, d, rng)
            if N is None:
                continue
            w = n
            n += 1
            adj.append(set())
            color.append(side)
            for b in N:
                adj[b].add(w)
                adj[w].add(b)
            placed = True
            break
        if placed:
            reach = None
            fails = 0
        else:
            fails += 1
    out = []
    for u in range(n):
        for v in adj[u]:
            if u < v:
                out.append((u, v))
    return n, out


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, 0.85 * time_limit - 3.0)
    deadline = start + budget
    search_deadline = start + 0.5 * budget   # leave the rest for augmentation
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
        done = False
        if D >= 4:
            try:
                geo = _symplectic_quadrangle(q)
                if geo is not None:
                    npts, lines, spread = geo
                    n0 = npts + len(lines)
                    edges0 = [(p, npts + j) for j, L in enumerate(lines) for p in L]
                    consider(n0, edges0)
                    O = _ovoid_search(npts, lines, rng, nprng, search_deadline)
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
                res = _blowup(n0, e0, d, search_deadline, rng, nprng)
                if res is not None:
                    consider(res[0], res[1])

    # Slack augmentation on the best graph found so far.
    if D >= 2 and best_n >= 2 and time.monotonic() < deadline:
        try:
            n2, e2 = _augment(best[0], best[1], d, D, deadline, rng)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
