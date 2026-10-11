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
# Exact symplectic spread of W(q) built from F_{q^2}^2, together with the
# cyclic group diag(mu, mu^-1) acting on the points (it preserves the form).
#
# Let Q = q^2 and view F_Q^2 as a 4-dimensional F_q-space. The form
#   f(v, w) = Tr_{F_Q/F_q}(delta * (v0 w1 - v1 w0))
# is F_q-bilinear, alternating and nondegenerate, so the points of PG(3, q) with
# the totally isotropic lines of f form W(q). For any v, the F_Q-line {lambda v}
# is a totally isotropic 2-dim F_q-subspace, and these q^2+1 subspaces partition
# the points: they are an exact spread.
# ----------------------------------------------------------------------------

def _symplectic_quadrangle(q):
    """Return (npts, lines, spread, perms) for W(q) built from F_{q^2}^2, or None.

    lines are sorted lists of point ids; spread is a list of q^2+1 line ids that
    pairwise share no point; perms is a list of point permutations (automorphisms
    of W(q)) generating a cyclic group that acts on the points.
    """
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

    # Automorphisms: (a, b) -> (mu a, mu^-1 b) preserves det, hence the form.
    # Use a primitive mu of F_Q^* to get a cyclic group acting on points.
    g = F.primitive_element()
    gi = F.inv(g)
    perm = [pid[mul(g, reps[p][0]) * Q + mul(gi, reps[p][1])] for p in range(npts)]
    if sorted(perm) != list(range(npts)):
        return None
    return npts, lines, spread, [perm]


# ----------------------------------------------------------------------------
# Twin blow-up with a distance-2-free vertex set.
#
# If every vertex of a base graph G has degree d-1, blow up some vertices v into
# two twin copies with the same neighbourhood. A copy of u then has degree
# sum_{v in N(u)} m_v, so every vertex may have at most one blown-up neighbour.
# For W(q) that means: blown points form a partial ovoid (no two collinear), and
# blown lines form a partial spread (no two meeting). The two sides do not
# constrain each other.
# ----------------------------------------------------------------------------

def _collinear_sets(npts, lines):
    """nb[p] = set of points collinear with p (p itself excluded)."""
    nb = [set() for _ in range(npts)]
    for L in lines:
        for p in L:
            nb[p].update(L)
    for p in range(npts):
        nb[p].discard(p)
    return nb


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


def _extend(O, nb, npts):
    """Greedily grow an independent point set O to a maximal one."""
    out = list(O)
    chosen = set(out)
    blocked = set()
    for p in out:
        blocked |= nb[p]
    for p in range(npts):
        if p in chosen or p in blocked:
            continue
        out.append(p)
        chosen.add(p)
        blocked |= nb[p]
    return out


def _best_union(m, ok, cadj, weight, node_limit=300000):
    """Exact (node-limited) maximum-weight independent set of orbits."""
    best = [0, []]
    nodes = [0]
    chosen = []

    def rec(cands, cur):
        nodes[0] += 1
        if cur > best[0]:
            best[0] = cur
            best[1] = list(chosen)
        if not cands or nodes[0] > node_limit:
            return
        tot = 0
        c = cands
        while c:
            low = c & -c
            tot += weight[low.bit_length() - 1]
            c ^= low
        if cur + tot <= best[0]:
            return
        low = cands & -cands
        v = low.bit_length() - 1
        chosen.append(v)
        rec(cands & ~cadj[v] & ~low, cur + weight[v])
        chosen.pop()
        rec(cands & ~low, cur)

    rec(sum(1 << i for i in range(m) if ok[i]), 0)
    return best[1]


def _orbit_ovoid(npts, lines, perms):
    """Partial ovoid that is a union of orbits of the automorphism group, then extended."""
    nb = _collinear_sets(npts, lines)
    orb_of = [-1] * npts
    orbits = []
    for p in range(npts):
        if orb_of[p] >= 0:
            continue
        k = len(orbits)
        orb = [p]
        orb_of[p] = k
        i = 0
        while i < len(orb):
            x = orb[i]
            i += 1
            for g in perms:
                y = g[x]
                if orb_of[y] < 0:
                    orb_of[y] = k
                    orb.append(y)
        orbits.append(orb)
    m = len(orbits)
    sets = [set(o) for o in orbits]
    # An orbit is usable only if its own points are pairwise non-collinear.
    ok = [not any(nb[p] & sets[i] for p in orbits[i]) for i in range(m)]
    cadj = [0] * m
    for i in range(m):
        for j in range(i + 1, m):
            if any(nb[p] & sets[j] for p in orbits[i]):
                cadj[i] |= 1 << j
                cadj[j] |= 1 << i
    weight = [len(o) for o in orbits]
    best = _best_union(m, ok, cadj, weight)
    O = [p for i in best for p in orbits[i]]
    return _extend(O, nb, npts)


def _ovoid_search(npts, lines, rng, nprng, deadline):
    """Large partial ovoid of the points: pairwise non-collinear point set."""
    nb = _collinear_sets(npts, lines)
    nbl = [sorted(s) for s in nb]
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

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.85 * time_limit - 3.0)
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
                    npts, lines, spread, perms = geo
                    n0 = npts + len(lines)
                    edges0 = [(p, npts + j) for j, L in enumerate(lines) for p in L]
                    consider(n0, edges0)
                    # Points side: best of a symmetry-reduced search and local search.
                    O_orb = _orbit_ovoid(npts, lines, perms)
                    O_loc = _ovoid_search(npts, lines, rng, nprng, deadline)
                    O = O_loc if len(O_loc) > len(O_orb) else O_orb
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
