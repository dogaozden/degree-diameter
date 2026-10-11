import itertools
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q): points and lines as explicit lists.
# ----------------------------------------------------------------------------

NOISE = 0.2
MAX_FAILS = 3000


def _gq_w(q):
    """Return (P, lines): points of W(q) indexed 0..P-1, and each totally isotropic line as a sorted point list."""
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


def _structures(P, lines):
    """Point->lines lists, collinearity sets on points, and line-meeting sets on lines."""
    L = len(lines)
    pl = [[] for _ in range(P)]
    for j, Ls in enumerate(lines):
        for p in Ls:
            pl[p].append(j)
    padj = [set() for _ in range(P)]
    for Ls in lines:
        for p in Ls:
            padj[p].update(r for r in Ls if r != p)
    ladj = [set() for _ in range(L)]
    for p in range(P):
        for a in pl[p]:
            ladj[a].update(b for b in pl[p] if b != a)
    return pl, padj, ladj


# ----------------------------------------------------------------------------
# Maximum independent set by iterated local search with tabu (numpy-based).
# Used to find a partial ovoid (points) and a partial spread (lines).
# ----------------------------------------------------------------------------

def _mis(n, nbr_sets, deadline, rng, nprng, target):
    if n == 0:
        return []
    nbr = [np.array(sorted(s), dtype=np.int64) for s in nbr_sets]
    inS = np.zeros(n, dtype=bool)
    cnt = np.zeros(n, dtype=np.int64)
    tabu = np.zeros(n, dtype=np.int64)
    size = 0
    best = []
    best_size = 0
    it = 0
    while True:
        it += 1
        if (it & 31) == 0 and time.monotonic() >= deadline:
            break
        if best_size >= target:
            break
        free = np.flatnonzero(~inS & (cnt == 0))
        if free.size:
            v = int(free[nprng.integers(free.size)])
            inS[v] = True
            cnt[nbr[v]] += 1
            size += 1
            if size > best_size:
                best_size = size
                best = np.flatnonzero(inS).tolist()
            continue
        cand = np.flatnonzero(~inS & (cnt == 1) & (tabu <= it))
        if cand.size and nprng.random() < 0.95:
            # (1,1)-swap: bring in v, drop its unique chosen neighbour.
            v = int(cand[nprng.integers(cand.size)])
            nb = nbr[v]
            u = int(nb[inS[nb]][0])
            inS[u] = False
            cnt[nbr[u]] -= 1
            tabu[u] = it + 7 + rng.randrange(10)
            inS[v] = True
            cnt[nbr[v]] += 1
        else:
            # Perturbation: force in a random vertex, dropping its chosen neighbours.
            pool = np.flatnonzero(~inS & (tabu <= it))
            if pool.size == 0:
                pool = np.flatnonzero(~inS)
            if pool.size == 0:
                break
            v = int(pool[nprng.integers(pool.size)])
            nb = nbr[v]
            for u in nb[inS[nb]].tolist():
                inS[u] = False
                cnt[nbr[u]] -= 1
                size -= 1
                tabu[u] = it + 7 + rng.randrange(10)
            inS[v] = True
            cnt[nbr[v]] += 1
            size += 1
    return best


# ----------------------------------------------------------------------------
# Twin blow-up: twins of an ovoid-like point set I and a spread-like line set J.
# Degrees stay <= q+2 because I is pairwise non-collinear and J pairwise disjoint.
# ----------------------------------------------------------------------------

def _twin(P, L, pl, lines, I, J, base_edges):
    edges = list(base_edges)
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
# Greedy extension for diameter 4.
#
# A new vertex x joined to a set S (spare vertices on the opposite side) keeps
# diameter <= 4 when the union of R3(s), s in S, covers every vertex. Adding x
# never lengthens an existing distance, so the check is local to x.
# ----------------------------------------------------------------------------

def _two_colour(n, adj):
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
    return color


def _ball3(n, adj):
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


def _cover(pool, reach, full, d, rng):
    """Randomised greedy set cover of all vertices by R3 balls of at most d pool vertices."""
    unc = full
    S = []
    avail = list(pool)
    rng.shuffle(avail)
    while unc and len(S) < d and avail:
        if rng.random() < NOISE:
            useful = [v for v in avail if reach[v] & unc]
            if not useful:
                return None
            v = rng.choice(useful)
        else:
            bg, bv = 0, -1
            for v in avail:
                g = (reach[v] & unc).bit_count()
                if g > bg:
                    bg, bv = g, v
            if bv < 0:
                return None
            v = bv
        S.append(v)
        unc &= ~reach[v]
        avail.remove(v)
    return S if not unc else None


def _extend(n, edges, d, deadline, rng):
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _two_colour(n, adj)
    fails = 0
    while time.monotonic() < deadline and fails < MAX_FAILS:
        reach = _ball3(n, adj)
        full = (1 << n) - 1
        spare = [[], []]
        for v in range(n):
            if len(adj[v]) < d:
                spare[color[v]].append(v)
        cols = [c for c in (0, 1) if spare[c]]
        if not cols:
            break
        added = False
        while time.monotonic() < deadline and fails < MAX_FAILS:
            c = rng.choice(cols)
            S = _cover(spare[c], reach, full, d, rng)
            if S is None:
                fails += 1
                continue
            x = n
            n += 1
            for s in S:
                edges.append((s, x))
                adj[s].append(x)
            adj.append(list(S))
            color.append(1 - c)
            fails = 0
            added = True
            break
        if not added:
            break
    return n, edges


# ----------------------------------------------------------------------------

def _moore(d, D):
    return 2 * sum((d - 1) ** i for i in range(D))


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = random.Random(seed)
    nprng = np.random.default_rng(abs(int(seed)) % (2 ** 32))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
            return True
        return False

    def at_bound():
        return d >= 3 and best[0] >= _moore(d, D)

    # Projective plane incidence graph: degree d, diameter 3.
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass
    if at_bound():
        return best

    # Generalized quadrangle W(q), q = d-2: base of degree d-1, blown up by twins.
    q = d - 2
    if D >= 4 and 2 <= q <= 11 and lib.is_prime_power(q) and not at_bound():
        try:
            P, lines = _gq_w(q)
            L = len(lines)
            pl, padj, ladj = _structures(P, lines)
            base_edges = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
            consider(P + L, base_edges)

            # Spread (lines) first, then ovoid (points); the rest goes to extension.
            now = time.monotonic()
            rem = max(0.0, deadline - now)
            J = _mis(L, ladj, now + 0.35 * rem, rng, nprng, q * q + 1)
            now = time.monotonic()
            rem = max(0.0, deadline - now)
            I = _mis(P, padj, now + 0.30 * rem, rng, nprng, q * q + 1)

            n, edges = _twin(P, L, pl, lines, I, J, base_edges)
            if consider(n, edges) and D == 4:
                n2, e2 = _extend(n, edges, d, deadline, rng)
                consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
