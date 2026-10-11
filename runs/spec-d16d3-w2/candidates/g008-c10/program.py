import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Weighted twin blow-up (new construction idea).
#
# Replace each base vertex v by k[v] "twins": copies with identical neighbourhoods.
# Twins of v are not adjacent, so they sit at distance 2 from each other, and
# twins of u and v are adjacent iff u ~ v in the base. Distances between classes
# are unchanged, and bipartiteness is kept. The blow-up is valid for max degree d
# iff for every base vertex u:  sum_{w ~ u} k[w] <= d.
#
# Weights k = 2 on a set T of points/lines of PG(2,q) recover the parent's
# arc-extension, but the search can use any weights. Simulated annealing over
# the weight vector maximises sum(k) under those load constraints.
# ----------------------------------------------------------------------------

def _adjacency(n, edges):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _blow_up(n0, edges, k):
    """Replace base vertex v by k[v] twins; join twin classes along base edges."""
    start = [0] * (n0 + 1)
    for v in range(n0):
        start[v + 1] = start[v] + k[v]
    E = []
    for u, v in edges:
        su, sv = start[u], start[v]
        for i in range(k[u]):
            a = su + i
            for j in range(k[v]):
                E.append((a, sv + j))
    return start[n0], E


def _weight_anneal(n0, adj, d, deadline, rng):
    """Anneal vertex weights k >= 1 maximising sum(k) s.t. load(u) = sum_{w~u} k[w] <= d.

    Penalised objective: sum(k) - lam * sum_u max(0, load(u) - d). Returns the best
    feasible weight vector seen.
    """
    k = [1] * n0
    load = [len(adj[u]) for u in range(n0)]
    if any(x > d for x in load):
        return k
    # Greedy feasible fill in random order.
    order = list(range(n0))
    rng.shuffle(order)
    for v in order:
        if k[v] < d and all(load[u] < d for u in adj[v]):
            k[v] += 1
            for u in adj[v]:
                load[u] += 1
    total = sum(k)
    viol = 0
    best_k, best_total = list(k), total

    lam = 0.6
    t0, t1 = 0.5, 0.03
    t_begin = time.monotonic()
    span = max(1e-3, deadline - t_begin)
    T = t0
    it = 0
    exp = math.exp
    while True:
        it += 1
        if not (it & 255):
            now = time.monotonic()
            if now >= deadline:
                break
            T = t0 * (t1 / t0) ** min(1.0, (now - t_begin) / span)
        v = rng.randrange(n0)
        kv = k[v]
        if kv == 1:
            delta = 1
        elif kv >= d:
            delta = -1
        else:
            delta = 1 if rng.random() < 0.6 else -1
        dv = 0
        for u in adj[v]:
            x = load[u]
            y = x + delta
            dv += (y - d if y > d else 0) - (x - d if x > d else 0)
        dobj = delta - lam * dv
        if dobj >= 0 or rng.random() < exp(dobj / T):
            k[v] = kv + delta
            for u in adj[v]:
                load[u] += delta
            viol += dv
            total += delta
            if viol == 0 and total > best_total:
                best_total = total
                best_k = list(k)
    return best_k


# ----------------------------------------------------------------------------
# Base graphs
# ----------------------------------------------------------------------------

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


def _bases(d, D):
    """Base graphs (n0, edges) whose weighted twin blow-ups are searched."""
    if d == 2:
        m = 2 * D
        return [(m, [(i, (i + 1) % m) for i in range(m)])]
    out = []
    if D == 3:
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
        for q in qs[:2]:
            out.append(lib.projective_plane_incidence(q))
    elif D >= 4:
        qs = [q for q in range(min(d - 1, 9), 1, -1) if lib.is_prime_power(q)]
        if qs:
            out.append(_gq_w(qs[0]))
    return out


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    budget = min(0.7 * float(time_limit), 40.0)
    deadline = t_start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    rng = random.Random(seed * 1000003 + 17 * d + D)

    # Safe fallback: K_{d,d} has diameter 2 and degree d.
    best_n, best_E = lib.haar_graph(d, range(d))
    if not lib.is_valid(best_n, best_E, d, D):
        return 1, []

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, list(E)

    bases = _bases(d, D)
    nb = len(bases)
    for idx, (n0, E0) in enumerate(bases):
        now = time.monotonic()
        if now >= deadline:
            break
        remaining = deadline - now
        if nb == 1:
            slice_ = remaining
        elif idx == 0:
            slice_ = 0.75 * remaining
        else:
            slice_ = remaining
        consider(n0, E0)  # the untouched base itself
        adj = _adjacency(n0, E0)
        k = _weight_anneal(n0, adj, d, now + slice_, rng)
        n, E = _blow_up(n0, E0, k)
        consider(n, E)

    return best_n, list(best_E)
