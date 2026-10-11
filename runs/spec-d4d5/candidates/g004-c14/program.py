import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases: every base is d-regular and bipartite, with side A = vertices 0..n/2-1.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4, (q+1)-regular."""
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


# ----------------------------------------------------------------------------
# Growth by pair insertion + 2-switch annealing (the new family).
#
# Adding a pair (a in A, b in B) to a d-regular bipartite graph: remove d edges
# x_i-y_i with distinct x_i and distinct y_i; join a to all y_i and b to all x_i.
# Degrees stay exactly d. Then 2-switches (a1-b1, a2-b2) -> (a1-b2, a2-b1)
# are annealed to drive the number of pairs at distance > D to zero.
# ----------------------------------------------------------------------------

def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance > D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        if new == reach:
            break
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _add_pair(n, adj, A, d, rng):
    """Insert one A-vertex and one B-vertex, keeping all degrees = d. Returns new n, or None."""
    pairs = []
    used_x, used_y = set(), set()
    tries = 0
    while len(pairs) < d and tries < 2000:
        tries += 1
        x = rng.choice(A)
        y = rng.choice(tuple(adj[x]))
        if x in used_x or y in used_y:
            continue
        used_x.add(x)
        used_y.add(y)
        pairs.append((x, y))
    if len(pairs) < d:
        return None
    for x, y in pairs:
        adj[x].discard(y)
        adj[y].discard(x)
    a, b = n, n + 1
    adj.append(set())
    adj.append(set())
    for x, y in pairs:
        adj[a].add(y)
        adj[y].add(a)
        adj[b].add(x)
        adj[x].add(b)
    A.append(a)
    return n + 2


def _anneal(n, adj, A, D, deadline, rng):
    """2-switch annealing until diameter <= D (cost 0) or the deadline. Returns True on success."""
    cost = _bad(n, adj, D)
    if cost == 0:
        return True
    t0 = time.monotonic()
    span = max(deadline - t0, 1e-3)
    while True:
        now = time.monotonic()
        if now >= deadline:
            return False
        frac = (now - t0) / span
        T = 2.0 * (0.025 ** frac)
        a1 = rng.choice(A)
        b1 = rng.choice(tuple(adj[a1]))
        a2 = rng.choice(A)
        b2 = rng.choice(tuple(adj[a2]))
        if a1 == a2 or b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
            continue
        adj[a1].discard(b1); adj[b1].discard(a1)
        adj[a2].discard(b2); adj[b2].discard(a2)
        adj[a1].add(b2); adj[b2].add(a1)
        adj[a2].add(b1); adj[b1].add(a2)
        c2 = _bad(n, adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            if cost == 0:
                return True
        else:
            adj[a1].discard(b2); adj[b2].discard(a1)
            adj[a2].discard(b1); adj[b1].discard(a2)
            adj[a1].add(b1); adj[b1].add(a1)
            adj[a2].add(b2); adj[b2].add(a2)


def _grow(n, adj, A, d, D, deadline, rng):
    """Repeatedly add a pair and anneal; commit only states with diameter <= D."""
    while time.monotonic() < deadline:
        t_adj = [set(s) for s in adj]
        t_A = list(A)
        t_n = _add_pair(n, t_adj, t_A, d, rng)
        if t_n is None:
            continue
        now = time.monotonic()
        budget_end = min(deadline, now + max(3.0, (deadline - now) * 0.3))
        if _anneal(t_n, t_adj, t_A, D, budget_end, rng):
            n, adj, A = t_n, t_adj, t_A
    return n, adj, A


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    deadline = start + max(0.5, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    # Candidate bases: K_{d,d} always; projective plane and GQ when d-1 is a prime power.
    cands = [lib.haar_graph(d, range(d))]
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        if D >= 3 and q <= 13:
            cands.append(lib.projective_plane_incidence(q))
        if D >= 4 and q <= 5:
            cands.append(_gq_w(q))

    best = None
    for n, e in cands:
        if (best is None or n > best[0]) and lib.is_valid(n, e, d, D):
            best = (n, e)
    if best is None:
        return 2, [(0, 1)]

    bn, be = best
    if bn >= lib._moore_bound(d, D):
        return best  # already optimal (calibration cases return instantly)

    adj = [set() for _ in range(bn)]
    for u, v in be:
        adj[u].add(v)
        adj[v].add(u)
    A = list(range(bn // 2))

    n, adj, A = _grow(bn, adj, A, d, D, deadline, rng)
    if n > bn:
        edges = [(u, v) for u in A for v in adj[u]]
        if lib.is_valid(n, edges, d, D):
            return n, edges
    return best
