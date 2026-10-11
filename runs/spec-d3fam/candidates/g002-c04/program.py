import math
import random
import time

import lib

TIME_FRAC = 0.80      # fraction of time_limit used for search
MARGIN = 3.0          # seconds kept in reserve
MAX_FAILS = 12        # consecutive failed growth attempts before stopping


# ---------------------------------------------------------------- helpers

def _color(n, adj):
    """Two-colour a bipartite graph given as adjacency sets."""
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _bad_count(n, adj, D):
    """Ordered count of vertex pairs at distance > D (bitmask BFS from adjacency sets)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


# ---------------------------------------------------------------- growth move

def _augment(n, edges, d, D, rng, deadline):
    """Grow a d-regular bipartite graph by two vertices (a point P and a line L).

    A matching of d edges (a_i, b_i) with a_i in colour 0 and b_i in colour 1 is
    replaced by (a_i, P) and (b_i, L). Old degrees are preserved, P and L get degree d.
    Then 2-switches (a,b),(c,e) -> (a,e),(c,b) anneal the number of pairs at distance > D
    down to zero. Degrees and bipartiteness are preserved by every switch.
    Returns (n+2, edges) or None if the search fails before the deadline.
    """
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)

    P, L = n, n + 1          # P has colour 1 (its neighbours have colour 0); L has colour 0
    adj.append(set())
    adj.append(set())
    N = n + 2

    oriented = [((u, v) if col[u] == 0 else (v, u)) for u, v in edges]  # (colour0, colour1)
    rng.shuffle(oriented)
    used, pick = set(), []
    for idx, (a, b) in enumerate(oriented):
        if a not in used and b not in used:
            pick.append(idx)
            used.add(a)
            used.add(b)
            if len(pick) == d:
                break
    if len(pick) < d:
        return None

    picked = set(pick)
    E = [oriented[i] for i in range(len(oriented)) if i not in picked]
    for idx in pick:
        a, b = oriented[idx]
        adj[a].discard(b)
        adj[b].discard(a)
        adj[a].add(P)
        adj[P].add(a)
        adj[b].add(L)
        adj[L].add(b)
        E.append((a, P))
        E.append((L, b))

    M = len(E)
    cur = _bad_count(N, adj, D)
    it = 0
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        it += 1
        # Slowly cooling temperature; reheat occasionally to escape plateaus.
        T = max(0.2, 1.2 * (1.0 - (it % 4000) / 4000.0)) + 0.05
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b); adj[b].discard(a)
        adj[c].discard(e); adj[e].discard(c)
        adj[a].add(e); adj[e].add(a)
        adj[c].add(b); adj[b].add(c)
        new = _bad_count(N, adj, D)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            adj[a].discard(e); adj[e].discard(a)
            adj[c].discard(b); adj[b].discard(c)
            adj[a].add(b); adj[b].add(a)
            adj[c].add(e); adj[e].add(c)
    return N, list(E)


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(TIME_FRAC * time_limit, time_limit - MARGIN))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:                       # cycle of length 2D: bipartite, diameter D
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:                       # K_{d,d} is extremal for D = 2
        return lib.haar_graph(d, range(d))
    if D == 3 and lib.is_prime_power(d - 1):   # Moore-extremal projective plane
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    # Structured starting bases for D = 3 (degree d, all verified).
    bases = []
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            bases.append(lib.araujo_lopez_graph(d - 2))   # order 2(q^2+q+5), q = d-2
        except Exception:
            pass
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if D == 3 and q >= 2:
        bases.append(lib.projective_plane_incidence(q))   # order 2(q^2+q+1), degree q+1 <= d
    bases.append(lib.haar_graph(d, range(d)))             # K_{d,d}: always valid

    valid = [(n, e) for n, e in bases if lib.is_valid(n, e, d, D)]
    if not valid:
        return lib.haar_graph(d, range(d))
    best_n, best_e = max(valid, key=lambda c: c[0])

    # Growth phase: repeatedly add two vertices while the Moore bound allows.
    # Only d-regular bases are grown (the augment move assumes d-regularity).
    mb = _moore(d, D)
    cur_n, cur_e = best_n, best_e
    regular = (len(cur_e) * 2 == cur_n * d)
    if regular and D == 3:
        fails = 0
        while time.monotonic() < deadline and fails < MAX_FAILS and cur_n + 2 <= mb:
            res = _augment(cur_n, cur_e, d, D, rng, deadline)
            if res is None:
                fails += 1
                continue
            n2, e2 = res
            if not lib.is_valid(n2, e2, d, D):
                fails += 1
                continue
            fails = 0
            cur_n, cur_e = n2, e2
            if cur_n > best_n:
                best_n, best_e = cur_n, cur_e

    if lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    return lib.haar_graph(d, range(d))
