import math
import random
import time

import lib

TIME_FRAC = 0.85      # fraction of time_limit used before returning
MARGIN = 2.0          # seconds kept in reserve
ITER = 1500           # annealing steps per growth attempt
MAX_FAILS = 8         # consecutive failed growth attempts before stopping
COVER_ITER = 300000   # annealing steps per difference-cover attempt
COVER_FAILS = 6       # consecutive failed moduli before the cover search stops


# ---------------------------------------------------------------- helpers

def _two_colour(n, edges):
    """Proper 2-colouring of a bipartite graph, component by component."""
    adj = lib.adjacency(n, edges)
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
    return color


def _balls_adj(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    reach = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        if new == reach:
            break
        reach = new
    return reach


def _bad_pairs(n, adj, D):
    """Number of unordered pairs at distance > D (unreachable counts)."""
    reach = _balls_adj(n, adj, D)
    return sum(n - r.bit_count() for r in reach) // 2


def _edges(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


# ---------------------------------------------------------- difference covers
# Haar graph H(Z_m, S): a_i ~ b_{i+s}. Distances a-a are governed by S-S and
# a-b by S-S+S, so diameter 3 holds whenever S-S covers Z_m and |S| = d.
# Perfect difference sets (d-1 a prime power) reach the Moore bound; for other
# d we search for near-perfect covers at moduli above the current record.

def _diff_cover(m, k, rng, deadline, iters):
    """Annealing search for k distinct residues mod m whose differences cover Z_m."""
    if k > m:
        return None
    S = rng.sample(range(m), k)

    def uncovered(S):
        seen = set()
        for s in S:
            for t in S:
                if s != t:
                    seen.add((s - t) % m)
        return m - 1 - len(seen)   # 0 is always covered

    cost = uncovered(S)
    for it in range(iters):
        if cost == 0:
            return sorted(S)
        if time.monotonic() > deadline:
            return None
        i = rng.randrange(k)
        r = rng.randrange(m)
        if r in S:
            continue
        old = S[i]
        S[i] = r
        new = uncovered(S)
        temp = 1.0 * (1.0 - it / iters) + 0.05
        if new <= cost or rng.random() < math.exp(-(new - cost) / temp):
            cost = new
        else:
            S[i] = old
    return sorted(S) if cost == 0 else None


def _haar_search(d, D, best, rng, deadline):
    """Search upward over cyclic moduli m for a difference cover of size d; keep the largest valid Haar graph."""
    best_n, best_e = best
    m = best_n // 2 + 1
    fails = 0
    while time.monotonic() < deadline and fails < COVER_FAILS and m <= d * d - d + 1:
        now = time.monotonic()
        remaining = deadline - now
        budget = min(remaining, max(2.0, remaining / 4.0))
        S = _diff_cover(m, d, rng, now + budget, COVER_ITER)
        if S is not None:
            n, e = lib.haar_graph(m, S)
            if n > best_n and lib.is_valid(n, e, d, D):
                best_n, best_e = n, e
            fails = 0
        else:
            fails += 1
        m += 1
    return best_n, best_e


# ---------------------------------------------------------------- local moves

def _pick_neighbours(n, adj, color, c, d, D, rng):
    """Choose d vertices of colour 1-c, greedily covering radius-(D-1) balls."""
    other = [v for v in range(n) if color[v] == 1 - c]
    if len(other) < d:
        return None
    balls = _balls_adj(n, adj, D - 1)
    full = (1 << n) - 1
    covered, chosen = 0, []
    cand = other[:]
    rng.shuffle(cand)
    while covered != full and len(chosen) < d and cand:
        best_u, best_g = -1, 0
        for u in cand:
            g = (balls[u] & ~covered).bit_count()
            if g > best_g:
                best_u, best_g = u, g
        if best_u < 0:
            break
        chosen.append(best_u)
        covered |= balls[best_u]
        cand.remove(best_u)
    chosen_set = set(chosen)
    rest = [v for v in other if v not in chosen_set]
    rng.shuffle(rest)
    chosen += rest[:d - len(chosen)]
    return chosen


def _swap(adj, side0, rng):
    """Degree-preserving double-edge swap keeping bipartiteness. Returns undo info or None."""
    a1 = rng.choice(side0)
    if not adj[a1]:
        return None
    b1 = rng.choice(tuple(adj[a1]))
    a2 = rng.choice(side0)
    if a2 == a1 or not adj[a2]:
        return None
    b2 = rng.choice(tuple(adj[a2]))
    if b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
        return None
    adj[a1].remove(b1); adj[b1].remove(a1)
    adj[a2].remove(b2); adj[b2].remove(a2)
    adj[a1].add(b2); adj[b2].add(a1)
    adj[a2].add(b1); adj[b1].add(a2)
    return (a1, b1, a2, b2)


def _unswap(adj, mv):
    a1, b1, a2, b2 = mv
    adj[a1].remove(b2); adj[b2].remove(a1)
    adj[a2].remove(b1); adj[b1].remove(a2)
    adj[a1].add(b1); adj[b1].add(a1)
    adj[a2].add(b2); adj[b2].add(a2)


def _augment(n, adj, color, d, rng):
    """Add edges between deficient opposite-colour vertices. Never breaks the diameter bound."""
    d0 = [u for u in range(n) if color[u] == 0 and len(adj[u]) < d]
    d1 = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    if not d0 or not d1:
        return
    rng.shuffle(d0)
    for u in d0:
        if len(adj[u]) >= d:
            continue
        for v in d1:
            if len(adj[v]) < d and v not in adj[u]:
                adj[u].add(v)
                adj[v].add(u)
                if len(adj[u]) >= d:
                    break


def _attempt(n, adj, color, d, D, rng, deadline):
    """Add one vertex and anneal until the diameter bound holds again. Returns new state or None."""
    adj = [set(s) for s in adj]
    color = list(color)
    c = rng.randrange(2)
    nb = _pick_neighbours(n, adj, color, c, d, D, rng)
    if nb is None:
        return None
    for u in nb:
        if len(adj[u]) >= d:
            w = rng.choice(tuple(adj[u]))
            adj[u].discard(w)
            adj[w].discard(u)
    x = n
    adj.append(set())
    color.append(c)
    n += 1
    for u in nb:
        adj[x].add(u)
        adj[u].add(x)

    side0 = [v for v in range(n) if color[v] == 0]
    cost = _bad_pairs(n, adj, D)
    for it in range(ITER):
        if cost == 0:
            break
        if time.monotonic() > deadline:
            return None
        mv = _swap(adj, side0, rng)
        if mv is None:
            continue
        new = _bad_pairs(n, adj, D)
        delta = new - cost
        temp = 1.5 * (1.0 - it / ITER) + 0.05
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cost = new
        else:
            _unswap(adj, mv)
    if cost != 0:
        return None
    _augment(n, adj, color, d, rng)
    return n, adj, color


def _grow(base_n, base_e, d, D, rng, deadline):
    """Add vertices with local annealing; return the largest valid graph found."""
    color = _two_colour(base_n, base_e)
    adj = [set() for _ in range(base_n)]
    for u, v in base_e:
        adj[u].add(v)
        adj[v].add(u)
    cur_n, cur_adj, cur_col = base_n, adj, color
    best_n, best_e = base_n, base_e

    fails = 0
    while time.monotonic() < deadline and fails < MAX_FAILS:
        res = _attempt(cur_n, cur_adj, cur_col, d, D, rng, deadline)
        if res is None:
            fails += 1
            continue
        fails = 0
        cur_n, cur_adj, cur_col = res
        if cur_n > best_n:
            best_n, best_e = cur_n, _edges(cur_n, cur_adj)
    return best_n, best_e


# ---------------------------------------------------------------- driver

def _starting_bases(d, D):
    """Verified starting graphs for (d, D); the largest one is used as the safe fallback."""
    bases = []
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            bases.append(lib.araujo_lopez_graph(d - 2))  # record construction, degree q+2 = d
        except Exception:
            pass
    pg = _pg_base(d)
    if pg is not None:
        bases.append(pg)
    bases.append(lib.haar_graph(d, range(d)))
    return [(n, e) for n, e in bases if lib.is_valid(n, e, d, D)]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, TIME_FRAC * time_limit - MARGIN)
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
        return lib.projective_plane_incidence(d - 1)

    valid = _starting_bases(d, D)
    if not valid:
        return lib.haar_graph(d, range(d))
    base_n, base_e = max(valid, key=lambda c: c[0])
    best_n, best_e = base_n, base_e

    # Bold change for D = 3: difference-cover Haar graphs (a different construction
    # from the projective-plane / Araujo-Pardo-Lopez lineage).
    if D == 3 and d >= 4:
        best_n, best_e = _haar_search(d, D, (best_n, best_e), rng, deadline)

    # Remaining time: local growth from the best valid graph.
    if time.monotonic() < deadline:
        try:
            gn, ge = _grow(best_n, best_e, d, D, rng, deadline)
            if gn > best_n and lib.is_valid(gn, ge, d, D):
                best_n, best_e = gn, ge
        except Exception:
            pass

    if lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    return base_n, base_e
