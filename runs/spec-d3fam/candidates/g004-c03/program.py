import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Basic graph helpers.
# ----------------------------------------------------------------------------

def _color(n, adj):
    """Two-colour a bipartite graph given as adjacency collections."""
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
    """Ordered count of vertex pairs at distance > D, via bitmask BFS."""
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


def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


# ----------------------------------------------------------------------------
# Spare-degree growth (cover extension + saturation). Only helps bases that
# have spare degree; regular bases are handled by the switch-based augment.
# ----------------------------------------------------------------------------

def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy cover of `full` by at most d candidates; None if it fails."""
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        bi = max(range(len(pool)), key=lambda i: (ball[pool[i]] & ~covered).bit_count())
        s = pool.pop(bi)
        if (ball[s] & ~covered) == 0:
            break
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Add vertices whose neighbourhoods cover everything within D-1 (keeps diameter <= D)."""
    if D < 2:
        return n, edges
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _color(n, adj)
    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = _greedy_cover(cands, ball, full, d, rng, False)
            if chosen is None:
                for _ in range(20):
                    chosen = _greedy_cover(cands, ball, full, d, rng, True)
                    if chosen:
                        break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate(n, edges, d, rng):
    """Join deficient opposite-side vertices (adding edges never increases distances)."""
    edges = list(edges)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    deg = [len(a) for a in adj]
    color = _color(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d and b not in adj[a]:
            edges.append((a, b))
            adj[a].add(b)
            adj[b].add(a)
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng):
    """Alternate cover extension and saturation while either still makes progress."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Two-vertex augmentation by degree-preserving 2-switches (annealed).
#
# Pick d disjoint edges (a_i, b_i) with a_i in colour 0; replace them by
# (a_i, P) and (b_i, L), where P and L are new vertices of degree d.
# Then anneal with 2-switches that keep all degrees and bipartiteness,
# minimising the number of pairs at distance > D.
# ----------------------------------------------------------------------------

def _augment(n, edges, d, D, rng, max_iter):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)

    P, L = n, n + 1                 # P has colour 1, L has colour 0
    adj.append(set())
    adj.append(set())
    N = n + 2

    oriented = [((u, v) if col[u] == 0 else (v, u)) for u, v in edges]
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
    T = 1.0
    for _ in range(max_iter):
        if cur == 0:
            break
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
    if cur > 0:
        return None
    return N, E


# ----------------------------------------------------------------------------
# Haar graph random search (fallback when no structured base applies).
# ----------------------------------------------------------------------------

def _haar_phase(d, D, rng, until, consider):
    m, misses = d + 1, 0
    while time.monotonic() < until and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= until:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            consider(*found)
            misses = 0
        else:
            misses += 1
        m += 1


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return (2, [(0, 1)]) if d >= 1 else (1, [])

    # Always-valid fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    structured = False
    if D == 3:
        bases = []
        q = d - 1
        if q >= 2 and lib.is_prime_power(q):
            bases.append(lib.projective_plane_incidence(q))     # degree d, order 2(q^2+q+1)
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            bases.append(lib.araujo_lopez_graph(d - 2))         # degree d, order 2(q^2+q+5)
        for n0, e0 in bases:
            if lib.is_valid(n0, e0, d, D):
                structured = True
                consider(n0, e0)
                n2, e2 = _grow(n0, e0, d, D, start + 0.15 * time_limit, rng)
                consider(n2, e2)

    if not structured:
        _haar_phase(d, D, rng, start + 0.4 * time_limit, consider)

    # Growth phase: repeatedly add two vertices by annealed 2-switches.
    mb = _moore(d, D)
    cur = best
    while time.monotonic() < deadline and cur[0] + 2 <= mb:
        res = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            r = _augment(cur[0], cur[1], d, D, rng, 1500)
            if r is not None and lib.is_valid(r[0], r[1], d, D):
                res = r
                break
        if res is None:
            break
        cur = res
        best = cur

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
