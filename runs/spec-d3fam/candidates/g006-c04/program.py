import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Pair insertion with degree-preserving repair (new helper for this program).
#
# Given a valid bipartite graph with max degree d, insert one new A-vertex v and
# one new B-vertex w. Pick d-1 pairwise disjoint edges (a_i, b_i), delete them,
# and add v-b_i, a_i-w for each i, plus the edge v-w. Then v and w both have
# degree d, and every old vertex keeps its degree. The new graph is usually not
# of diameter D, so a simulated annealing search over degree-preserving 2-switches
# (a1-b1, a2-b2 -> a1-b2, a2-b1) minimises the number of pairs at distance > D.
# If the cost reaches zero, the pair is kept and the process repeats.
# ----------------------------------------------------------------------------

def _orient(n, edges):
    """Return the edges with the A-endpoint (colour 0) first, after a 2-colouring by BFS."""
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
    return [(u, v) if color[u] == 0 else (v, u) for u, v in edges]


def _make_adj(N, E):
    adj = [set() for _ in range(N)]
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
    return adj


def _bad(N, adj, D):
    """Ordered count of vertex pairs at distance greater than D (zero iff valid)."""
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = [0] * N
        for v in range(N):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(N - r.bit_count() for r in reach)


def _grow_pair(E, n, d, rng):
    """Insert one A-vertex n and one B-vertex n+1 by rewiring d-1 disjoint edges; None on failure."""
    order = list(range(len(E)))
    rng.shuffle(order)
    used_a, used_b, chosen = set(), set(), []
    for idx in order:
        if len(chosen) == d - 1:
            break
        a, b = E[idx]
        if a in used_a or b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        chosen.append(idx)
    if len(chosen) < d - 1:
        return None
    cs = set(chosen)
    out = [e for k, e in enumerate(E) if k not in cs]
    v, w = n, n + 1
    for idx in chosen:
        a, b = E[idx]
        out.append((v, b))
        out.append((a, w))
    out.append((v, w))
    return out


def _repair(n0, E0, d, D, deadline, rng, budget):
    """Repeatedly insert a vertex pair and anneal back to diameter D; return the last valid state."""
    cur_n, cur_E = n0, list(E0)
    while time.monotonic() < deadline - 0.2:
        newE = _grow_pair(cur_E, cur_n, d, rng)
        if newE is None:
            break
        N = cur_n + 2
        E = newE
        adj = _make_adj(N, E)
        cost = _bad(N, adj, D)
        att_start = time.monotonic()
        att_end = min(deadline, att_start + budget)
        T0, T1 = 3.0, 0.2
        m = len(E)
        while cost > 0:
            t = time.monotonic()
            if t >= att_end:
                break
            frac = (t - att_start) / max(1e-9, att_end - att_start)
            T = T0 * (T1 / T0) ** frac
            i = rng.randrange(m)
            j = rng.randrange(m)
            if i == j:
                continue
            a1, b1 = E[i]
            a2, b2 = E[j]
            if a1 == a2 or b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
                continue
            adj[a1].discard(b1)
            adj[b1].discard(a1)
            adj[a2].discard(b2)
            adj[b2].discard(a2)
            adj[a1].add(b2)
            adj[b2].add(a1)
            adj[a2].add(b1)
            adj[b1].add(a2)
            c2 = _bad(N, adj, D)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                E[i] = (a1, b2)
                E[j] = (a2, b1)
                cost = c2
            else:
                adj[a1].discard(b2)
                adj[b2].discard(a1)
                adj[a2].discard(b1)
                adj[b1].discard(a2)
                adj[a1].add(b1)
                adj[b1].add(a1)
                adj[a2].add(b2)
                adj[b2].add(a2)
        if cost == 0:
            cur_n, cur_E = N, E
        else:
            break
    return cur_n, cur_E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Fallback: K_{d,d} has diameter 2.
    kn, ke = lib.haar_graph(d, range(d))
    cands = [(kn, ke)]

    if D >= 3:
        # Araujo-Pardo & Lopez record for d = q + 2, q a prime power.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                cands.append(lib.araujo_lopez_graph(d - 2))
            except (ValueError, AssertionError):
                pass
        # Plain projective plane incidence graph with the largest prime power q <= d - 1.
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                cands.append(lib.projective_plane_incidence(q))
                break

    valid = [c for c in cands if lib.is_valid(c[0], c[1], d, D)]
    best_n, best_e = max(valid, key=lambda c: c[0])

    if D >= 3 and d >= 3:
        attempt_budget = max(2.0, 0.12 * budget)
        n2, e2 = _repair(best_n, _orient(best_n, best_e), d, D,
                         deadline, rng, attempt_budget)
        e2 = [(int(u), int(v)) for u, v in e2]
        if n2 > best_n and lib.is_valid(n2, e2, d, D):
            best_n, best_e = n2, e2

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = kn, ke
    return best_n, [(int(u), int(v)) for u, v in best_e]
