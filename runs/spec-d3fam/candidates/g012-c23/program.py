import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: instead of growing from algebraic bases by cover/arc extension,
# start from the best algebraic base and run a degree-preserving repair search.
#
#   * Insertion: pick d vertex-disjoint edges (a_i, b_i), delete them, add a new
#     pair (A, B) with A ~ all b_i and B ~ all a_i. Every degree is preserved and
#     the graph stays bipartite, but the order grows by 2.
#   * Repair: simulated annealing with degree-preserving 2-switches
#     (a,b),(c,e) -> (a,e),(c,b), minimising the number of unreachable ordered
#     pairs at distance > D.
#   * Any epoch that fails is discarded, and the search restarts from the best
#     verified graph, so the output is always valid.
# ----------------------------------------------------------------------------


def _bipartition(n, adj):
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


def _bad(n, adj, D):
    """Number of ordered pairs (v, w) with dist(v, w) > D. Zero iff diameter <= D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _swap(adj, a, b, c, e):
    """Replace edges (a,b),(c,e) by (a,e),(c,b). Degrees are preserved."""
    adj[a].discard(b)
    adj[b].discard(a)
    adj[c].discard(e)
    adj[e].discard(c)
    adj[a].add(e)
    adj[e].add(a)
    adj[c].add(b)
    adj[b].add(c)


def _base(d, D):
    """Best algebraic base graph (valid for the given d, D); K_{d,d} as the floor."""
    best = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    if D >= 3 and d >= 3:
        cands = []
        if lib.is_prime_power(d - 1):
            cands.append(lib.projective_plane_incidence(d - 1))
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                cands.append(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        if not cands:
            for q in range(d - 2, 1, -1):
                if lib.is_prime_power(q):
                    cands.append(lib.projective_plane_incidence(q))
                    break
        for c in sorted(cands, key=lambda t: -t[0]):
            if lib.is_valid(c[0], c[1], d, D):
                best = c
                break
    return best


def _fill(n, adj, col, d, E, rng):
    """Greedily add edges between deficient opposite-colour vertices (never breaks degrees)."""
    L = [v for v in range(n) if col[v] == 0 and len(adj[v]) < d]
    R = [v for v in range(n) if col[v] == 1 and len(adj[v]) < d]
    rng.shuffle(L)
    rng.shuffle(R)
    for a in L:
        for b in R:
            if len(adj[a]) >= d:
                break
            if len(adj[b]) < d and b not in adj[a]:
                adj[a].add(b)
                adj[b].add(a)
                E.append((a, b))


def _repair(d, D, n0, edges0, deadline, rng):
    moore = lib._moore_bound(d, D)
    adj0 = [[] for _ in range(n0)]
    for u, v in edges0:
        adj0[u].append(v)
        adj0[v].append(u)
    col0 = _bipartition(n0, adj0)
    best_n = n0
    best_col = col0
    best_E = [(a, b) if col0[a] == 0 else (b, a) for a, b in edges0]

    while time.monotonic() < deadline and best_n < moore:
        n = best_n
        col = best_col
        E = list(best_E)
        adj = [set() for _ in range(n)]
        for a, b in E:
            adj[a].add(b)
            adj[b].add(a)
        _fill(n, adj, col, d, E, rng)

        # Insertion: remove d disjoint edges, add a degree-preserving vertex pair.
        order = list(range(len(E)))
        rng.shuffle(order)
        used = set()
        pick = []
        for idx in order:
            a, b = E[idx]
            if a in used or b in used:
                continue
            pick.append(idx)
            used.add(a)
            used.add(b)
            if len(pick) == d:
                break
        if len(pick) < d:
            break

        A, B = n, n + 1
        ps = set(pick)
        new_E = [E[i] for i in range(len(E)) if i not in ps]
        adj.append(set())
        adj.append(set())
        for i in pick:
            a, b = E[i]
            adj[a].discard(b)
            adj[b].discard(a)
        for i in pick:
            a, b = E[i]
            adj[a].add(B)
            adj[B].add(a)
            adj[b].add(A)
            adj[A].add(b)
            new_E.append((a, B))
            new_E.append((A, b))
        E = new_E
        n2 = n + 2

        # Repair by annealed degree-preserving 2-switches.
        cost = _bad(n2, adj, D)
        ok = cost == 0
        iters = 4000
        it = 0
        while not ok and it < iters and time.monotonic() < deadline:
            it += 1
            T = 0.5 * (0.02 ** (it / iters))
            i = rng.randrange(len(E))
            j = rng.randrange(len(E))
            if i == j:
                continue
            a, b = E[i]
            c, e = E[j]
            if e in adj[a] or b in adj[c]:
                continue
            _swap(adj, a, b, c, e)
            new = _bad(n2, adj, D)
            if new <= cost or rng.random() < math.exp(-(new - cost) / T):
                cost = new
                E[i] = (a, e)
                E[j] = (c, b)
                if cost == 0:
                    ok = True
            else:
                _swap(adj, a, e, c, b)  # undo

        if ok:
            edges = [(a, b) for a, b in E]
            if lib.is_valid(n2, edges, d, D):
                best_n = n2
                best_col = col + [0, 1]
                best_E = edges
        # Otherwise discard this epoch and retry from the best verified graph.

    return best_n, [(a, b) for a, b in best_E]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 3.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    fallback = (2, [(0, 1)])
    base = _base(d, D)
    if lib.is_valid(base[0], base[1], d, D):
        best = base
    else:
        best = fallback

    try:
        rng = random.Random(seed)
        n_r, e_r = _repair(d, D, best[0], list(best[1]), deadline, rng)
        if n_r > best[0] and lib.is_valid(n_r, e_r, d, D):
            best = (n_r, e_r)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
