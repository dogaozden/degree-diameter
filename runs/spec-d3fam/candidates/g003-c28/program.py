import math
import random
import time

import lib


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _is_regular(n, edges, d):
    """True if every vertex 0..n-1 has degree exactly d."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return all(x == d for x in deg)


def _cost(n, adj, D):
    """Number of unordered vertex pairs at distance > D (0 means diameter <= D)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _surgery(n, E, adj, d, rng):
    """Add two vertices x (left) and y (right) to a d-regular bipartite graph.

    Removes a matching of d edges (a_i, b_i) and reconnects x to all b_i and y to all a_i.
    The graph stays d-regular. Returns (n_new, E_new) or None if no matching of size d is found.
    """
    idx = list(range(len(E)))
    rng.shuffle(idx)
    usedL, usedR, pick = set(), set(), []
    for k in idx:
        a, b = E[k]
        if a in usedL or b in usedR:
            continue
        usedL.add(a)
        usedR.add(b)
        pick.append(k)
        if len(pick) == d:
            break
    if len(pick) < d:
        return None
    x, y = n, n + 1
    pickset = set(pick)
    newE = [E[k] for k in range(len(E)) if k not in pickset]
    adj.append(set())
    adj.append(set())
    for k in pick:
        a, b = E[k]
        adj[a].discard(b)
        adj[b].discard(a)
        adj[a].add(y)
        adj[y].add(a)
        adj[b].add(x)
        adj[x].add(b)
        newE.append((a, y))
        newE.append((x, b))
    return n + 2, newE


def _sa_grow(n, E, d, D, deadline, start, budget, rng, consider):
    """Grow a d-regular bipartite graph by vertex pairs, using simulated annealing on
    2-switches (which preserve degrees) to remove pairs at distance > D."""
    E = list(E)
    adj = [set() for _ in range(n)]
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
    cur = _cost(n, adj, D)
    while time.monotonic() < deadline:
        if cur == 0:
            consider(n, list(E))
            if n + 2 > lib._moore_bound(d, D):
                break
            res = _surgery(n, E, adj, d, rng)
            if res is None:
                break
            n, E = res
            cur = _cost(n, adj, D)
            continue
        for _ in range(200):
            if time.monotonic() >= deadline:
                break
            i = rng.randrange(len(E))
            j = rng.randrange(len(E))
            if i == j:
                continue
            a, b = E[i]
            c, e = E[j]
            if a == c or b == e:
                continue
            if e in adj[a] or b in adj[c]:
                continue
            adj[a].discard(b)
            adj[b].discard(a)
            adj[c].discard(e)
            adj[e].discard(c)
            adj[a].add(e)
            adj[e].add(a)
            adj[c].add(b)
            adj[b].add(c)
            E[i] = (a, e)
            E[j] = (c, b)
            new = _cost(n, adj, D)
            T = max(0.2, 2.0 * (1.0 - (time.monotonic() - start) / budget))
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
                if cur == 0:
                    break
            else:
                adj[a].discard(e)
                adj[e].discard(a)
                adj[c].discard(b)
                adj[b].discard(c)
                adj[a].add(b)
                adj[b].add(a)
                adj[c].add(e)
                adj[e].add(c)
                E[i] = (a, b)
                E[j] = (c, e)
    return


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = 0.7 * time_limit
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and degree d.
    best_n, best_e = lib.haar_graph(d, range(d))
    holder = {"n": best_n, "e": best_e}

    def consider(n, e):
        if n > holder["n"] and lib.is_valid(n, e, d, D):
            holder["n"] = n
            holder["e"] = list(e)

    sources = []
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            sources.append(pg)
        # Araujo-Pardo & Lopez record family for d = q + 2, q a prime power.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                al = lib.araujo_lopez_graph(d - 2)
                consider(al[0], al[1])
                sources.append(al)
            except Exception:
                pass

    # Bold experiment for the diameter-3 targets: start from the largest d-regular
    # source and grow it by annealed 2-switch repair of vertex pairs.
    if D == 3 and d >= 3:
        regular = [s for s in sources if _is_regular(s[0], s[1], d)]
        if regular:
            n0, e0 = max(regular, key=lambda s: s[0])
            color = [-1] * n0
            adj0 = [[] for _ in range(n0)]
            for u, v in e0:
                adj0[u].append(v)
                adj0[v].append(u)
            # Two-colour the bipartite source (color 0 = left side).
            for s in range(n0):
                if color[s] != -1:
                    continue
                color[s] = 0
                stack = [s]
                while stack:
                    u = stack.pop()
                    for v in adj0[u]:
                        if color[v] == -1:
                            color[v] = 1 - color[u]
                            stack.append(v)
            E = [(u, v) if color[u] == 0 else (v, u) for u, v in e0]
            _sa_grow(n0, E, d, D, deadline, start, budget, rng, consider)

    final_n, final_e = holder["n"], holder["e"]
    if not lib.is_valid(final_n, final_e, d, D):
        return lib.haar_graph(d, range(d))
    return final_n, final_e
