import random
import time

import lib


def _masks(adj, n, R):
    """Bitmask of the radius-R ball around every vertex."""
    reach = [1 << v for v in range(n)]
    for _ in range(R):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _to_edges(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _color(n, adj):
    """2-colouring of a bipartite graph (components coloured independently)."""
    side = [-1] * n
    for s in range(n):
        if side[s] != -1:
            continue
        side[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if side[v] == -1:
                    side[v] = 1 - side[u]
                    stack.append(v)
    return side


def _grow(n, adj, side, d, D, rng, deadline):
    """Greedy growth that keeps validity.

    Step 1: add edges between spare-degree vertices on opposite sides (never hurts distances).
    Step 2 (radius-cover insertion): a new vertex x on side s with neighbours N(x) in the
    opposite side is valid iff the radius-(D-1) balls of N(x) cover every existing vertex,
    since dist(x, y) = 1 + min_{w in N(x)} dist(w, y). Choose N(x) by greedy set cover
    over the bitmask balls, using only spare-degree candidates.
    """
    while time.monotonic() < deadline:
        progress = False

        spA = [v for v in range(n) if side[v] == 0 and len(adj[v]) < d]
        spB = [v for v in range(n) if side[v] == 1 and len(adj[v]) < d]
        rng.shuffle(spA)
        rng.shuffle(spB)
        for a in spA:
            for b in spB:
                if len(adj[a]) >= d:
                    break
                if len(adj[b]) < d and b not in adj[a]:
                    adj[a].add(b)
                    adj[b].add(a)
                    progress = True

        full = (1 << n) - 1
        balls = _masks(adj, n, D - 1)
        for s in rng.sample([0, 1], 2):
            avail = [v for v in range(n) if side[v] == 1 - s and len(adj[v]) < d]
            if not avail:
                continue
            covered, chosen = 0, []
            while len(chosen) < d and covered != full and avail:
                best_gain, best_list = 0, []
                for c in avail:
                    g = (balls[c] & ~covered).bit_count()
                    if g > best_gain:
                        best_gain, best_list = g, [c]
                    elif g == best_gain and g > 0:
                        best_list.append(c)
                if best_gain == 0:
                    break
                c = rng.choice(best_list)
                chosen.append(c)
                covered |= balls[c]
                avail.remove(c)
            if chosen and covered == full:
                for c in chosen:
                    adj[c].add(n)
                adj.append(set(chosen))
                side.append(s)
                n += 1
                progress = True
                break

        if not progress:
            break
    return n


def _improve(n, edges, d, D, rng, deadline):
    """Randomised local search: delete a couple of edges, regrow, keep valid results."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    side = _color(n, adj)
    cur_n = _grow(n, adj, side, d, D, rng, deadline)
    cur_adj, cur_side = adj, side
    best = (cur_n, _to_edges(cur_n, cur_adj))

    while time.monotonic() < deadline:
        t_adj = [set(s) for s in cur_adj]
        t_side = list(cur_side)
        for _ in range(rng.choice([1, 1, 2])):
            nonempty = [v for v in range(len(t_adj)) if t_adj[v]]
            if not nonempty:
                break
            u = rng.choice(nonempty)
            v = rng.choice(sorted(t_adj[u]))
            t_adj[u].discard(v)
            t_adj[v].discard(u)
        tn = _grow(len(t_adj), t_adj, t_side, d, D, rng, deadline)
        if time.monotonic() >= deadline:
            break
        tedges = _to_edges(tn, t_adj)
        if tn < cur_n or not lib.within_diameter(tn, tedges, D):
            continue
        cur_adj, cur_side, cur_n = t_adj, t_side, tn
        if tn > best[0]:
            best = (tn, tedges)
    return best


def _haar_search(d, D, rng, deadline):
    best = lib.haar_graph(d, range(d))
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)
    q = d - 1

    if D == 3:
        # Exact Moore-type record when d-1 is a prime power.
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)

        # Araujo-Pardo & Lopez record for d = q+2 with q a prime power.
        q2 = d - 2
        if q2 >= 3 and lib.is_prime_power(q2):
            try:
                n0, e0 = lib.araujo_lopez_graph(q2)
            except Exception:
                n0, e0 = None, None
            if n0 is not None and lib.is_valid(n0, e0, d, D):
                try:
                    n1, e1 = _improve(n0, e0, d, D, rng, deadline)
                    if n1 > n0 and lib.is_valid(n1, e1, d, D):
                        return n1, e1
                except Exception:
                    pass
                return n0, e0

    return _haar_search(d, D, rng, deadline)
