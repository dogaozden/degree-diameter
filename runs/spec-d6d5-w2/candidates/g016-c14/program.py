import math
import random
import time

import lib


def _kdd(d):
    """Complete bipartite K_{d,d}: diameter 2, degree d, always valid for D >= 2."""
    return lib.haar_graph(d, range(d))


def _bipartition(n, adj):
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


def _bad_pairs(n, adj, D):
    """Number of unordered pairs at distance > D (unreachable counts as bad)."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return sum(n - b.bit_count() for b in ball) // 2


def _insert_pair(adj, color, d, rng):
    """Append an A-vertex x and a B-vertex y. Reroute d-1 disjoint existing edges
    (a_i, b_i) into (x, b_i) and (a_i, y), then join x-y. Degrees are preserved
    everywhere and every new vertex gets degree d. Returns False if no picks."""
    n = len(adj)
    picks, used_a, used_b = [], set(), set()
    tries = 0
    while len(picks) < d - 1 and tries < 5000:
        tries += 1
        a = rng.randrange(n)
        if color[a] != 0 or a in used_a or not adj[a]:
            continue
        b = rng.choice(list(adj[a]))
        if b in used_b:
            continue
        used_a.add(a)
        used_b.add(b)
        picks.append((a, b))
    if len(picks) < d - 1:
        return False
    x, y = n, n + 1
    adj.append(set())
    adj.append(set())
    color.append(0)
    color.append(1)
    for a, b in picks:
        adj[a].discard(b)
        adj[b].discard(a)
        adj[x].add(b)
        adj[b].add(x)
        adj[a].add(y)
        adj[y].add(a)
    adj[x].add(y)
    adj[y].add(x)
    return True


def _anneal(adj, color, D, deadline, rng, iters, cost):
    """Double-edge-swap annealing on bad-pair count. Preserves bipartiteness and degrees."""
    n = len(adj)
    A = [v for v in range(n) if color[v] == 0]
    T = 0.6
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        a1, a2 = rng.choice(A), rng.choice(A)
        if a1 == a2 or not adj[a1] or not adj[a2]:
            continue
        b1 = rng.choice(list(adj[a1]))
        b2 = rng.choice(list(adj[a2]))
        if b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
            continue
        adj[a1].discard(b1)
        adj[b1].discard(a1)
        adj[a2].discard(b2)
        adj[b2].discard(a2)
        adj[a1].add(b2)
        adj[b2].add(a1)
        adj[a2].add(b1)
        adj[b1].add(a2)
        c2 = _bad_pairs(n, adj, D)
        if c2 <= cost or rng.random() < math.exp((cost - c2) / T):
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
        T = max(0.05, T * 0.99)
    return cost


def _edges_of(adj):
    return [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]


def _grow(d, D, deadline, rng, record):
    """Repeatedly insert vertex pairs and anneal back to diameter D. Calls record(n, edges)
    after each successful stage."""
    adj = [set(range(d, 2 * d)) if v < d else set(range(d)) for v in range(2 * d)]
    color = [0] * d + [1] * d
    record(len(adj), _edges_of(adj))
    batch = 1
    fails = 0
    while time.monotonic() < deadline:
        trial = [set(s) for s in adj]
        tcol = list(color)
        ok = True
        for _ in range(batch):
            if not _insert_pair(trial, tcol, d, rng):
                ok = False
                break
        if not ok:
            break
        c = _bad_pairs(len(trial), trial, D)
        c = _anneal(trial, tcol, D, deadline, rng, 150, c)
        if c == 0:
            adj, color = trial, tcol
            record(len(adj), _edges_of(adj))
            fails = 0
            batch = min(batch * 2, max(1, len(adj) // 30))
        else:
            fails += 1
            batch = max(1, batch // 2)
            if fails > 20:
                break


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best_n, best_e = _kdd(d)
    if not lib.is_valid(best_n, best_e, d, D):
        return 1, []

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    # Small structured baselines for D = 3 (calibration cases return instantly).
    if D == 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break
        q = d - 2
        if q >= 3 and lib.is_prime_power(q):
            try:
                consider(*lib.araujo_lopez_graph(q))
            except Exception:
                pass
        if best_n >= 14 and D == 3 and d == 3:
            return best_n, best_e

    # Main bold family for D >= 3: degree-preserving growth with diameter repair.
    rng = random.Random(seed * 1000003 + d * 131 + D)
    grow_deadline = start + (0.85 if D >= 5 else 0.5) * time_limit
    _grow(d, D, grow_deadline, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = _kdd(d)
    return best_n, best_e
