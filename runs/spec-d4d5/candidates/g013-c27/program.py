import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective plane base (exact for D = 3 with d - 1 a prime power).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
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


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products Z_m x| Z_k (annealed).
# Used as the fallback family that supplies a strong starting graph.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# NEW family: edge-switch annealing on d-regular bipartite graphs.
#
# A bipartite graph is stored as a list E of pairs (a, b): a in 0..N-1 is an
# A-vertex, b in 0..N-1 is a B-vertex (global id N + b). A move swaps the
# partners of two edges, (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), which keeps the
# graph simple, bipartite and d-regular. The cost is the number of ordered
# vertex pairs at distance > D, computed with big-int reachability bitsets.
# Once cost reaches 0 the graph is recorded and grown by one A and one B
# vertex (edge-insertion that preserves regularity), then annealed again.
# ----------------------------------------------------------------------------

def _unreached(n, adj, D):
    """Number of ordered vertex pairs at distance > D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _cost_bip(N, E, D):
    n = 2 * N
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(N + b)
        adj[N + b].append(a)
    return _unreached(n, adj, D)


def _random_regular(N, d, rng):
    """Random simple d-regular bipartite edge list on N + N vertices, or None."""
    E = []
    eset = set()
    for _ in range(d):
        found = False
        for _ in range(500):
            p = list(range(N))
            rng.shuffle(p)
            if all((i, p[i]) not in eset for i in range(N)):
                found = True
                break
        if not found:
            return None
        for i in range(N):
            eset.add((i, p[i]))
            E.append((i, p[i]))
    return E


def _to_bip(n, edges, d):
    """Convert a d-regular balanced bipartite graph to (N, E), or None."""
    adj = lib.adjacency(n, edges)
    if any(len(a) != d for a in adj):
        return None
    color = _bipartition(n, adj)
    A = [v for v in range(n) if color[v] == 0]
    B = [v for v in range(n) if color[v] == 1]
    if len(A) != len(B):
        return None
    ia = {v: i for i, v in enumerate(A)}
    ib = {v: i for i, v in enumerate(B)}
    E = []
    for u, v in edges:
        if color[u] == 0:
            E.append((ia[u], ib[v]))
        else:
            E.append((ia[v], ib[u]))
    return len(A), E


def _grow_bip(N, E, d, rng):
    """Add one A and one B vertex by edge insertion; keeps d-regularity. Returns new N or None."""
    m = len(E)
    pick = None
    for _ in range(50):
        order = list(range(m))
        rng.shuffle(order)
        usedA, usedB, cand = set(), set(), []
        for k in order:
            a, b = E[k]
            if a in usedA or b in usedB:
                continue
            usedA.add(a)
            usedB.add(b)
            cand.append(k)
            if len(cand) == d:
                break
        if len(cand) == d:
            pick = cand
            break
    if pick is None:
        return None
    newA = N
    newB = N
    pairs = [E[k] for k in pick]
    # (a_i, b_i) becomes (a_i, newB); then (newA, b_i) is appended for each i.
    for k, (a, _b) in zip(pick, pairs):
        E[k] = (a, newB)
    for _a, b in pairs:
        E.append((newA, b))
    return N + 1


def _sa_bip(N, d, D, E, rng, deadline):
    """Edge-switch anneal on E (in place) until cost 0 or deadline. Returns True on success."""
    eset = set(E)
    cost = _cost_bip(N, E, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 2.0, 0.05
    T = T0
    m = len(E)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = min(1.0, (now - t0) / span)
        T = T0 * (T1 / T0) ** frac
        for _ in range(20):
            i = rng.randrange(m)
            j = rng.randrange(m)
            if i == j:
                continue
            a1, b1 = E[i]
            a2, b2 = E[j]
            if a1 == a2 or b1 == b2:
                continue
            if (a1, b2) in eset or (a2, b1) in eset:
                continue
            E[i] = (a1, b2)
            E[j] = (a2, b1)
            c2 = _cost_bip(N, E, D)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                eset.discard((a1, b1))
                eset.discard((a2, b2))
                eset.add((a1, b2))
                eset.add((a2, b1))
                cost = c2
                if cost == 0:
                    break
            else:
                E[i] = (a1, b1)
                E[j] = (a2, b2)
    return cost == 0


def _edge_search(d, D, N, E, rng, deadline, consider):
    """Repeatedly: anneal to a valid graph at size N, record it, grow to N + 1."""
    while time.monotonic() < deadline:
        if not _sa_bip(N, d, D, E, rng, deadline):
            break
        consider(2 * N, [(a, N + b) for a, b in E])
        nxt = _grow_bip(N, E, d, rng)
        if nxt is None:
            break
        N = nxt


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D == 3:
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
        return best

    if D >= 4 and d >= 3:
        # Phase 1: voltage-lift annealing supplies a strong starting graph.
        lift_deadline = start + 0.3 * time_limit
        ks = [1, 1, 2, 2, 3, 4]
        while time.monotonic() < lift_deadline:
            k = rng.choice(ks)
            G = max(2, best_n // (2 * k) + 1 + rng.randrange(0, 3))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, lift_deadline, iters=1500)
            if res is not None:
                consider(res[0], res[1])

        # Phase 2 (new family): edge-switch annealing with growth.
        conv = _to_bip(best[0], best[1], d)
        if conv is not None:
            N, E = conv
        else:
            N = best_n // 2 + 1
            E = _random_regular(N, d, rng)
        if E is not None and N >= d:
            _edge_search(d, D, N, E, rng, deadline, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
