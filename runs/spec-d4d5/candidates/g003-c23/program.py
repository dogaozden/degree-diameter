import math
import random
import time

import lib


_BIG = 10 ** 9


class _Best:
    """Holds the best validated graph found so far."""

    def __init__(self, d, D, n, edges):
        self.d, self.D, self.n, self.e = d, D, n, edges

    def offer(self, n, edges):
        """Adopt (n, edges) if it is larger and passes the exact validity check."""
        if n > self.n and lib.is_valid(n, edges, self.d, self.D):
            self.n, self.e = n, edges
            return True
        return False


# ----------------------------------------------------------------------------
# Phase 1: annealed bi-Cayley voltage lifts over Z_m x| Z_k (k base vertices per side).
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G, or None."""
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
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms, limit=float("inf")):
    """Number of (representative, vertex) pairs not reached within D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
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
        if total > limit:
            return total
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and B-assignments of each layer."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)
        limit = cost - T * math.log(1.0 - rng.random())
        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


def _lift_phase(d, D, best, deadline, rng):
    ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
    while time.monotonic() < deadline:
        k = rng.choice(ks)
        base = best.n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        res = _anneal(d, D, k, order, mul, rng, deadline, 400)
        if res is not None:
            best.offer(res[0], res[1])


# ----------------------------------------------------------------------------
# Phase 2 (bold, different): edge-level simulated annealing that grows the best
# graph by two vertices (one per side) and repairs it directly, with cost =
# number of vertex pairs at distance > D. Degrees never exceed d.
# ----------------------------------------------------------------------------

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


def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs included)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _propose(A, B, adj, d, rng):
    """Random move as a list of ('+'/'-', a, b) edge operations, or None."""
    r = rng.random()
    if r < 0.4:
        a1 = rng.choice(A)
        a2 = rng.choice(A)
        if a1 == a2 or not adj[a1] or not adj[a2]:
            return None
        b1 = rng.choice(list(adj[a1]))
        b2 = rng.choice(list(adj[a2]))
        if b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
            return None
        return [('-', a1, b1), ('-', a2, b2), ('+', a1, b2), ('+', a2, b1)]
    defA = [a for a in A if len(adj[a]) < d]
    defB = [b for b in B if len(adj[b]) < d]
    if r < 0.6:
        if not defA or not defB:
            return None
        a = rng.choice(defA)
        b = rng.choice(defB)
        if b in adj[a]:
            return None
        return [('+', a, b)]
    if r < 0.8:
        if not defA:
            return None
        a0 = rng.choice(defA)
        a = rng.choice(A)
        if a == a0 or not adj[a]:
            return None
        b = rng.choice(list(adj[a]))
        if b in adj[a0]:
            return None
        return [('-', a, b), ('+', a0, b)]
    if not defB:
        return None
    b0 = rng.choice(defB)
    b = rng.choice(B)
    if b == b0 or not adj[b]:
        return None
    a = rng.choice(list(adj[b]))
    if a in adj[b0]:
        return None
    return [('-', a, b), ('+', a, b0)]


def _apply(adj, ops):
    for s, a, b in ops:
        if s == '+':
            adj[a].add(b)
            adj[b].add(a)
        else:
            adj[a].discard(b)
            adj[b].discard(a)


def _undo(adj, ops):
    for s, a, b in reversed(ops):
        if s == '+':
            adj[a].discard(b)
            adj[b].discard(a)
        else:
            adj[a].add(b)
            adj[b].add(a)


def _sa(n, A, B, adj, d, D, deadline, rng):
    """Anneal edges on the fixed vertex set until bad pairs = 0 or time runs out."""
    cost = _bad(n, adj, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0, T1 = 2.0, 0.1
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** ((now - t0) / span)
        limit = cost - T * math.log(1.0 - rng.random())
        ops = _propose(A, B, adj, d, rng)
        if not ops:
            continue
        _apply(adj, ops)
        c2 = _bad(n, adj, D)
        if c2 <= limit:
            cost = c2
        else:
            _undo(adj, ops)
    return cost


def _grow_phase(d, D, best, deadline, rng):
    fails = 0
    while time.monotonic() < deadline - 0.2 and fails < 2:
        n, edges = best.n, best.e
        adjl = [[] for _ in range(n)]
        for u, v in edges:
            adjl[u].append(v)
            adjl[v].append(u)
        side = _bipartition(n, adjl) + [0, 1]
        N = n + 2
        adj = [set() for _ in range(N)]
        for u, v in edges:
            adj[u].add(v)
            adj[v].add(u)
        A = [v for v in range(N) if side[v] == 0]
        B = [v for v in range(N) if side[v] == 1]
        now = time.monotonic()
        slice_end = min(deadline, now + max(2.0, 0.35 * (deadline - now)))
        cost = _sa(N, A, B, adj, d, D, slice_end, rng)
        if cost != 0:
            fails += 1
            continue
        fails = 0
        e2 = [(a, b) for a in A for b in adj[a]]
        if not best.offer(N, e2):
            break


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = 0.85 * time_limit
    deadline = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    n0, e0 = lib.haar_graph(d, range(d))
    best = _Best(d, D, n0, e0)

    if D >= 3 and d >= 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        best.offer(n, e)
        if best.n >= lib._moore_bound(d, D):
            return best.n, best.e

    if d >= 3 and D >= 3 and best.n < lib._moore_bound(d, D):
        try:
            _lift_phase(d, D, best, start + 0.45 * total, rng)
        except Exception:
            pass
        try:
            _grow_phase(d, D, best, deadline, rng)
        except Exception:
            pass

    if not lib.is_valid(best.n, best.e, d, D):
        return n0, e0
    return best.n, best.e
