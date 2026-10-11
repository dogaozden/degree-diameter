import math
import random
import time

import lib

_TABLE_CACHE = {}
_GROUPS_CACHE = {}


def _groups(N):
    """Semidirect groups Z_m x|_r Z_k of order N (cyclic when r = 1 or m = 1)."""
    if N in _GROUPS_CACHE:
        return _GROUPS_CACHE[N]
    out = []
    for m in range(1, N + 1):
        if N % m:
            continue
        k = N // m
        if m == 1:
            out.append((1, k, 0))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                out.append((m, k, r))
    _GROUPS_CACHE[N] = out
    return out


def _table(grp):
    """Order and full multiplication table (right multiplication by g is T[x][g])."""
    if grp in _TABLE_CACHE:
        return _TABLE_CACHE[grp]
    order, mul, _ = lib.semidirect_group(*grp)
    T = [[mul(x, g) for g in range(order)] for x in range(order)]
    _TABLE_CACHE[grp] = (order, T)
    return order, T


def _lift(a, N, T, darts):
    """Bipartite lift: A-copies u*N+x, B-copies (a+v)*N+x; dart (u,v,g) joins A(u,x) to B(v,x*g)."""
    n = 2 * a * N
    adj = [set() for _ in range(n)]
    for u, v, g in darts:
        base_v = (a + v) * N
        for x in range(N):
            A = u * N + x
            B = base_v + T[x][g]
            adj[A].add(B)
            adj[B].add(A)
    return n, adj


def _check(n, adj, reps, D):
    """Diameter check from representative vertices only.

    The left action of the group preserves the lifted edge set and is transitive on
    each base-vertex orbit, so eccentricities from the base representatives suffice.
    """
    for src in reps:
        vis = [False] * n
        vis[src] = True
        frontier = [src]
        seen = 1
        for _ in range(D):
            nxt = []
            for x in frontier:
                for y in adj[x]:
                    if not vis[y]:
                        vis[y] = True
                        nxt.append(y)
            seen += len(nxt)
            frontier = nxt
            if not frontier:
                break
        if seen != n:
            return False
    return True


def _attempt(s, d, D, rng, deadline):
    """Random search for a bipartite group lift with 2*s vertices (a * |G| = s)."""
    pool = []
    for a in range(1, min(6, s) + 1):
        if s % a:
            continue
        N = s // a
        for grp in _groups(N):
            pool.append((a, N, grp))
    if not pool:
        return None
    while time.monotonic() < deadline:
        a, N, grp = pool[rng.randrange(len(pool))]
        order, T = _table(grp)
        darts = []
        for _ in range(d):
            perm = list(range(a))
            rng.shuffle(perm)
            for u in range(a):
                darts.append((u, perm[u], rng.randrange(order)))
        n, adj = _lift(a, order, T, darts)
        reps = [u * order for u in range(a)] + [(a + v) * order for v in range(a)]
        if not _check(n, adj, reps, D):
            continue
        edges = [(A, B) for A in range(a * order) for B in adj[A]]
        if lib.is_valid(n, edges, d, D):
            return n, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.75 * time_limit, time_limit - 5.0))
    deadline = start + budget

    best = None

    def consider(n, edges):
        nonlocal best
        if best is None or n > best[0]:
            if lib.is_valid(n, edges, d, D):
                best = (n, edges)

    # Safe fallbacks.
    try:
        if d >= 1 and D >= 2:
            consider(*lib.haar_graph(d, range(d)))   # K_{d,d}
        if d >= 1 and D >= 1:
            consider(2, [(0, 1)])
    except Exception:
        pass

    # Exact constructions for D = 3.
    if D == 3:
        q = d - 1
        try:
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                if best is not None and best[0] == 2 * (q * q + q + 1):
                    return best
        except Exception:
            pass
        try:
            q = d - 2
            if q >= 3 and lib.is_prime_power(q):
                consider(*lib.araujo_lopez_graph(q))
        except Exception:
            pass

    if best is None:
        return 2, [(0, 1)] if d >= 1 and D >= 1 else (1, [])

    # Bold search: bipartite group lifts over non-cyclic groups, aiming above the best order.
    try:
        rng = random.Random(seed)
        mb = lib.moore_bound(d, D)
        target = max(best[0] // 2 + 1, mb // 4)
        slice_len = 2.0
        while time.monotonic() < deadline:
            best_half = best[0] // 2
            now = time.monotonic()
            res = _attempt(target, d, D, rng, min(deadline, now + slice_len))
            if res is not None:
                consider(*res)
                target = max(target, res[0] // 2) + 1
            else:
                if target > best_half + 1:
                    step = max(1, (target - best_half) // 4)
                    target = max(best_half + 1, target - step)
    except Exception:
        pass

    return best[0], best[1]
