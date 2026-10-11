import math
import random
import time

import lib


def _fallback(d, D):
    """Verified baseline: K_{d,d} (diameter 2) or trivial graphs for small parameters."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    return lib.haar_graph(d, range(d))


def _group_list(N, rng):
    """Cyclic group of order N plus a few semidirect products Z_m x| Z_k of order N."""
    groups = [lib.cyclic_group(N)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:3]:
            try:
                groups.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return groups


def _ratio_table(N, mul, inv):
    """R[x][y] = x * y^{-1}."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


def _upd(cnt, R, S, skip, v, sign):
    """Add (sign=+1) or remove (sign=-1) ordered differences of v against S[j], j != skip.

    Returns the change in the number of uncovered group elements.
    """
    ch = 0
    Rv = R[v]
    for j, b in enumerate(S):
        if j == skip:
            continue
        for g in (Rv[b], R[b][v]):
            if sign > 0:
                if cnt[g] == 0:
                    ch -= 1
                cnt[g] += 1
            else:
                cnt[g] -= 1
                if cnt[g] == 0:
                    ch += 1
    return ch


def _anneal(N, R, d, rng, steps, e):
    """Find d distinct elements S with S S^{-1} = G by annealing; None if not found."""
    S = rng.sample(range(N), d)
    cnt = [0] * N
    cnt[e] = 1
    for a in S:
        for b in S:
            if a != b:
                cnt[R[a][b]] += 1
    unc = sum(1 for c in cnt if c == 0)
    if unc == 0:
        return S
    for it in range(steps):
        T = 1.0 - 0.95 * it / steps
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        old = S[i]
        delta = _upd(cnt, R, S, i, old, -1) + _upd(cnt, R, S, i, x, +1)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = x
            unc += delta
            if unc == 0:
                return S
        else:
            _upd(cnt, R, S, i, x, -1)
            _upd(cnt, R, S, i, old, +1)
    return None


# ----------------------------------------------------------------------------
# New routine: vertex-pair growth by edge switching.
#
# For a d-regular bipartite graph G with diameter <= D, remove a matching M of
# d edges (x_i, y_i), add a new A-vertex a joined to all y_i and a new B-vertex
# b joined to all x_i. Degrees stay d, but distances may break. Then anneal with
# degree-preserving double edge switches (x1,y1),(x2,y2) -> (x1,y2),(x2,y1),
# minimising the number of pairs at distance > D. Success gives a valid
# d-regular bipartite graph on n+2 vertices.
# ----------------------------------------------------------------------------

def _adj_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _two_color(n, adj):
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
                elif col[v] == col[u]:
                    return None
    return col


def _bad_count(n, adj, D):
    """Number of unordered pairs at distance > D (bitset balls)."""
    reach = [1 << v for v in range(n)]
    nb = [list(s) for s in adj]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in nb[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _grow(n, edges, d, D, rng, deadline):
    """Try to add two vertices to a d-regular bipartite diameter-D graph; return (n+2, edges) or None."""
    adj = _adj_sets(n, edges)
    if any(len(s) != d for s in adj):
        return None
    col = _two_color(n, adj)
    if col is None:
        return None
    E = [(u, v) if col[u] == 0 else (v, u) for u, v in edges]  # (A-vertex, B-vertex)

    # Choose a matching of d edges with distinct A- and B-endpoints.
    chosen = None
    for _ in range(300):
        idx = rng.sample(range(len(E)), d)
        xs = [E[i][0] for i in idx]
        ys = [E[i][1] for i in idx]
        if len(set(xs)) == d and len(set(ys)) == d:
            chosen = (idx, xs, ys)
            break
    if chosen is None:
        return None
    idx, xs, ys = chosen

    drop = set(idx)
    E = [e for i, e in enumerate(E) if i not in drop]
    for x, y in zip(xs, ys):
        adj[x].discard(y)
        adj[y].discard(x)

    a, b = n, n + 1
    adj.append(set())
    adj.append(set())
    nn = n + 2
    for y in ys:
        adj[a].add(y)
        adj[y].add(a)
        E.append((a, y))
    for x in xs:
        adj[x].add(b)
        adj[b].add(x)
        E.append((x, b))

    cur = _bad_count(nn, adj, D)
    start = time.monotonic()
    total = max(1e-3, deadline - start)
    m = len(E)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - start) / total
        T = 2.0 * (1.0 - frac) + 0.05
        i, j = rng.randrange(m), rng.randrange(m)
        if i == j:
            continue
        x1, y1 = E[i]
        x2, y2 = E[j]
        if x1 == x2 or y1 == y2:
            continue
        if y2 in adj[x1] or y1 in adj[x2]:
            continue
        adj[x1].discard(y1); adj[y1].discard(x1)
        adj[x2].discard(y2); adj[y2].discard(x2)
        adj[x1].add(y2); adj[y2].add(x1)
        adj[x2].add(y1); adj[y1].add(x2)
        new = _bad_count(nn, adj, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            E[i] = (x1, y2)
            E[j] = (x2, y1)
            cur = new
        else:
            adj[x1].discard(y2); adj[y2].discard(x1)
            adj[x2].discard(y1); adj[y1].discard(x2)
            adj[x1].add(y1); adj[y1].add(x1)
            adj[x2].add(y2); adj[y2].add(x2)

    out = [(u, v) for u in range(nn) for v in adj[u] if u < v]
    return nn, out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.85 * time_limit - 2.0)
    deadline = start + total
    rng = random.Random(seed)

    best = _fallback(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Only diameter 3 is searched; other regimes use the baseline.
    if D != 3 or d < 3:
        return best

    # Moore-extremal case: incidence graph of PG(2, d-1).
    if lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best

    # Araujo-Pardo & Lopez record family for d = q + 2.
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Difference-cover Haar lifts, given a share of the budget.
    haar_deadline = start + 0.4 * total
    hi = d * (d - 1) + 1
    lo = best_n // 2 + 1
    for N in range(max(lo, d), hi + 1):
        if time.monotonic() >= haar_deadline:
            break
        groups = _group_list(N, rng)
        tables = [None] * len(groups)
        found = None
        deadline_N = time.monotonic() + 0.5 * max(0.0, haar_deadline - time.monotonic())
        while found is None and time.monotonic() < deadline_N:
            for idx in range(len(groups)):
                if time.monotonic() >= deadline_N:
                    break
                if tables[idx] is None:
                    mul, inv = groups[idx][1], groups[idx][2]
                    tables[idx] = _ratio_table(N, mul, inv)
                R = tables[idx]
                S = _anneal(N, R, d, rng, 6000, R[0][0])
                if S is not None:
                    found = (idx, S)
                    break
        if found is None:
            break
        idx, S = found
        mul = groups[idx][1]
        n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
        consider(n, edges)

    # Vertex-pair growth by edge switching on the best regular graph found.
    cur_n, cur_e = best
    while time.monotonic() < deadline:
        res = _grow(cur_n, cur_e, d, D, rng, deadline)
        if res is None:
            break
        n2, e2 = res
        if not lib.is_valid(n2, e2, d, D):
            break
        cur_n, cur_e = n2, e2
        consider(n2, e2)

    return best
