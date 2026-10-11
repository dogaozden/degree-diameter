import math
import random
import time

import lib

TIME_FRAC = 0.85      # fraction of time_limit used before returning
MARGIN = 2.0          # seconds kept in reserve
VOLT_SHARE = 0.55     # share of usable time given to the voltage-lift search
VOLT_STEPS = 1500     # annealing steps per voltage attempt
VOLT_FAILS = 4        # failed attempts before a group order k is dropped
ITER = 1500           # growth: annealing steps per attempt
MAX_FAILS = 8         # growth: consecutive failed attempts before stopping


# ---------------------------------------------------------------- shared helpers

def _two_colour(n, edges):
    """Proper 2-colouring of a bipartite graph, component by component."""
    adj = lib.adjacency(n, edges)
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


def _balls_adj(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    reach = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        if new == reach:
            break
        reach = new
    return reach


def _bad_pairs(n, adj, D):
    """Number of unordered pairs at distance > D (unreachable counts)."""
    reach = _balls_adj(n, adj, D)
    return sum(n - r.bit_count() for r in reach) // 2


def _edges(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


# ---------------------------------------------------------------- voltage-lift search
# A bipartite lift: base has k A-vertices and k B-vertices; each base dart (i, j)
# carries a voltage in Z_m. Lift vertices are (A_i, g) -> i*m+g and (B_j, h) -> (k+j)*m+h,
# and dart (i, j, a) joins (A_i, g) to (B_j, g+a). The cyclic action g -> g+1 is an
# automorphism, so the diameter condition only needs balls around the 2k orbit
# representatives. The cost is m times the number of (rep, far vertex) pairs.

def _lift_adj(k, m, darts, volt):
    n = 2 * k * m
    adj = [set() for _ in range(n)]
    for t, (i, j) in enumerate(darts):
        a = volt[t]
        xa = i * m
        yb = (k + j) * m
        for g in range(m):
            x = xa + g
            y = yb + (g + a) % m
            adj[x].add(y)
            adj[y].add(x)
    return n, adj


def _ball_size(adj, s, R):
    seen = {s}
    frontier = [s]
    for _ in range(R):
        nxt = []
        for v in frontier:
            for u in adj[v]:
                if u not in seen:
                    seen.add(u)
                    nxt.append(u)
        if not nxt:
            break
        frontier = nxt
    return len(seen)


def _lift_cost(k, m, darts, volt, R):
    n, adj = _lift_adj(k, m, darts, volt)
    reps = [i * m for i in range(k)] + [(k + j) * m for j in range(k)]
    bad = 0
    for r in reps:
        bad += n - _ball_size(adj, r, R)
    return bad * m, n, adj


def _volt_attempt(k, m, darts, R, rng, deadline):
    """Anneal voltages until the lift has diameter <= R. Returns (n, edges) or None."""
    T = len(darts)
    volt = [rng.randrange(m) for _ in range(T)]
    cost, n, adj = _lift_cost(k, m, darts, volt, R)
    for it in range(VOLT_STEPS):
        if cost == 0:
            break
        if time.monotonic() > deadline:
            return None
        t = rng.randrange(T)
        old = volt[t]
        volt[t] = rng.randrange(m)
        if volt[t] == old:
            continue
        new, n2, adj2 = _lift_cost(k, m, darts, volt, R)
        delta_units = (new - cost) / m
        temp = 1.0 * (1.0 - it / VOLT_STEPS) + 0.05
        if delta_units <= 0 or rng.random() < math.exp(-delta_units / temp):
            cost, n, adj = new, n2, adj2
        else:
            volt[t] = old
    if cost != 0:
        return None
    return n, [(u, v) for u in range(n) for v in adj[u] if u < v]


def _voltage_search(d, D, base_n, end, rng):
    """Round-robin over group orders k; returns verified-by-construction lifts (diam <= D)."""
    out = []
    moore = lib._moore_bound(d, D)
    ks = [k for k in (1, 2, 3, 4) if k <= d]
    st = {k: [max(2, base_n // (2 * k) + 1), 0] for k in ks}   # [next m, fail count]
    active = list(ks)
    while active and time.monotonic() < end:
        for k in list(active):
            if time.monotonic() >= end:
                break
            m = st[k][0]
            if 2 * k * m > moore:
                active.remove(k)
                continue
            darts = [(i, (i + s) % k) for i in range(k) for s in range(d)]
            res = _volt_attempt(k, m, darts, D, rng, end)
            if res is None:
                st[k][1] += 1
                if st[k][1] >= VOLT_FAILS:
                    active.remove(k)
                continue
            out.append(res)
            st[k][0] = m + 1
            st[k][1] = 0
            base_n = max(base_n, res[0])
            for kk in st:
                st[kk][0] = max(st[kk][0], base_n // (2 * kk) + 1)
    return out


# ---------------------------------------------------------------- growth search (parent method)

def _pick_neighbours(n, adj, color, c, d, D, rng):
    """Choose d vertices of colour 1-c, greedily covering radius-(D-1) balls."""
    other = [v for v in range(n) if color[v] == 1 - c]
    if len(other) < d:
        return None
    balls = _balls_adj(n, adj, D - 1)
    full = (1 << n) - 1
    covered, chosen = 0, []
    cand = other[:]
    rng.shuffle(cand)
    while covered != full and len(chosen) < d and cand:
        best_u, best_g = -1, 0
        for u in cand:
            g = (balls[u] & ~covered).bit_count()
            if g > best_g:
                best_u, best_g = u, g
        if best_u < 0:
            break
        chosen.append(best_u)
        covered |= balls[best_u]
        cand.remove(best_u)
    chosen_set = set(chosen)
    rest = [v for v in other if v not in chosen_set]
    rng.shuffle(rest)
    chosen += rest[:d - len(chosen)]
    return chosen


def _swap(adj, side0, rng):
    """Degree-preserving double-edge swap keeping bipartiteness. Returns undo info or None."""
    a1 = rng.choice(side0)
    if not adj[a1]:
        return None
    b1 = rng.choice(tuple(adj[a1]))
    a2 = rng.choice(side0)
    if a2 == a1 or not adj[a2]:
        return None
    b2 = rng.choice(tuple(adj[a2]))
    if b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
        return None
    adj[a1].remove(b1); adj[b1].remove(a1)
    adj[a2].remove(b2); adj[b2].remove(a2)
    adj[a1].add(b2); adj[b2].add(a1)
    adj[a2].add(b1); adj[b1].add(a2)
    return (a1, b1, a2, b2)


def _unswap(adj, mv):
    a1, b1, a2, b2 = mv
    adj[a1].remove(b2); adj[b2].remove(a1)
    adj[a2].remove(b1); adj[b1].remove(a2)
    adj[a1].add(b1); adj[b1].add(a1)
    adj[a2].add(b2); adj[b2].add(a2)


def _augment(n, adj, color, d, rng):
    """Add edges between deficient opposite-colour vertices. Never breaks the diameter bound."""
    d0 = [u for u in range(n) if color[u] == 0 and len(adj[u]) < d]
    d1 = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    if not d0 or not d1:
        return
    rng.shuffle(d0)
    for u in d0:
        if len(adj[u]) >= d:
            continue
        for v in d1:
            if len(adj[v]) < d and v not in adj[u]:
                adj[u].add(v)
                adj[v].add(u)
                if len(adj[u]) >= d:
                    break


def _attempt(n, adj, color, d, D, rng, deadline):
    """Add one vertex and anneal until the diameter bound holds again. Returns new state or None."""
    adj = [set(s) for s in adj]
    color = list(color)
    c = rng.randrange(2)
    nb = _pick_neighbours(n, adj, color, c, d, D, rng)
    if nb is None:
        return None
    for u in nb:
        if len(adj[u]) >= d:
            w = rng.choice(tuple(adj[u]))
            adj[u].discard(w)
            adj[w].discard(u)
    x = n
    adj.append(set())
    color.append(c)
    n += 1
    for u in nb:
        adj[x].add(u)
        adj[u].add(x)

    side0 = [v for v in range(n) if color[v] == 0]
    cost = _bad_pairs(n, adj, D)
    for it in range(ITER):
        if cost == 0:
            break
        if time.monotonic() > deadline:
            return None
        mv = _swap(adj, side0, rng)
        if mv is None:
            continue
        new = _bad_pairs(n, adj, D)
        delta = new - cost
        temp = 1.5 * (1.0 - it / ITER) + 0.05
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            cost = new
        else:
            _unswap(adj, mv)
    if cost != 0:
        return None
    _augment(n, adj, color, d, rng)
    return n, adj, color


def _grow(base_n, base_e, d, D, rng, deadline):
    """Grow from a valid base by repeated local annealing. Returns the best (n, edges) found."""
    color = _two_colour(base_n, base_e)
    adj = [set() for _ in range(base_n)]
    for u, v in base_e:
        adj[u].add(v)
        adj[v].add(u)
    cur_n, cur_adj, cur_col = base_n, adj, color
    best_n, best_e = base_n, base_e
    fails = 0
    while time.monotonic() < deadline and fails < MAX_FAILS:
        res = _attempt(cur_n, cur_adj, cur_col, d, D, rng, deadline)
        if res is None:
            fails += 1
            continue
        fails = 0
        cur_n, cur_adj, cur_col = res
        if cur_n > best_n:
            best_n, best_e = cur_n, _edges(cur_n, cur_adj)
    return best_n, best_e


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    usable = max(0.5, TIME_FRAC * time_limit - MARGIN)
    deadline = start + usable
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:                       # cycle of length 2D: bipartite, diameter D
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:                       # K_{d,d} is extremal for D = 2
        return lib.haar_graph(d, range(d))
    if D == 3 and lib.is_prime_power(d - 1):   # Moore-extremal projective plane
        return lib.projective_plane_incidence(d - 1)

    # Safe fallback: K_{d,d} is always valid here.
    kdd = lib.haar_graph(d, range(d))
    bases = [kdd]
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            bases.append(lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    pg = _pg_base(d)
    if pg is not None:
        bases.append(pg)

    cands = []
    for n, e in bases:
        if lib.is_valid(n, e, d, D):
            cands.append((n, e))
    if not cands:
        return kdd

    # Phase A: voltage-lift search (a different construction from growth).
    base_n = max(n for n, _ in cands)
    volt_end = start + VOLT_SHARE * usable
    cands.extend(_voltage_search(d, D, base_n, min(volt_end, deadline), rng))

    # Phase B: growth from the largest candidate found so far.
    best_n, best_e = max(cands, key=lambda c: c[0])
    if time.monotonic() < deadline:
        gn, ge = _grow(best_n, best_e, d, D, rng, deadline)
        if gn > best_n:
            cands.append((gn, ge))

    # Final verification: take the largest candidate that passes the exact check.
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            return n, e
    return kdd

