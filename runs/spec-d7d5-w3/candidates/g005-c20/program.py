import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline family.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Slack extension: add new vertices using spare degree (exact ball-cover test).
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Return the 2-colouring of the graph, or None if it is not bipartite."""
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
                elif color[v] == color[u]:
                    return None
    return color


def _radius_balls(n, adj, radius):
    """Bitmask per vertex: bit x set when x is within distance `radius` of the vertex."""
    reach = [1 << v for v in range(n)]
    for _ in range(radius):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices using spare degree; returns (n, edges), always valid."""
    edges = [tuple(e) for e in edges]
    adj = [list(a) for a in lib.adjacency(n, edges)]
    color = _bipartition(n, adj)
    if color is None or D < 2:
        return n, edges
    deg = [len(a) for a in adj]
    radius = D - 1

    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        ball = _radius_balls(n, adj, radius)
        full = (1 << n) - 1
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            accepted = False
            for _ in range(4000):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                cover = 0
                for v in pick:
                    cover |= ball[v]
                if cover != full:
                    continue
                w = n
                edges.extend((v, w) for v in pick)
                adj.append(list(pick))
                for v in pick:
                    adj[v].append(w)
                    deg[v] += 1
                n += 1
                color.append(1 - side)
                deg.append(d)
                spare = [v for v in spare if deg[v] < d]
                grew = True
                accepted = True
                ball = _radius_balls(n, adj, radius)
                full = (1 << n) - 1
            if accepted:
                grew = True
    return n, edges


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l pairs A_i with B_{layers[l][i]} through voltage s: A_{i,g} ~ B_{p,g*s}.
#
# Moves: voltage move (defect-targeted or uniform), layer swap, and
# NEW voltage-pair swap (exchanges the voltages of one base vertex between two
# layers, keeping the layer permutations). The search is an iterated local
# search: each run returns its best state, and later runs for the same base
# size k restart from a perturbed copy of that elite state (same group).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e))."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = g*s
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b set when representative block b is within distance D."""
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _unreached(k, N, reach):
    """Number of unreached (representative, vertex) pairs."""
    return 2 * k * N - int(_POP[reach].sum())


def _metro(c2, cost, temp, rng):
    """Metropolis acceptance."""
    return c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp)


def _perturb(state, rng, d, k, G):
    """Elite restart kick: re-draw a few voltages (and occasionally swap one layer pair)."""
    layers = [list(x) for x in state[0]]
    S = [list(x) for x in state[1]]
    for _ in range(rng.randint(2, 4)):
        S[rng.randrange(d)][rng.randrange(k)] = rng.randrange(G)
    if k >= 2 and rng.random() < 0.3:
        l = rng.randrange(d)
        i1, i2 = rng.sample(range(k), 2)
        layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
    return layers, S


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience, init=None):
    """Simulated annealing with stagnation stop.

    Returns ((n, edges), 0, None) on success, else (None, best_cost, best_state).
    """
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    if init is None:
        layers = [rng.sample(range(k), k) for _ in range(d)]
        S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    else:
        layers = [list(x) for x in init[0]]
        S = [list(x) for x in init[1]]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    def refresh(l, i):
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def snapshot():
        return [list(x) for x in layers], [list(x) for x in S]

    reach = _reach(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))
    best_cost = cost
    best_state = snapshot()
    last_improve = 0

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last_improve > patience:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.2:
            # Layer-swap move: exchange B-targets of two A-blocks in one layer.
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            refresh(l, i1)
            refresh(l, i2)
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if _metro(c2, cost, temp, rng):
                cost, reach = c2, r2
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                refresh(l, i1)
                refresh(l, i2)

        elif d >= 2 and x < 0.35:
            # NEW: voltage-pair swap between two layers for one base vertex.
            i = rng.randrange(k)
            l1, l2 = rng.sample(range(d), 2)
            S[l1][i], S[l2][i] = S[l2][i], S[l1][i]
            refresh(l1, i)
            refresh(l2, i)
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if _metro(c2, cost, temp, rng):
                cost, reach = c2, r2
            else:
                S[l1][i], S[l2][i] = S[l2][i], S[l1][i]
                refresh(l1, i)
                refresh(l2, i)

        else:
            # Voltage move: defect-targeted with probability 0.4, otherwise uniform.
            bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else None
            if bad is not None and bad.size:
                u = int(bad[rng.randrange(bad.size)])
                block = u // G
                l = rng.randrange(d)
                i = block if block < k else layers[l].index(block - k)
            else:
                l = rng.randrange(d)
                i = rng.randrange(k)
            old = S[l][i]
            new = rng.randrange(G)
            if new == old:
                continue
            S[l][i] = new
            refresh(l, i)
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if _metro(c2, cost, temp, rng):
                cost, reach = c2, r2
            else:
                S[l][i] = old
                refresh(l, i)

        if cost < best_cost:
            best_cost, last_improve = cost, t
            best_state = snapshot()

    if cost == 0:
        edges = set()
        for u in range(k * G):
            for v in nbr[:, u]:
                edges.add((u, int(v)))
        return (N, sorted(edges)), 0, None
    return None, best_cost, best_state


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, time_limit - 5.0)
    deadline = start + budget
    final_deadline = start + max(1.0, time_limit - 2.5)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
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
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    elite = {}  # k -> (cost, m, k2, r, state)

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k = pick_k()
        init = None
        grp = None

        # Elite restart: reuse the group and perturb the best state found for this k.
        if k in elite and rng.random() < 0.6:
            _, e_m, e_k2, e_r, e_state = elite[k]
            if 2 * k * e_m * e_k2 > best_n:
                grp = (e_m, e_k2, e_r)
                init = _perturb(e_state, rng, d, k, e_m * e_k2)

        if grp is None:
            base = best_n // (2 * k)
            target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
            g = _sample_group(target, rng)
            if g is None:
                continue
            if 2 * k * g[0] * g[1] <= best_n:
                continue
            grp = g

        m, k2, r = grp
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        trials[k] += 1
        res, cost, state = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000, 1200, init)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])
        elif state is not None and (k not in elite or cost < elite[k][0]):
            elite[k] = (cost, m, k2, r, state)

    # Use spare degree in the best graph to add vertices (exact, fast check).
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
