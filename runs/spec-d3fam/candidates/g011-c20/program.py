import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Base constructions (all valid for the given D; checked with lib.is_valid).
# ----------------------------------------------------------------------------

def _largest_pp_at_most(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _base_candidates(d, D):
    out = []
    # K_{d,d}: diameter 2, Moore-optimal for D = 2. Safe fallback.
    out.append(lib.haar_graph(d, range(d)))
    if d == 2 and D >= 2:
        m = 2 * D
        out.append((m, [(i, (i + 1) % m) for i in range(m)]))  # C_{2D}
    if D >= 3:
        if d - 1 >= 2 and lib.is_prime_power(d - 1):
            out.append(lib.projective_plane_incidence(d - 1))   # Moore graph
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                out.append(lib.araujo_lopez_graph(d - 2))       # record family
            except (ValueError, KeyError, StopIteration):
                pass
        q = _largest_pp_at_most(d - 1)
        if q is not None and q >= 2:
            out.append(lib.projective_plane_incidence(q))       # degree q+1 <= d
    return out


# ----------------------------------------------------------------------------
# Bold change: grow by vertex pairs and repair with annealing.
#
# Instead of extending by cover sets, each step adds one vertex a on side A and
# one vertex b on side B. Degree is kept within d by linking a and b to spare
# slots, and by "splitting" saturated edges: an existing edge (x, w) is replaced
# by (a, w) and (x, b). The result is then repaired by simulated annealing that
# uses degree-preserving double-edge switches and additions between spare
# slots. The cost is the number of ordered vertex pairs at distance > D,
# computed with dense matrix powers of (I + A). Only fully valid graphs are
# kept, so the fallback always remains.
# ----------------------------------------------------------------------------

def _color(n, E):
    adj = [[] for _ in range(n)]
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
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


def _add_pair(n, E, color, d, rng):
    nbr = [set() for _ in range(n + 2)]
    for u, v in E:
        nbr[u].add(v)
        nbr[v].add(u)
    col = list(color) + [0, 1]
    a, b = n, n + 1

    def link(x, y):
        nbr[x].add(y)
        nbr[y].add(x)

    # Fill spare slots of the new vertices from deficient opposite vertices.
    defB = [v for v in range(n) if col[v] == 1 and len(nbr[v]) < d]
    rng.shuffle(defB)
    for v in defB[:d]:
        link(a, v)
    defA = [v for v in range(n) if col[v] == 0 and len(nbr[v]) < d]
    rng.shuffle(defA)
    for v in defA[:d]:
        link(b, v)

    # Split: steal edges (x, w) from saturated B vertices w, giving (a, w) and (x, b).
    fullB = [v for v in range(n) if col[v] == 1 and len(nbr[v]) >= d]
    used = []
    tries = 0
    while len(nbr[a]) < d and fullB and tries < 50 * d:
        tries += 1
        w = rng.choice(fullB)
        if w in nbr[a] or len(nbr[w]) < d:
            continue
        opts = [x for x in nbr[w] if x not in nbr[b] and x not in used]
        if not opts:
            continue
        x = rng.choice(opts)
        nbr[x].discard(w)
        nbr[w].discard(x)
        link(a, w)
        used.append(x)
    for x in used:
        if len(nbr[b]) < d and len(nbr[x]) < d and x not in nbr[b]:
            link(b, x)

    E2 = [(u, v) for u in range(n + 2) if col[u] == 0 for v in nbr[u]]
    return n + 2, E2, col


def _bad(M, D):
    """Ordered pairs at distance > D, where M = I + A."""
    P = M
    for _ in range(D - 1):
        P = P @ M
    n = M.shape[0]
    return n * n - int(np.count_nonzero(P))


def _setedge(A, M, x, y, val):
    A[x, y] = val
    A[y, x] = val
    M[x, y] = val
    M[y, x] = val


def _repair(n, E, color, d, D, deadline, rng):
    A = np.zeros((n, n), dtype=np.float32)
    Ed = []
    deg = [0] * n
    for u, v in E:
        if color[u] == 1:
            u, v = v, u
        Ed.append([u, v])
        A[u, v] = 1
        A[v, u] = 1
        deg[u] += 1
        deg[v] += 1
    M = A + np.eye(n, dtype=np.float32)
    Aside = [v for v in range(n) if color[v] == 0]
    Bside = [v for v in range(n) if color[v] == 1]

    cost = _bad(M, D)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    T0 = 2.0
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - t0) / span
        T = T0 * (1.0 - frac) + 0.05

        # Add an edge between two deficient opposite vertices (never hurts).
        if rng.random() < 0.3:
            defA = [v for v in Aside if deg[v] < d]
            defB = [v for v in Bside if deg[v] < d]
            if defA and defB:
                a = rng.choice(defA)
                b = rng.choice(defB)
                if A[a, b] == 0:
                    _setedge(A, M, a, b, 1)
                    deg[a] += 1
                    deg[b] += 1
                    Ed.append([a, b])
                    cost = _bad(M, D)
                    continue

        # Degree-preserving double-edge switch.
        if len(Ed) < 2:
            return None
        i = rng.randrange(len(Ed))
        j = rng.randrange(len(Ed))
        if i == j:
            continue
        a, b = Ed[i]
        c, e = Ed[j]
        if a == c or b == e or A[a, e] != 0 or A[c, b] != 0:
            continue
        _setedge(A, M, a, b, 0)
        _setedge(A, M, c, e, 0)
        _setedge(A, M, a, e, 1)
        _setedge(A, M, c, b, 1)
        cost2 = _bad(M, D)
        delta = cost2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = cost2
            Ed[i] = [a, e]
            Ed[j] = [c, b]
        else:
            _setedge(A, M, a, e, 0)
            _setedge(A, M, c, b, 0)
            _setedge(A, M, a, b, 1)
            _setedge(A, M, c, e, 1)

    return [(int(u), int(v)) for u, v in Ed]


def _extend(base_n, base_E, d, D, deadline, rng):
    cur_n, cur_E = base_n, list(base_E)
    cur_color = _color(cur_n, cur_E)
    best = (cur_n, cur_E)
    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0.5:
            break
        budget = max(2.0, 0.35 * remaining)
        att_deadline = min(deadline, now + budget)
        n2, E2, c2 = _add_pair(cur_n, cur_E, cur_color, d, rng)
        res = _repair(n2, E2, c2, d, D, att_deadline, rng)
        if res is not None and lib.is_valid(n2, res, d, D):
            cur_n, cur_E, cur_color = n2, res, c2
            best = (cur_n, cur_E)
    return best


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 2.0)
    rng = random.Random(seed)

    if d < 1 or D < 0:
        return 1, []
    if D == 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = None
    best_n = 0
    for n_c, e_c in _base_candidates(d, D):
        if n_c > best_n and lib.is_valid(n_c, e_c, d, D):
            best = (n_c, e_c)
            best_n = n_c
    if best is None:
        best = lib.haar_graph(d, range(d))
        best_n = best[0]

    moore = lib._moore_bound(d, D)
    if D >= 3 and d >= 3 and D <= 6 and best_n < moore and best_n <= 1200:
        try:
            ext = _extend(best[0], best[1], d, D, deadline, rng)
            if ext[0] > best_n and lib.is_valid(ext[0], ext[1], d, D):
                best = ext
                best_n = ext[0]
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
