import itertools
import random
import time

import numpy as np

import lib


def _parent(d, D, seed, time_limit):
    """Previous Haar-graph search, kept as the last-resort fallback."""
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))  # complete bipartite K_{d,d}: always valid
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


def _largest_pp(d):
    """Largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _gq_incidence(q):
    """Incidence graph of the generalized quadrangle W(q): points of PG(3,q) vs totally
    isotropic lines of the symplectic form. Order 2(q+1)(q^2+1), degree q+1, diameter 4.
    Returns (n, edges, N) where N is the number of points (vertices 0..N-1 are points)."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    N = len(pts)
    idx = {v: i for i, v in enumerate(pts)}
    P = np.array(pts, dtype=np.int64)
    C = [P[:, k] for k in range(4)]
    add, mul = F.add_table, F.mul_table
    neg = np.array([F.neg(x) for x in range(q)], dtype=np.int64)
    # Symplectic form B(x, y) = x0 y1 - x1 y0 + x2 y3 - x3 y2.
    t1 = mul[C[0][:, None], C[1][None, :]]
    t2 = mul[C[1][:, None], C[0][None, :]]
    t3 = mul[C[2][:, None], C[3][None, :]]
    t4 = mul[C[3][:, None], C[2][None, :]]
    s1 = add[t1, neg[t2]]
    s2 = add[t3, neg[t4]]
    B = add[s1, s2]
    cov = ~(B == 0)          # non-isotropic pairs are never on a common line
    np.fill_diagonal(cov, True)

    def norm_index(v):
        c = next(x for x in v if x)
        ci = F.inv(c)
        return idx[tuple(F.mul(ci, x) for x in v)]

    lines = []
    for i in range(N):
        for j in np.nonzero(~cov[i])[0]:
            j = int(j)
            if cov[i, j]:
                continue
            pi, pj = pts[i], pts[j]
            L = {i}
            for c in range(q):
                v = tuple(F.add(pj[t], F.mul(c, pi[t])) for t in range(4))
                L.add(norm_index(v))
            L = sorted(L)
            lines.append(L)
            cov[np.ix_(L, L)] = True
    edges = [(p, N + k) for k, L in enumerate(lines) for p in L]
    return N + len(lines), edges, N


def _balls3(n, adj):
    """R3[v] = bitmask of all vertices within distance 3 of v."""
    bits = [1 << v for v in range(n)]
    R1 = [0] * n
    for v in range(n):
        r = bits[v]
        for u in adj[v]:
            r |= bits[u]
        R1[v] = r
    R2 = [0] * n
    for v in range(n):
        r = R1[v]
        for u in adj[v]:
            r |= R1[u]
        R2[v] = r
    R3 = [0] * n
    for v in range(n):
        r = R2[v]
        for u in adj[v]:
            r |= R2[u]
        R3[v] = r
    return R3


def _extend(n, edges, side, d, deadline, rng):
    """Greedily add vertices. A new vertex w on side s joins vertices of the other side
    (with spare degree) whose radius-3 balls cover every existing vertex. Existing pairs
    keep their distances, so the diameter invariant is preserved."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    edges = list(edges)
    fails = 0
    while fails < 40 and time.monotonic() < deadline:
        R3 = _balls3(n, adj)
        full = (1 << n) - 1
        added = False
        order = [0, 1]
        rng.shuffle(order)
        for s in order:
            cand = [u for u in range(n) if side[u] != s and len(adj[u]) < d]
            covered = 0
            chosen = []
            taken = set()
            while covered != full and len(chosen) < d:
                best_gain, best = 0, []
                for u in cand:
                    if u in taken:
                        continue
                    g = (R3[u] & ~covered).bit_count()
                    if g > best_gain:
                        best_gain, best = g, [u]
                    elif g and g == best_gain:
                        best.append(u)
                if best_gain == 0:
                    break
                pick = rng.choice(best)
                chosen.append(pick)
                taken.add(pick)
                covered |= R3[pick]
            if covered == full:
                w = n
                n += 1
                adj.append(list(chosen))
                side.append(s)
                for u in chosen:
                    adj[u].append(w)
                    edges.append((u, w))
                added = True
                break
            if time.monotonic() >= deadline:
                break
        fails = 0 if added else fails + 1
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.6 * time_limit
    rng = random.Random(seed)

    if D == 4:
        q = _largest_pp(d)
        if q is not None:
            try:
                n0, e0, N = _gq_incidence(q)
                if lib.is_valid(n0, e0, d, D):
                    try:
                        side = [0] * N + [1] * (n0 - N)
                        n1, e1 = _extend(n0, e0, side, d, deadline, rng)
                        if n1 > n0 and lib.is_valid(n1, e1, d, D):
                            return n1, e1
                    except Exception:
                        pass
                    return n0, e0
            except Exception:
                pass

    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    return _parent(d, D, seed, time_limit)
