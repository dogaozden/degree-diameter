import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases: projective plane (D = 3) and generalized quadrangle W(q) (D >= 4).
# ----------------------------------------------------------------------------

def _pg_base(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4, degree q+1."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


# ----------------------------------------------------------------------------
# New construction: deletion search inside a large generalized quadrangle.
# Start from W(q) with degree q+1 > d and look for a large INDUCED subgraph
# with max degree <= d and diameter <= D. State is a kept-vertex mask;
# descend by removing the vertices involved in most violations, then add
# vertices back where the cost stays zero. Iterated local search on top.
# ----------------------------------------------------------------------------

def _deletion_search(n, edges, d, D, deadline, rng):
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)

    def evaluate(K):
        verts = [v for v in range(n) if K[v]]
        m = len(verts)
        nbr = [None] * n
        viol = 0
        for v in verts:
            nb = [u for u in adj[v] if K[u]]
            nbr[v] = nb
            if len(nb) > d:
                viol += len(nb) - d
        reach = [0] * n
        for v in verts:
            reach[v] = 1 << v
        for _ in range(D):
            new = [0] * n
            for v in verts:
                r = reach[v]
                for u in nbr[v]:
                    r |= reach[u]
                new[v] = r
            reach = new  # synchronous update keeps the radius exact
        bad = [0] * n
        total = 0
        for v in verts:
            b = m - reach[v].bit_count()
            bad[v] = b
            total += b
        return total // 2 + 1000 * viol, bad, nbr

    best_K, best_size = None, 0
    cur_valid = None
    base_K = [True] * n

    while time.monotonic() < deadline:
        K = base_K[:]
        cost, bad, nbr = evaluate(K)

        # Descend: remove the worst vertices until the induced graph is valid.
        while cost > 0 and time.monotonic() < deadline:
            cand = []
            for v in range(n):
                if K[v]:
                    ex = len(nbr[v]) - d
                    s = bad[v] + (1000 * ex if ex > 0 else 0) + rng.random()
                    cand.append((s, v))
            cand.sort(reverse=True)
            kill = 1 if cost < 20 else max(1, len(cand) // 50)
            for _, v in cand[:kill]:
                K[v] = False
            cost, bad, nbr = evaluate(K)

        if cost == 0 and time.monotonic() < deadline:
            # Add back removed vertices while validity holds.
            outs = [v for v in range(n) if not K[v]]
            rng.shuffle(outs)
            for v in outs[:80]:
                if time.monotonic() >= deadline:
                    break
                K[v] = True
                c2, b2, n2 = evaluate(K)
                if c2 == 0:
                    cost, bad, nbr = c2, b2, n2
                else:
                    K[v] = False

            size = sum(K)
            cur_valid = K[:]
            if size > best_size:
                best_size = size
                best_K = K[:]

        # Next start: current valid state or best, with a small random kick.
        if cur_valid is not None and rng.random() < 0.5:
            src = cur_valid
        elif best_K is not None:
            src = best_K
        else:
            src = [True] * n
        base_K = src[:]
        kept = [v for v in range(n) if base_K[v]]
        if kept:
            for v in rng.sample(kept, min(len(kept), rng.randint(1, 8))):
                base_K[v] = False

    if best_K is None:
        return None
    idx = {}
    for v in range(n):
        if best_K[v]:
            idx[v] = len(idx)
    E = [(idx[u], idx[v]) for u, v in edges if best_K[u] and best_K[v]]
    return len(idx), E


# ----------------------------------------------------------------------------
# Main driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    if D == 2:
        return best

    if D == 3:
        pg = _pg_base(d)
        if pg is not None:
            consider(pg[0], pg[1])
        return best if lib.is_valid(best[0], best[1], d, D) else lib.haar_graph(d, range(d))

    # D >= 4: generalized quadrangle bases.
    # Safe base: W(q) with q + 1 <= d (diameter 4, no deletion needed).
    small = [q for q in range(8, 1, -1) if lib.is_prime_power(q) and q + 1 <= d]
    if small:
        gq = _gq_w(small[0])
        consider(gq[0], gq[1])

    # Bold base: W(q) with q + 1 > d, then search for a large induced subgraph.
    big = [q for q in range(2, 9) if lib.is_prime_power(q) and q + 1 > d][:2]
    for i, q in enumerate(big):
        now = time.monotonic()
        if now >= deadline:
            break
        share = (deadline - now) / (len(big) - i)
        n0, e0 = _gq_w(q)
        res = _deletion_search(n0, e0, d, D, time.monotonic() + share, rng)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
