import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# High-risk experiment for D >= 4, d = q (prime power): start from the incidence
# graph of the generalized quadrangle W(q), whose degree is q+1 = d+1 and whose
# diameter is 4, then delete vertices by simulated annealing until the induced
# subgraph has max degree <= d and diameter <= D. Valid by construction, and
# every candidate is re-checked with lib.is_valid before it is accepted.
#
# Fallbacks (always valid): K_{d,d} for D = 2, even cycles for d = 2, PG(2,q)
# for D = 3, and W(q) with q + 1 <= d for D >= 4. Nothing is returned unless it
# passes lib.is_valid.
#
# Risk: this is a different construction from the previous program. It may
# reach fewer vertices than the previous program's 358 on d=7 D=4.
# ----------------------------------------------------------------------------


def _largest_pp(m):
    """Largest prime power q with 2 <= q <= m, or None."""
    for q in range(m, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _gq_w(q):
    """Incidence graph of points and totally isotropic lines of W(q); 2(q+1)(q^2+1) vertices, diameter 4."""
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
    edges = []
    line_id = 0
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
            for p in L:
                edges.append((p, P + line_id))
            line_id += 1
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))
    return 2 * P, edges


def _anneal_delete(n, e0, d, D, deadline, rng, consider):
    """Anneal over vertex subsets of a base graph, keeping induced subgraphs with
    max degree <= d and diameter <= D. Energy = bad pairs + penalty*excess degree
    - kept vertices. The best feasible subset found is passed to consider()."""
    adj = [[] for _ in range(n)]
    for u, v in e0:
        adj[u].append(v)
        adj[v].append(u)
    alive = [True] * n
    WV, ALPHA = 2.0, 1.0

    def evaluate():
        verts = [v for v in range(n) if alive[v]]
        K = len(verts)
        aadj = [None] * n
        viol = 0
        vl = []
        for v in verts:
            nb = [u for u in adj[v] if alive[u]]
            aadj[v] = nb
            if len(nb) > d:
                viol += len(nb) - d
                vl.append(v)
        reach = [0] * n
        for v in verts:
            reach[v] = 1 << v
        for _ in range(D):
            new = [0] * n
            for v in verts:
                x = reach[v]
                for u in aadj[v]:
                    x |= reach[u]
                new[v] = x
            reach = new
        bad2 = 0
        for v in verts:
            bad2 += K - reach[v].bit_count()
        bad = bad2 // 2
        return bad + WV * viol - ALPHA * K, bad, viol, K, vl

    E, bad, viol, K, vl = evaluate()
    # Greedy start: remove violating vertices until max degree <= d.
    while viol > 0 and time.monotonic() < deadline:
        v = rng.choice(vl)
        alive[v] = False
        E, bad, viol, K, vl = evaluate()

    best_K, best_alive = -1, None
    if viol == 0 and bad == 0:
        best_K, best_alive = K, alive[:]

    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T_hi, T_lo = 2.5, 0.15
    while True:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T_hi * (T_lo / T_hi) ** min(1.0, (now - t0) / span)
        r = rng.random()
        if vl and r < 0.5:
            v = rng.choice(vl)
            if rng.random() < 0.6:
                x = v
            else:
                nb = [u for u in adj[v] if alive[u]]
                x = rng.choice(nb) if nb else v
        elif r < 0.85:
            x = rng.randrange(n)
            tries = 0
            while alive[x] and tries < 50:
                x = rng.randrange(n)
                tries += 1
            if alive[x]:
                continue
        else:
            x = rng.randrange(n)

        alive[x] = not alive[x]
        E2, bad2, viol2, K2, vl2 = evaluate()
        if E2 <= E or rng.random() < math.exp(-(E2 - E) / T):
            E, bad, viol, K, vl = E2, bad2, viol2, K2, vl2
            if viol == 0 and bad == 0 and K > best_K:
                best_K, best_alive = K, alive[:]
        else:
            alive[x] = not alive[x]

    if best_alive is not None:
        verts = [v for v in range(n) if best_alive[v]]
        idx = {v: i for i, v in enumerate(verts)}
        E2 = [(idx[u], idx[v]) for u, v in e0 if best_alive[u] and best_alive[v]]
        consider(len(verts), E2)


def _run(d, D, deadline, rng, consider):
    if D == 2:
        return  # K_{d,d} already attains the Moore order for D = 2
    if d == 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])  # even cycle C_{2D}
        return
    if D == 3:
        q = _largest_pp(d - 1)
        if q:
            consider(*lib.projective_plane_incidence(q))
        return

    # D >= 4: fallback W(q) with degree q+1 <= d, restricted to small q for speed.
    q = _largest_pp(min(d - 1, 9))
    if q:
        consider(*_gq_w(q))

    # Main experiment: d is a prime power in [3, 9], so W(d) has degree d+1 and
    # we delete vertices to bring the degree down to d.
    if D == 4 and 3 <= d <= 9 and lib.is_prime_power(d):
        n0, e0 = _gq_w(d)
        _anneal_delete(n0, e0, d, D, deadline, rng, consider)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    st = {"best": lib.haar_graph(d, range(d))}  # K_{d,d}: valid fallback for D >= 2

    def consider(n, e):
        if n > st["best"][0] and lib.is_valid(n, e, d, D):
            st["best"] = (n, e)

    try:
        _run(d, D, deadline, rng, consider)
    except Exception:
        pass

    n, e = st["best"]
    if not lib.is_valid(n, e, d, D):
        return lib.haar_graph(d, range(d))
    return n, e
