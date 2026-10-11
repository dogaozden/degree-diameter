"""Diameter-3 bipartite graphs from PG(2,q) with polarity-paired cover families.

Base: incidence graph of PG(2,q), q the largest prime power with q+1 <= d. Each old vertex
has spare capacity s = d-q-1.

Extension idea (new in this version): choose a family of sets T_1..T_a of lines of PG(2,q) with
  (1) every T_k covers all points (each point lies on some line of T_k),
  (2) any two T_k, T_l share a line,
  (3) every line lies in at most s of the sets.
Add a point-side vertex x_k joined to the lines of T_k, and a line-side vertex y_k joined to the
points of T_k (same index labels, via the polarity point u <-> line u). Then every old vertex keeps
degree <= q+1+s = d, and the diameter stays 3:
  x_k to points: covered by (1); x_k to x_l: shared line (2); x_k to lines: via T_k meeting the line;
  x_k to y_l: some line of T_k passes through a point of T_l, by (1).
Order = 2(q^2+q+1) + 2a. Pencils at an arc (conic) give a = q+1 (the known 394 for d=16).
The search looks for a family with a+1 sets using simulated annealing on the three constraints.
"""
import math
import random
import time

import lib


def _pg(q):
    """Return (m, edges, pl, lp): PG(2,q) incidence; pl[P] = lines through P, lp[L] = points on L."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return m, edges, pl, lp


def _pencil_start(q, s, m, pl):
    """Family of pencils at a conic (plus nucleus for even q). Returns [] if loads exceed s."""
    if s < 2:
        return []
    pts = lib.projective_points(q)
    F = lib.GF(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    load = [0] * m
    for P in S:
        for L in pl[P]:
            load[L] += 1
    if max(load) > s:
        return []
    return [list(pl[P]) for P in S]


def _anneal(m, pl, lp, fam, s, rng, deadline):
    """Simulated annealing on a family of line-sets. Returns the family if all constraints hold, else None."""
    a = len(fam)
    T = [list(t) for t in fam]
    mem = [bytearray(m) for _ in range(a)]
    cov = [[0] * m for _ in range(a)]
    load = [0] * m
    for x in range(a):
        for L in T[x]:
            mem[x][L] = 1
            load[L] += 1
            for P in lp[L]:
                cov[x][P] += 1
    share = [[0] * a for _ in range(a)]
    for x in range(a):
        for y in range(x + 1, a):
            c = sum(1 for L in T[x] if mem[y][L])
            share[x][y] = share[y][x] = c
    U = sum(1 for x in range(a) for P in range(m) if cov[x][P] == 0)
    V = sum(1 for x in range(a) for y in range(x + 1, a) if share[x][y] == 0)
    O = sum(max(0, l - s) for l in load)
    st = [U, V, O]

    def swap(x, Lo, Li):
        """Set x replaces line Lo by line Li; updates all tables and the totals in st."""
        U_, V_, O_ = st
        cx = cov[x]
        for P in lp[Lo]:
            cx[P] -= 1
            if cx[P] == 0:
                U_ += 1
        for P in lp[Li]:
            if cx[P] == 0:
                U_ -= 1
            cx[P] += 1
        mem[x][Lo] = 0
        mem[x][Li] = 1
        sx = share[x]
        for y in range(a):
            if y == x:
                continue
            my = mem[y]
            if my[Lo]:
                v = sx[y] - 1
                sx[y] = v
                share[y][x] = v
                if v == 0:
                    V_ += 1
            if my[Li]:
                v = sx[y]
                if v == 0:
                    V_ -= 1
                sx[y] = v + 1
                share[y][x] = v + 1
        l = load[Lo]
        if l > s:
            O_ -= 1
        load[Lo] = l - 1
        l = load[Li]
        if l >= s:
            O_ += 1
        load[Li] = l + 1
        st[0], st[1], st[2] = U_, V_, O_

    cur = st[0] + st[1] + 2 * st[2]
    if cur == 0:
        return T
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    temp = 1.0
    it = 0
    while True:
        it += 1
        if (it & 255) == 0:
            now = time.monotonic()
            if now >= deadline:
                return None
            temp = 0.05 + 1.0 * (1.0 - (now - t0) / span)
        x = rng.randrange(a)
        Tx = T[x]
        idx = rng.randrange(len(Tx))
        Lo = Tx[idx]
        Li = -1
        if rng.random() < 0.8:
            cx = cov[x]
            for _ in range(6):
                P = rng.randrange(m)
                if cx[P] == 0:
                    Li = rng.choice(pl[P])
                    break
        if Li < 0:
            Li = rng.randrange(m)
        if mem[x][Li]:
            continue
        before = cur
        swap(x, Lo, Li)
        cur = st[0] + st[1] + 2 * st[2]
        delta = cur - before
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            Tx[idx] = Li
            if cur == 0:
                return T
        else:
            swap(x, Li, Lo)
            cur = before


def _graph(m, edges, fam):
    """Old PG(2,q) incidence plus, per family set k, a point-side vertex and a line-side vertex."""
    a = len(fam)
    E = list(edges)
    for k, Tk in enumerate(fam):
        x = 2 * m + k
        for L in Tk:
            E.append((x, m + L))
        y = 2 * m + a + k
        for P in Tk:
            E.append((P, y))
    return 2 * m + 2 * a, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return lib.haar_graph(d, range(d))  # K_{d,d}

    qs = [x for x in range(2, d) if lib.is_prime_power(x)]
    if not qs:
        return lib.haar_graph(d, range(d))
    q = qs[-1]
    m, edges, pl, lp = _pg(q)
    best = (2 * m, list(edges))
    s = d - q - 1
    if s == 0:
        return best

    fam = _pencil_start(q, s, m, pl)
    K = d
    while time.monotonic() < deadline:
        now = time.monotonic()
        left = deadline - now
        attempt_end = min(deadline, now + max(3.0, left / 3.0))
        new = [list(t) for t in fam] + [rng.sample(range(m), K)]
        res = _anneal(m, pl, lp, new, s, rng, attempt_end)
        if res is not None:
            fam = res
            n_c, e_c = _graph(m, edges, fam)
            if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
                best = (n_c, e_c)

    return best
