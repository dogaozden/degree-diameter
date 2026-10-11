import math
import random
import time

import lib

# ----------------------------------------------------------------------------
# Decoupled covering families over PG(2, q)  (new construction)
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Each line has spare degree s = d - q - 1, and so does each point.
#
# Side A: a family F_A of line-sets X_1..X_k. Each X_t gets one new point-side
#   vertex joined to the lines of X_t. Validity needs only:
#     (cover)     every point lies on some line of X_t,
#     (intersect) any two members share a line,
#     (capacity)  each line lies in at most s members.
# Side B: a family F_B of point-sets Y_u, dual to side A. Each Y_u gets one
#   new line-side vertex joined to the points of Y_u. Conditions: every line
#   contains a point of Y_u, members pairwise share a point, and each point
#   lies in at most s members.
#
# The two sides use disjoint spare capacity, so they are independent. Diameter
# stays 3: same-side pairs share a block, and cross pairs are at distance 3
# because covering makes every point lie on a line of every A-member.
#
# Total order = 2m + |F_A| + |F_B|. Pencils (all lines through a point of an
# arc) give 14 + 14 = 28 extra for q = 13, s = 2, which matches the record 394.
# A 15th member on either side beats it. Annealing searches for such members,
# with warm starts from the current family.
# ----------------------------------------------------------------------------


def _best_q(d):
    """Largest prime power q <= 23 with q + 1 <= d, or None."""
    for q in range(min(d - 1, 23), 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _pg_data(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q)."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    return m, edges, point_lines, line_points


def _conic_idx(q, index):
    """Conic plus nucleus (q even) as point indices: an arc candidate."""
    F = lib.GF(q)
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _loads_ok(C, boe, m, cap):
    """True if every block is used by at most cap pencils centred on C."""
    cnt = [0] * m
    for e in C:
        for b in boe[e]:
            cnt[b] += 1
    return max(cnt, default=0) <= cap


def _greedy_centers(n_el, cap, boe, rng, trials, deadline):
    """Randomized greedy set of elements whose pencils respect the capacity cap."""
    best = []
    order = list(range(n_el))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cnt = [0] * n_el
        S = []
        for e in order:
            bl = boe[e]
            if all(cnt[b] < cap for b in bl):
                S.append(e)
                for b in bl:
                    cnt[b] += 1
        if len(S) > len(best):
            best = S
    return best


def _fit(mem, z, m, rng):
    """Truncate or pad a block list to exactly z distinct blocks."""
    mem = list(mem)[:z]
    seen = set(mem)
    while len(mem) < z:
        b = rng.randrange(m)
        if b not in seen:
            seen.add(b)
            mem.append(b)
    return mem


def _anneal_family(m, cap, z, eob, boe, init, rng, deadline):
    """Anneal k = len(init) blocks-subsets of size z into a valid covering family.

    eob[b]: elements covered by block b. boe[e]: blocks containing element e.
    Constraints: cover (every element covered by each member), pairwise
    intersection of members, and at most cap members per block.
    Cost = uncovered pairs + non-intersecting pairs + capacity excess.
    Returns the list of members on success, else None.
    """
    k = len(init)
    mem = [list(x) for x in init]
    inset = [set(x) for x in mem]
    use = [0] * m
    for X in mem:
        for b in X:
            use[b] += 1
    cost = sum(max(0, u - cap) for u in use)
    cover = []
    for X in mem:
        c = [0] * m
        for b in X:
            for e in eob[b]:
                c[e] += 1
        cover.append(c)
        cost += sum(1 for x in c if x == 0)
    inter = [[0] * k for _ in range(k)]
    for i in range(k):
        for j in range(i + 1, k):
            c = len(inset[i] & inset[j])
            inter[i][j] = inter[j][i] = c
            if c == 0:
                cost += 1
    if cost == 0:
        return mem

    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T = 1.0
    it = 0
    while True:
        it += 1
        if (it & 127) == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            T = max(0.02, 0.03 ** ((now - t0) / span))
        i = rng.randrange(k)
        t = rng.randrange(z)
        a = mem[i][t]
        ci = cover[i]
        b = -1
        if rng.random() < 0.8:
            for _ in range(16):
                e = rng.randrange(m)
                if ci[e] == 0:
                    bl = boe[e]
                    b = bl[rng.randrange(len(bl))]
                    break
        if b < 0:
            b = rng.randrange(m)
        si_ = inset[i]
        if b in si_:
            continue
        ea = eob[a]
        eb = eob[b]
        dU = 0
        for e in ea:
            ci[e] -= 1
            if ci[e] == 0:
                dU += 1
        for e in eb:
            if ci[e] == 0:
                dU -= 1
            ci[e] += 1
        dN = 0
        newvals = []
        for j in range(k):
            if j == i:
                continue
            ij = inter[i][j]
            nw = ij
            sj = inset[j]
            if a in sj:
                nw -= 1
            if b in sj:
                nw += 1
            if ij == 0 and nw != 0:
                dN -= 1
            elif ij != 0 and nw == 0:
                dN += 1
            newvals.append((j, nw))
        dO = 0
        if use[a] > cap:
            dO -= 1
        if use[b] >= cap:
            dO += 1
        delta = dU + dN + dO
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            for j, nw in newvals:
                inter[i][j] = inter[j][i] = nw
            si_.discard(a)
            si_.add(b)
            mem[i][t] = b
            use[a] -= 1
            use[b] += 1
            cost += delta
            if cost <= 0:
                return mem
        else:
            for e in eb:
                ci[e] -= 1
            for e in ea:
                ci[e] += 1
    return None


def _assemble(m, edges, famA, famB):
    """Base PG incidence plus one new point-side vertex per A-member and one line-side vertex per B-member."""
    E = list(edges)
    x = 2 * m
    for X in famA:
        for L in X:
            E.append((x, m + L))
        x += 1
    for Y in famB:
        for P in Y:
            E.append((P, x))
        x += 1
    return x, E


def _twin_saturate(n, edges, d, D, rng, deadline):
    """Add diameter-preserving twins of vertices whose neighbours all have spare degree."""
    if D < 2:
        return n, list(edges)
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    while time.monotonic() < deadline:
        elig = [v for v in range(n)
                if adj[v] and all(len(adj[u]) < d for u in adj[v])]
        if not elig:
            break
        v = rng.choice(elig)
        t = n
        n += 1
        adj.append(list(adj[v]))
        for u in adj[t]:
            adj[u].append(t)
            edges.append((u, t))
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.85 * time_limit - 1.0)
    hard = start + 0.9 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2 or d < 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    def consider_twins(n, e):
        consider(n, e)
        tn, te = _twin_saturate(n, e, d, D, rng,
                                min(hard, time.monotonic() + 1.0))
        consider(tn, te)

    q = _best_q(d)
    if q is None:
        return best
    s = d - q - 1
    m, edges, point_lines, line_points = _pg_data(q)
    consider(2 * m, edges)
    if s < 1:
        return best  # d = q + 1: the projective-plane incidence graph is extremal

    try:
        pts = lib.projective_points(q)
        index = {p: i for i, p in enumerate(pts)}
        conic = _conic_idx(q, index)
        # side 0: A-family (members are line sets); side 1: B-family (point sets)
        sides = [(point_lines, line_points), (line_points, point_lines)]
        centers = []
        for boe, _ in sides:
            cands = []
            if _loads_ok(conic, boe, m, s):
                cands.append(conic)
            cands.append(_greedy_centers(m, s, boe, rng, 40,
                                         time.monotonic() + 1.0))
            centers.append(max(cands, key=len))

        fam = [[list(boe[e]) for e in centers[si]]
               for si, (boe, _) in enumerate(sides)]
        consider_twins(*_assemble(m, edges, fam[0], fam[1]))

        z_opts = [d - 1, d]
        cur = [len(fam[0]), len(fam[1])]
        turn = 0
        while True:
            now = time.monotonic()
            remaining = deadline - now
            if remaining < 0.3:
                break
            si = turn % 2
            turn += 1
            boe, eob = sides[si]
            k = cur[si] + 1
            z = rng.choice(z_opts)
            slice_len = min(remaining, max(2.0, min(12.0, remaining / 3.0)))
            if fam[si] and rng.random() < 0.6:
                # Warm start: current family plus one random member.
                init = [_fit(x, z, m, rng) for x in fam[si]]
                init.append(rng.sample(range(m), z))
            else:
                # Cold start: a random subset of the arc as pencils, the rest random.
                t = rng.randint(0, min(len(centers[si]), k))
                sub = rng.sample(centers[si], t)
                init = [_fit(boe[e], z, m, rng) for e in sub]
                while len(init) < k:
                    init.append(rng.sample(range(m), z))
            res = _anneal_family(m, s, z, eob, boe, init, rng, now + slice_len)
            if res is not None:
                fam[si] = res
                cur[si] = k
                consider_twins(*_assemble(m, edges, fam[0], fam[1]))
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
