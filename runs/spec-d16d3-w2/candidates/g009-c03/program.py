import random
import time

import lib


# ----------------------------------------------------------------------------
# Projective-plane helpers.
# ----------------------------------------------------------------------------

def _pg(q):
    """Return (m, edges, point_lines, line_points) for PG(2, q); points and lines are both indexed 0..m-1."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]
    lp = [[] for _ in range(m)]
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return m, edges, pl, lp


def _loads_ok(S, s, m, pl, lp):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, pl, lp, rng, deadline, trials=40):
    """Randomized greedy arc-like set with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in pl[P]) and all(cp[Q] < s for Q in lp[P]):
                S.append(P)
                for L in pl[P]:
                    cl[L] += 1
                for Q in lp[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _start_set(q, m, s, pl, lp, rng, deadline):
    """Best feasible starting set: conic (plus nucleus for even q) or greedy."""
    cands = []
    if q >= 3:
        idx = {p: i for i, p in enumerate(lib.projective_points(q))}
        F = lib.GF(q)
        cs = [idx[(1, t, F.mul(t, t))] for t in range(q)]
        cs.append(idx[(0, 0, 1)])
        if q % 2 == 0:
            cs.append(idx[(0, 1, 0)])
        if _loads_ok(cs, s, m, pl, lp):
            cands.append(cs)
    g = _greedy_arc(m, s, pl, lp, rng, deadline)
    if g and _loads_ok(g, s, m, pl, lp):
        cands.append(g)
    return max(cands, key=len, default=[])


def _arc_search(m, s, pl, lp, rng, deadline, S0):
    """Iterated local search for a large S with all loads <= s, starting from feasible S0.

    Insert a random outside point if feasible; swap out its single blocker (plateau move);
    occasionally swap out a pair of blockers. On stagnation, perturb by dropping two members.
    """
    cl = [0] * m
    cp = [0] * m
    inS = [False] * m
    S = []

    def add(P):
        inS[P] = True
        S.append(P)
        for L in pl[P]:
            cl[L] += 1
        for Q in lp[P]:
            cp[Q] += 1

    def remove(P):
        inS[P] = False
        S.remove(P)
        for L in pl[P]:
            cl[L] -= 1
        for Q in lp[P]:
            cp[Q] -= 1

    def blockers(P):
        satL = {L for L in pl[P] if cl[L] >= s}
        satQ = {Q for Q in lp[P] if cp[Q] >= s}
        if not satL and not satQ:
            return []
        return [R for R in S
                if any(L in satL for L in pl[R]) or any(Q in satQ for Q in lp[R])]

    for P in S0:
        add(P)
    best = list(S)
    it = 0
    stall = 0
    while True:
        it += 1
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        P = rng.randrange(m)
        if inS[P]:
            continue
        B = blockers(P)
        if not B:
            add(P)
        elif len(B) == 1 or (len(B) == 2 and rng.random() < 0.05):
            for R in B:
                remove(R)
            add(P)
        else:
            stall += 1
            continue
        if len(S) > len(best):
            best = list(S)
            stall = 0
        else:
            stall += 1
        if stall > 20000:
            for R in rng.sample(S, min(2, len(S))):
                remove(R)
            stall = 0
    return best


def _arc_graph(m, edges, pl, lp, S):
    """PG(2,q) incidence plus, per element of S, an A-vertex (on the point side) and a B-vertex (on the line side)."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        a = 2 * m + t
        for L in pl[P]:
            E.append((a, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in lp[j]:
            E.append((Q, b))
    return n, E


# ----------------------------------------------------------------------------
# Diameter-preserving growth: twins, cover extension, edge saturation.
# ----------------------------------------------------------------------------

def _adjlist(n, E):
    adj = [[] for _ in range(n)]
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    return adj


def _bip(n, adj):
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        st = [s]
        while st:
            u = st.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    st.append(v)
    return color


def _balls(n, adj, r):
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _twin(n, E, d, rng, deadline):
    """Add twins (same neighbourhood) of vertices whose neighbours all have spare degree.

    A twin keeps all old distances and sits at distance 2 from its original, so diameter
    <= D is preserved for D >= 2; it stays on the same side, so bipartiteness is kept.
    """
    E = list(E)
    adj = _adjlist(n, E)
    while time.monotonic() < deadline:
        elig = [v for v in range(n)
                if adj[v] and all(len(adj[u]) < d for u in adj[v])]
        if not elig:
            break
        v = rng.choice(elig)
        t = n
        n += 1
        nb = list(adj[v])
        adj.append(nb)
        for u in nb:
            adj[u].append(t)
            E.append((u, t))
    return n, E


def _greedy_cover(cands, ball, full, d, rng, randomize):
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        bg = max(gains)
        if bg == 0:
            break
        thr = bg
        if randomize and rng.random() < 0.5:
            thr = bg - 1
        opts = [i for i, g in enumerate(gains) if g >= max(thr, 1)]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, E, d, D, deadline, rng):
    """Add a vertex on one side adjacent to a set covering all vertices within distance D-1."""
    E = list(E)
    adj = _adjlist(n, E)
    deg = [len(a) for a in adj]
    color = _bip(n, adj)
    while time.monotonic() < deadline:
        ball = _balls(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for att in range(30):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, att > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    E.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, E


def _saturate(n, E, d, rng):
    """Join deficient opposite-colour vertices with spare degree (only shortens distances)."""
    E = list(E)
    adj = _adjlist(n, E)
    deg = [len(a) for a in adj]
    color = _bip(n, adj)
    existing = {(min(u, v), max(u, v)) for u, v in E}
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            E.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return n, E


def _grow(n, E, d, D, deadline, rng):
    for _ in range(6):
        if time.monotonic() >= deadline:
            break
        n2, E2 = _extend_cover(n, E, d, D, deadline, rng)
        grew = n2 != n
        n, E = _saturate(n2, E2, d, rng)
        if not grew:
            break
    return n, E


def _post(n, E, d, D, deadline, rng):
    now = time.monotonic()
    rem = max(0.0, deadline - now)
    n, E = _twin(n, E, d, rng, min(deadline, now + 0.3 * rem))
    n, E = _grow(n, E, d, D, deadline, rng)
    n, E = _twin(n, E, d, rng, deadline)
    return n, E


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.75 * float(time_limit), 44.0)
    deadline = start + budget
    rng = random.Random(seed * 1000003 + 31 * d + D)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))
    best = (best_n, list(best_E))

    def consider(n, E):
        nonlocal best
        if n > best[0] and lib.is_valid(n, E, d, D):
            best = (n, list(E))

    if D == 2 or d < 2:
        return best

    # Pure projective plane PG(2, q), q the largest prime power with q + 1 <= d. Diameter 3.
    qs = [q for q in range(2, d) if lib.is_prime_power(q)]
    if qs:
        n, E = lib.projective_plane_incidence(qs[-1])
        consider(n, E)

    # Arc-extended projective planes: spare degree s = d - q - 1 per vertex.
    cands = []
    for q in qs:
        s = d - q - 1
        if s < 1 or q < 3:
            continue
        m = q * q + q + 1
        bound = 2 * m + 2 * (s * m // (q + 1))
        if bound > best[0]:
            cands.append((bound, q, s))
    cands.sort(reverse=True)

    for idx, (_bound, q, s) in enumerate(cands):
        now = time.monotonic()
        if now >= deadline:
            break
        share = (deadline - now) / (len(cands) - idx)
        q_deadline = now + share
        m, edges, pl, lp = _pg(q)
        S0 = _start_set(q, m, s, pl, lp, rng, now + 0.25 * share)
        S = _arc_search(m, s, pl, lp, rng, now + 0.7 * share, S0)
        if not S or not _loads_ok(S, s, m, pl, lp):
            continue
        n, E = _arc_graph(m, edges, pl, lp, S)
        consider(n, E)
        n2, E2 = _post(n, E, d, D, q_deadline, rng)
        consider(n2, E2)

    if not lib.is_valid(best[0], best[1], d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
        return best_n, list(best_E)
    return best[0], list(best[1])
