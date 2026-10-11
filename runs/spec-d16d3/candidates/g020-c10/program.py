import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold variant: free-form "cover" vertices on top of PG(2, q).
#
# Base: incidence graph of PG(2, q), q = largest prime power with q + 1 <= d.
# Spare degree per old vertex is s = d - q - 1.
#
# Extra A-vertex: a set T of lines, every line used by < s extra A-vertices.
#   It must cover all points (so it is within distance 2 of every point),
#   pairwise share a line with other A-vertices, and meet every B-vertex
#   (some line of T is incident to a point of the B-set).
# Extra B-vertex: the dual construction (a set U of points blocking all lines).
#
# The initial state is the conic-based arc extension (order 2(q^2+q+1)+2(q+1)),
# and a randomized search then tries to add more covers/blockers. Every
# accepted state is checked by a bitmask diameter test, and the final graph is
# checked with lib.is_valid. On any failure we fall back to a validated graph.
# ----------------------------------------------------------------------------


def _incidence(q):
    """PG(2, q) incidence: points 0..m-1, lines are indices 0..m-1 with vertex m+L."""
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    pl = [[] for _ in range(m)]  # point -> lines through it
    lp = [[] for _ in range(m)]  # line -> points on it
    for u, v in edges:
        pl[u].append(v - m)
        lp[v - m].append(u)
    return m, edges, pl, lp


def _reach_ok(n, edges, d, D):
    """True if max degree <= d and every pair of vertices is within distance D (bitmask BFS)."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) > d for a in adj):
        return False
    full = (1 << n) - 1
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt.append(r)
        reach = nxt
    return all(r == full for r in reach)


def _assemble(m, base, A, B):
    """Full graph: base PG incidence, A-vertices (adjacent to lines), B-vertices (adjacent to points)."""
    n = 2 * m + len(A) + len(B)
    edges = list(base)
    for i, T in enumerate(A):
        x = 2 * m + i
        edges.extend((x, m + L) for L in T)
    off = 2 * m + len(A)
    for j, U in enumerate(B):
        y = off + j
        edges.extend((Q, y) for Q in U)
    return n, edges


def _loads_ok(S, m, pl, lp, s):
    """Each line holds <= s points of S (A-side load) and each point lies on <= s lines of S (B-side)."""
    lc = [0] * m
    pc = [0] * m
    for P in S:
        for L in pl[P]:
            lc[L] += 1
        for Q in lp[P]:
            pc[Q] += 1
    return max(lc, default=0) <= s and max(pc, default=0) <= s


def _conic_set(q, m, pl, lp, s):
    """Conic (plus nucleus for even q) as a point-index set, if its loads fit in spare degree s."""
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {p: i for i, p in enumerate(pts)}
    S = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S if _loads_ok(S, m, pl, lp, s) else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.8 * time_limit, time_limit - 5.0))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid whenever D >= 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    if D == 2 or d < 3:
        return fb_n, fb_e

    qs = [q for q in range(min(d - 1, 23), 1, -1) if lib.is_prime_power(q)]
    if not qs:
        return fb_n, fb_e
    q = qs[0]
    s = d - q - 1

    m, base, pl, lp = _incidence(q)
    base_n = 2 * m
    if lib.is_valid(base_n, base, d, D) is False and D >= 3:
        return fb_n, fb_e
    if s <= 0:
        return base_n, base

    rng = random.Random(seed)

    # ---- initial state: arc-type pencils / duals -------------------------
    S = None
    if s >= 2:
        S = _conic_set(q, m, pl, lp, s)
    if S is None:
        bestS = []
        for _ in range(60):
            if time.monotonic() > deadline:
                break
            order = list(range(m))
            rng.shuffle(order)
            lc = [0] * m
            pc = [0] * m
            cur = []
            for P in order:
                if all(lc[L] < s for L in pl[P]) and all(pc[Q] < s for Q in lp[P]):
                    cur.append(P)
                    for L in pl[P]:
                        lc[L] += 1
                    for Q in lp[P]:
                        pc[Q] += 1
            if len(cur) > len(bestS):
                bestS = cur
        S = bestS

    A = [list(pl[P]) for P in S]   # pencil at P: lines through P
    B = [list(lp[P]) for P in S]   # dual: points on line P
    lineload = [0] * m
    ptload = [0] * m
    for T in A:
        for L in T:
            lineload[L] += 1
    for U in B:
        for Q in U:
            ptload[Q] += 1

    init_A = [list(T) for T in A]
    init_B = [list(U) for U in B]

    # ---- candidate generators -------------------------------------------
    def new_A():
        uncovered = set(range(m))
        cands = [L for L in range(m) if lineload[L] < s]
        T = []
        inT = set()
        while uncovered:
            if len(T) >= d:
                return None
            rng.shuffle(cands)
            best_L, bc = -1, 0
            for L in cands:
                if L in inT:
                    continue
                c = 0
                for Q in lp[L]:
                    if Q in uncovered:
                        c += 1
                if c > bc:
                    bc, best_L = c, L
            if best_L < 0:
                return None
            T.append(best_L)
            inT.add(best_L)
            uncovered.difference_update(lp[best_L])
        return T

    def new_B():
        uncovered = set(range(m))  # lines not yet blocked
        cands = [Q for Q in range(m) if ptload[Q] < s]
        U = []
        inU = set()
        while uncovered:
            if len(U) >= d:
                return None
            rng.shuffle(cands)
            best_Q, bc = -1, 0
            for Q in cands:
                if Q in inU:
                    continue
                c = 0
                for L in pl[Q]:
                    if L in uncovered:
                        c += 1
                if c > bc:
                    bc, best_Q = c, Q
            if best_Q < 0:
                return None
            U.append(best_Q)
            inU.add(best_Q)
            uncovered.difference_update(pl[best_Q])
        return U

    def compat_A(T):
        Ts = set(T)
        for T2 in A:
            if Ts.isdisjoint(T2):
                return False
        for U in B:
            if not any(L in Ts for Q in U for L in pl[Q]):
                return False
        return True

    def compat_B(U):
        Us = set(U)
        for U2 in B:
            if Us.isdisjoint(U2):
                return False
        for T in A:
            if not any(Q in Us for L in T for Q in lp[L]):
                return False
        return True

    def graph_ok():
        n, e = _assemble(m, base, A, B)
        return _reach_ok(n, e, d, D)

    best_A, best_B = [list(T) for T in A], [list(U) for U in B]
    best_tot = len(A) + len(B)

    # ---- randomized search ----------------------------------------------
    while time.monotonic() < deadline:
        r = rng.random()
        if r < 0.4:
            T = new_A()
            if T is not None and compat_A(T):
                A.append(T)
                for L in T:
                    lineload[L] += 1
                if not graph_ok():
                    A.pop()
                    for L in T:
                        lineload[L] -= 1
                    continue
        elif r < 0.8:
            U = new_B()
            if U is not None and compat_B(U):
                B.append(U)
                for Q in U:
                    ptload[Q] += 1
                if not graph_ok():
                    B.pop()
                    for Q in U:
                        ptload[Q] -= 1
                    continue
        else:
            # Perturbation: drop one extra vertex to escape plateaus.
            if (A or B) and rng.random() < 0.5:
                if A and (not B or rng.random() < 0.5):
                    i = rng.randrange(len(A))
                    T = A.pop(i)
                    for L in T:
                        lineload[L] -= 1
                elif B:
                    j = rng.randrange(len(B))
                    U = B.pop(j)
                    for Q in U:
                        ptload[Q] -= 1
            continue

        tot = len(A) + len(B)
        if tot > best_tot:
            best_tot = tot
            best_A = [list(T) for T in A]
            best_B = [list(U) for U in B]

    # ---- final validation with safe fallbacks ---------------------------
    for cA, cB in ((best_A, best_B), (init_A, init_B), ([], [])):
        n, e = _assemble(m, base, cA, cB)
        if lib.is_valid(n, e, d, D):
            return n, e
    return fb_n, fb_e
