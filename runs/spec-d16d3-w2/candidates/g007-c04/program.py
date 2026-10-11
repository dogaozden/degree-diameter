import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline: arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). Each old vertex has degree q+1,
# so spare capacity s = d - q - 1. Pick a point set S with at most s points of
# S on every line (A-side stars) and at most s lines indexed by S through every
# point (B-side stars). Each P in S gets a new A-vertex joined to the q+1 lines
# through P; each j in S gets a new B-vertex joined to the q+1 points on j.
# ----------------------------------------------------------------------------

def _loads_ok(S, s, m, point_lines, line_points):
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
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
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _arc_base(q, d, rng, deadline):
    """Return (adj, side) for the arc-extended PG(2,q) graph, or None."""
    s = d - q - 1
    if s < 0:
        return None
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)

    S = []
    if s >= 1:
        S = _greedy_arc(m, s, point_lines, line_points, rng, 30, deadline)
    if s >= 2:
        F = lib.GF(q)
        index = {p: i for i, p in enumerate(pts)}
        cs = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
        if q % 2 == 0:
            cs.append(index[(0, 1, 0)])
        if len(cs) > len(S) and _loads_ok(cs, s, m, point_lines, line_points):
            S = cs
    if not _loads_ok(S, s, m, point_lines, line_points):
        return None

    adj = {}
    side = {}

    def link(u, v):
        adj.setdefault(u, set()).add(v)
        adj.setdefault(v, set()).add(u)

    for v in range(2 * m):
        side[v] = 0 if v < m else 1
    for u, v in edges:
        link(u, v)
    k = len(S)
    for t, P in enumerate(S):
        x = 2 * m + t
        side[x] = 0
        for L in point_lines[P]:
            link(x, m + L)
    for t, j in enumerate(S):
        b = 2 * m + k + t
        side[b] = 1
        for Q in line_points[j]:
            link(b, Q)
    return adj, side


# ----------------------------------------------------------------------------
# Generic graph-state helpers. The state is adj: {vertex: set(neighbours)} with
# side[vertex] in {0, 1}. Vertices with no edges are not stored.
# ----------------------------------------------------------------------------

def _check(adj, d, D):
    """Return (ok, n, edges) where edges is the relabelled edge list."""
    E = [(u, v) for u in adj for v in adj[u] if u < v]
    if not E:
        return False, 0, []
    n, E2 = lib.relabel(E)
    return lib.is_valid(n, E2, d, D), n, E2


def _unlink(adj, v):
    for u in adj.pop(v):
        s = adj[u]
        s.discard(v)
        if not s:
            del adj[u]


def _greedy_add(adj, side, d, rng, ns):
    """Pick neighbours (on the opposite side, spare degree) that cover all same-side vertices
    within distance 2 of a new vertex on side ns. Returns a list or None."""
    opp = 1 - ns
    tset = {v for v in adj if side[v] == ns}
    if not tset:
        return None
    spare = [v for v in adj if side[v] == opp and len(adj[v]) < d]
    if not spare:
        return None
    rng.shuffle(spare)
    covered = set()
    chosen = set()
    T = []
    for _ in range(d):
        best_t = None
        best_g = 0
        for t in spare:
            if t in chosen:
                continue
            g = len((adj[t] & tset) - covered)
            if g > best_g:
                best_g = g
                best_t = t
        if best_t is None:
            break
        chosen.add(best_t)
        T.append(best_t)
        covered |= (adj[best_t] & tset)
        if len(covered) == len(tset):
            break
    return T if T else None


def _search(adj, side, d, D, deadline, rng, best):
    """Hill climbing with plateau moves. Every stored graph is validated.
    Moves: add a vertex covering its same-side set (may attach to new vertices),
    or remove one vertex and greedily refill. Returns the best (n, edges) found."""
    cur = {u: set(s) for u, s in adj.items()}
    best_n, best_E = best
    nid = max(side) + 1
    while time.monotonic() < deadline:
        trial = {u: set(s) for u, s in cur.items()}
        if rng.random() < 0.6:
            ns = rng.randrange(2)
            T = _greedy_add(trial, side, d, rng, ns)
            if T is None:
                continue
        else:
            v = rng.choice(list(trial))
            ns = side[v]
            _unlink(trial, v)
            T = _greedy_add(trial, side, d, rng, ns)
            if T is None:
                continue
        x = nid
        nid += 1
        side[x] = ns
        trial[x] = set(T)
        for t in T:
            trial[t].add(x)

        ok, n, E = _check(trial, d, D)
        if not ok or len(trial) < len(cur):
            continue
        cur = trial
        if n > best_n:
            best_n, best_E = n, E
    return best_n, best_E


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, 0.8 * time_limit - 1.0)
    end = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best_n, best_E = lib.haar_graph(d, range(d))
    if not lib.is_valid(best_n, best_E, d, D):
        return 1, []

    if D >= 3:
        arc_deadline = start + 0.25 * budget
        bases = []
        for q in range(2, d):
            if not lib.is_prime_power(q):
                continue
            if time.monotonic() > arc_deadline:
                break
            b = _arc_base(q, d, rng, arc_deadline)
            if b is None:
                continue
            adj, side = b
            ok, n, E = _check(adj, d, D)
            if ok:
                bases.append((n, E, adj, side))

        if bases:
            bases.sort(key=lambda t: -t[0])
            n0, E0, adj0, side0 = bases[0]
            if n0 > best_n:
                best_n, best_E = n0, E0
            best_n, best_E = _search(adj0, side0, d, D, end, rng, (best_n, best_E))

    ok, _, _ = _check({}, d, D) if False else (True, 0, 0)
    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, best_E
