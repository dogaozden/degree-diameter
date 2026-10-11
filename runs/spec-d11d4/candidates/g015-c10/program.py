import itertools
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q): points and totally isotropic lines.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Return (P, lines): points of W(q) indexed 0..P-1 and each totally isotropic line as a sorted point list."""
    F = lib.GF(q)
    mul = F.mul_table.tolist()
    add = F.add_table.tolist()
    neg = [next(b for b in range(q) if add[a][b] == 0) for a in range(q)]
    inv = [0] * q
    for a in range(1, q):
        inv[a] = next(b for b in range(1, q) if mul[a][b] == 1)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        ic = inv[c]
        return tuple(mul[ic][x] for x in v)

    def form(x, y):
        t = add[mul[x[0]][y[1]]][neg[mul[x[1]][y[0]]]]
        u = add[mul[x[2]][y[3]]][neg[mul[x[3]][y[2]]]]
        return add[t][u]

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i * P + j) in covered:
                continue
            y = pts[j]
            if form(x, y):
                continue
            Lset = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(add[mul[a][x[k]]][mul[b][y[k]]] for k in range(4))
                    if any(v):
                        Lset.add(index[norm(v)])
            Ls = sorted(Lset)
            lines.append(Ls)
            for p in Ls:
                for r in Ls:
                    if p < r:
                        covered.add(p * P + r)
    return P, lines


def _gq_incidence(q):
    """Incidence graph of W(q): (n, edges), points 0..P-1, lines P..P+L-1; degree q+1, diameter 4."""
    P, lines = _gq_w(q)
    L = len(lines)
    return P + L, [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]


def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Blow-up: replacing a base vertex v by a twin (same neighbourhood) raises the
# degree of each neighbour of v by one. For a base of degree d-1, a set S of
# base vertices may be blown up iff no two members of S share a neighbour.
# Two base vertices conflict iff they share a neighbour, so the conflict graph
# splits into the point part (collinear points) and the line part (concurrent
# lines) for the incidence graph of a generalized quadrangle.
# ----------------------------------------------------------------------------

def _conflicts(n0, edges0):
    """Conflict lists: u ~ w iff u and w have a common neighbour in the base."""
    adj = [[] for _ in range(n0)]
    for u, v in edges0:
        adj[u].append(v)
        adj[v].append(u)
    cs = [set() for _ in range(n0)]
    for w in range(n0):
        a = adj[w]
        for i in range(len(a)):
            ai = a[i]
            for j in range(i + 1, len(a)):
                aj = a[j]
                cs[ai].add(aj)
                cs[aj].add(ai)
    return [sorted(s) for s in cs]


def _mis_tabu(adjl, deadline, rng, nprng):
    """Large independent set via k-growing tabu search on conflict counts.

    Keeps a set S; when S has no internal conflicts it is recorded and a new
    vertex is added. Otherwise a conflicting vertex is swapped with the
    non-tabu outside vertex of fewest conflicts. Stops at the deadline or after
    a long stretch without growth.
    """
    n = len(adjl)
    nb = [np.asarray(a, dtype=np.int64) for a in adjl]
    c = np.zeros(n, dtype=np.int64)
    inS = np.zeros(n, dtype=bool)
    tabu = np.zeros(n, dtype=np.int64)
    S = []
    best = []
    patience = max(50000, 1000 * n)
    STALL = max(3000, 30 * n)
    last_grow = 0
    best_conf = None
    stall = 0

    def add(v):
        inS[v] = True
        c[nb[v]] += 1
        S.append(v)

    def remove(u):
        inS[u] = False
        c[nb[u]] -= 1
        S.remove(u)

    add(rng.randrange(n))
    it = 0
    while True:
        it += 1
        if (it & 127) == 0:
            if time.monotonic() >= deadline or it - last_grow > patience:
                break
        Sarr = np.array(S, dtype=np.int64)
        cs = c[Sarr]
        conf = int(cs.sum()) // 2
        if conf == 0:
            best = list(S)
            last_grow = it
            score = c + nprng.random(n) * 0.5
            score[inS] = np.inf
            v = int(np.argmin(score))
            if not np.isfinite(score[v]):
                break
            add(v)
            best_conf = None
            stall = 0
            continue
        if best_conf is None or conf < best_conf:
            best_conf = conf
            stall = 0
        else:
            stall += 1
            if stall > STALL:
                for _ in range(2):
                    if S:
                        remove(S[rng.randrange(len(S))])
                    while True:
                        v = rng.randrange(n)
                        if not inS[v]:
                            break
                    add(v)
                best_conf = None
                stall = 0
                continue
        cand = Sarr[cs > 0]
        u = int(cand[rng.randrange(len(cand))])
        score = c + nprng.random(n) * 0.5
        score[nb[u]] -= 1.0
        score[inS] = np.inf
        score[tabu > it] = np.inf
        v = int(np.argmin(score))
        if not np.isfinite(score[v]):
            continue
        remove(u)
        tabu[u] = it + int(0.6 * conf) + 1 + rng.randrange(10)
        add(v)
    return best


def _solve_mis(n, cl, deadline, rng, nprng):
    """Maximum-independent-set heuristic on the conflict graph, component by component."""
    seen = [False] * n
    comps = []
    for s in range(n):
        if seen[s]:
            continue
        seen[s] = True
        comp = [s]
        k = 0
        while k < len(comp):
            u = comp[k]
            k += 1
            for w in cl[u]:
                if not seen[w]:
                    seen[w] = True
                    comp.append(w)
        comps.append(comp)

    result = []
    work = []
    for comp in comps:
        if len(comp) == 1:
            result.append(comp[0])
        elif all(len(cl[v]) == len(comp) - 1 for v in comp):
            # Complete conflict graph: any single vertex is optimal.
            result.append(comp[0])
        else:
            work.append(comp)

    remaining = sum(len(c) for c in work)
    for comp in sorted(work, key=len, reverse=True):
        now = time.monotonic()
        left = deadline - now
        share = max(0.0, left) * len(comp) / max(1, remaining)
        remaining -= len(comp)
        loc = {v: i for i, v in enumerate(comp)}
        sub = [[loc[w] for w in cl[v]] for v in comp]
        sol = _mis_tabu(sub, now + share, rng, nprng)
        result.extend(comp[i] for i in sol)
    return result


def _blow(n0, edges0, S):
    """Blow up each vertex of S into two twin copies (same neighbourhood)."""
    extra = {}
    for v in S:
        extra[v] = n0 + len(extra)
    copies = [[v] + ([extra[v]] if v in extra else []) for v in range(n0)]
    edges = []
    for u, v in edges0:
        for a in copies[u]:
            for b in copies[v]:
                edges.append((a, b))
    return n0 + len(extra), edges


def _blowup(n0, edges0, d, deadline, rng, nprng):
    """Twin blow-up of a base graph of degree d-1 by a large conflict-free set."""
    deg = [0] * n0
    for u, v in edges0:
        deg[u] += 1
        deg[v] += 1
    if any(x != d - 1 for x in deg):
        return None
    cl = _conflicts(n0, edges0)
    S = list(dict.fromkeys(_solve_mis(n0, cl, deadline, rng, nprng)))
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = random.Random(seed)
    nprng = np.random.default_rng(abs(int(seed)) % (2 ** 32))

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Projective plane incidence graph: degree d, diameter 3.
    if D >= 3:
        try:
            pg = _pg(d)
            if pg is not None:
                consider(*pg)
        except Exception:
            pass

    # W(d-1) incidence graph: degree d, diameter 4.
    if D >= 4 and 2 <= d - 1 <= 11 and lib.is_prime_power(d - 1):
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    # Blow-up route: base of degree exactly d-1 with q = d-2 a prime power.
    q = d - 2
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < deadline - 2.0:
        try:
            if D >= 4:
                n0, e0 = _gq_incidence(q)
            else:
                n0, e0 = lib.projective_plane_incidence(q)
            consider(n0, e0)
            res = _blowup(n0, e0, d, deadline, rng, nprng)
            if res is not None:
                consider(res[0], res[1])
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
