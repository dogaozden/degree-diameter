import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) as a point/line list (table-based, pure Python).
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


# ----------------------------------------------------------------------------
# Maximum independent set by fixed-size tabu search (min-conflicts swaps).
# We keep an independent set of size k, grow k whenever we reach a conflict-free
# state, and otherwise swap one conflicting member out for one outside vertex
# chosen to minimise the number of internal edges, with tabu tenures to avoid
# cycling. This targets exactly the structured instances here (partial ovoids
# and partial spreads), where plain iterated local search stalls.
# ----------------------------------------------------------------------------

def _greedy_is(n, adj, rng):
    """Random-order greedy maximal independent set."""
    order = list(range(n))
    rng.shuffle(order)
    blocked = [False] * n
    S = []
    for v in order:
        if not blocked[v]:
            S.append(v)
            blocked[v] = True
            for w in adj[v]:
                blocked[w] = True
    return S


def _tabu_mis(n, adj, deadline, rng):
    """Return a large independent set of the graph (n vertices, adj neighbour lists) found before deadline."""
    if n == 0:
        return []
    adjset = [set(a) for a in adj]
    init = _greedy_is(n, adj, rng)
    best = list(init)
    inS = [False] * n
    conf = [0] * n          # number of neighbours of v inside S
    for v in init:
        inS[v] = True
        for w in adj[v]:
            conf[w] += 1

    f = 0                   # number of edges inside S (0 for the initial greedy set)
    tabu_add = [0] * n      # vertex may not re-enter S before this iteration
    tabu_rm = [0] * n       # vertex may not leave S before this iteration
    it = 0
    big = 10 ** 6

    while True:
        if (it & 31) == 0 and time.monotonic() >= deadline:
            break
        it += 1

        if f == 0:
            # Conflict-free: record and grow the set by the least-conflicting outside vertex.
            best = [v for v in range(n) if inS[v]]
            outs = [v for v in range(n) if not inS[v]]
            if not outs:
                break
            mc = min(conf[v] for v in outs)
            v = rng.choice([x for x in outs if conf[x] == mc])
            f += conf[v]
            inS[v] = True
            for w in adj[v]:
                conf[w] += 1
            tabu_rm[v] = it + 10 + rng.randrange(10)
            continue

        ins = [u for u in range(n) if inS[u]]
        cand_u = [u for u in ins if conf[u] > 0 and tabu_rm[u] <= it]
        if not cand_u:
            cand_u = [u for u in ins if conf[u] > 0]
        mx = max(conf[u] for u in cand_u)
        u = rng.choice([x for x in cand_u if conf[x] == mx])

        # Choose the outside vertex whose insertion (after removing u) adds the fewest conflicts.
        au = adjset[u]
        best_key = None
        ties = []
        for v in range(n):
            if inS[v]:
                continue
            key = conf[v] - (1 if v in au else 0)
            if tabu_add[v] > it:
                key += big
            if best_key is None or key < best_key:
                best_key = key
                ties = [v]
            elif key == best_key:
                ties.append(v)
        v = rng.choice(ties)

        # Remove u.
        f -= conf[u]
        inS[u] = False
        for w in adj[u]:
            conf[w] -= 1
        tabu_add[u] = it + 10 + rng.randrange(10)

        # Add v.
        f += conf[v]
        inS[v] = True
        for w in adj[v]:
            conf[w] += 1
        tabu_rm[v] = it + 5 + rng.randrange(6)

    return best


# ----------------------------------------------------------------------------
# Twin construction on W(q), degree q+2 (for d = q+2, D = 4).
#
# Each W(q) vertex has one spare degree slot. We add:
#   * a "point twin" v_p for each p in I (I pairwise non-collinear), adjacent to
#     all lines through p (so each line gets at most one new neighbour);
#   * a "line twin" w_L for each L in J (J pairwise disjoint lines), adjacent to
#     all points of L (so each point gets at most one new neighbour).
# Non-collinear points are at distance 4 and disjoint lines are at distance 4,
# which keeps every pair within distance 4. The final lib.is_valid check
# guards against any mistake.
# ----------------------------------------------------------------------------

def _twin_graph(q, deadline, rng):
    P, lines = _gq_w(q)
    L = len(lines)
    pl = [[] for _ in range(P)]
    for j, Ls in enumerate(lines):
        for p in Ls:
            pl[p].append(j)
    padj = [set() for _ in range(P)]          # collinear points
    for Ls in lines:
        for p in Ls:
            for r in Ls:
                if p != r:
                    padj[p].add(r)
    ladj = [set() for _ in range(L)]          # lines sharing a point
    for p in range(P):
        for a in pl[p]:
            for b in pl[p]:
                if a != b:
                    ladj[a].add(b)

    now = time.monotonic()
    mid = now + (deadline - now) / 2.0
    I = _tabu_mis(P, [sorted(s) for s in padj], mid, rng)
    J = _tabu_mis(L, [sorted(s) for s in ladj], deadline, rng)

    edges = [(p, P + j) for j, Ls in enumerate(lines) for p in Ls]
    n = P + L
    for p in I:
        for j in pl[p]:
            edges.append((n, P + j))
        n += 1
    for j in J:
        for p in lines[j]:
            edges.append((p, n))
        n += 1
    return n, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 10.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, edges):
        nonlocal best
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)

    # Projective plane incidence graph: degree d, diameter 3.
    if D >= 3 and lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass

    # Generalized quadrangle W(d-1): degree d, diameter 4.
    if D >= 4 and lib.is_prime_power(d - 1) and 2 <= d - 1 <= 11:
        try:
            consider(*_gq_incidence(d - 1))
        except Exception:
            pass

    # Bold path: W(d-2) with twins using the spare degree slot (degree d, diameter 4).
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            consider(*_twin_graph(d - 2, deadline, rng))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
