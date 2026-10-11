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
# Maximum independent set by iterated local search with (1,2)-swaps
# (Andrade-Resende-Werneck style). Pure Python.
# ----------------------------------------------------------------------------

def _ils_mis(n, adj, deadline, rng):
    """Return a large independent set of the graph (n vertices, adj neighbour lists) found before deadline."""
    adjset = [set(a) for a in adj]
    inS = [False] * n
    tau = [0] * n        # number of neighbours of v inside S
    S = set()

    def ins(v):
        inS[v] = True
        S.add(v)
        for w in adj[v]:
            tau[w] += 1

    def rem(v):
        inS[v] = False
        S.discard(v)
        for w in adj[v]:
            tau[w] -= 1

    def fill():
        cand = [v for v in range(n) if not inS[v] and tau[v] == 0]
        rng.shuffle(cand)
        for v in cand:
            if not inS[v] and tau[v] == 0:
                ins(v)

    def two_improve():
        changed = True
        while changed:
            changed = False
            for x in list(S):
                # Free-after-removal neighbours of x: only x blocks them.
                cand = [w for w in adj[x] if tau[w] == 1 and not inS[w]]
                if len(cand) < 2:
                    continue
                found = None
                for i in range(len(cand)):
                    au = adjset[cand[i]]
                    for j in range(i + 1, len(cand)):
                        if cand[j] not in au:
                            found = (cand[i], cand[j])
                            break
                    if found:
                        break
                if found:
                    rem(x)
                    ins(found[0])
                    ins(found[1])
                    fill()
                    changed = True
                    break

    fill()
    two_improve()
    cur = list(S)
    best = list(S)
    while time.monotonic() < deadline:
        v = rng.randrange(n)
        if inS[v]:
            continue
        for w in adj[v]:
            if inS[w]:
                rem(w)
        ins(v)
        fill()
        two_improve()
        if len(S) > len(best):
            best = list(S)
        if len(S) >= len(cur) or rng.random() < 0.02:
            cur = list(S)
        else:
            for u in list(S):
                rem(u)
            for u in cur:
                ins(u)
    return best


# ----------------------------------------------------------------------------
# Spare-slot greedy extension (new helper).
#
# A new vertex x on side s, joined to a set N of vertices on the other side,
# keeps the diameter at most D iff every vertex w satisfies dist(N, w) <= D-1.
# Adding a vertex never shortens nothing that matters: existing distances can
# only shrink, so earlier pairs stay valid. We greedily choose N from vertices
# with spare degree, using bitmask balls of radius D-1 as set-cover sets.
# ----------------------------------------------------------------------------

def _colors(n, adj):
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        st = [s]
        while st:
            u = st.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    st.append(v)
    return col


def _balls(n, adj, R):
    """Bitmask of all vertices within distance R of each vertex."""
    reach = [1 << v for v in range(n)]
    for _ in range(R):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _extend(n, adj, col, d, D, deadline, rng):
    """Greedily add vertices keeping diameter <= D. Returns (new_n, new_edges)."""
    new_edges = []
    fails = 0
    while time.monotonic() < deadline and fails < 3:
        ball = _balls(n, adj, D - 1)
        full = (1 << n) - 1
        done = False
        sides = [0, 1]
        rng.shuffle(sides)
        for s in sides:
            pool = [y for y in range(n) if col[y] != s and len(adj[y]) < d]
            if not pool:
                continue
            for _ in range(3):
                rng.shuffle(pool)
                cov = 0
                chosen = []
                picked = set()
                while cov != full and len(chosen) < d:
                    by, bg = -1, 0
                    for y in pool:
                        if y in picked:
                            continue
                        g = (ball[y] & ~cov).bit_count()
                        if g > bg:
                            bg, by = g, y
                    if by < 0:
                        break
                    chosen.append(by)
                    picked.add(by)
                    cov |= ball[by]
                if cov == full:
                    x = n
                    n += 1
                    adj.append([])
                    col.append(s)
                    for y in chosen:
                        adj[y].append(x)
                        adj[x].append(y)
                        new_edges.append((y, x))
                    done = True
                    break
            if done:
                break
        fails = 0 if done else fails + 1
    return n, new_edges


# ----------------------------------------------------------------------------
# Twin construction on W(q), degree q+2 (for d = q+2, D = 4).
#
# Each W(q) vertex has one spare degree slot. We add:
#   * a "point twin" v_p for each p in I (I pairwise non-collinear), adjacent to
#     all lines through p;
#   * a "line twin" w_L for each L in J (J pairwise disjoint lines), adjacent to
#     all points of L.
# The two families use independent spare slots, so |I| and |J| are optimized
# separately: partial ovoid and partial spread problems.
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
    rem = max(0.0, deadline - now)
    I = _ils_mis(P, [sorted(s) for s in padj], now + 0.4 * rem, rng)
    J = _ils_mis(L, [sorted(s) for s in ladj], now + 0.8 * rem, rng)

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
    total = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = t0 + total
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

    # Twin graph on W(d-2) (degree d, diameter 4), then spare-slot extension.
    if D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11:
        try:
            n2, e2 = _twin_graph(d - 2, deadline, rng)
            consider(n2, e2)
            adj = [[] for _ in range(n2)]
            for u, v in e2:
                adj[u].append(v)
                adj[v].append(u)
            col = _colors(n2, adj)
            n3, extra = _extend(n2, adj, col, d, D, deadline, rng)
            if extra:
                consider(n3, e2 + extra)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
