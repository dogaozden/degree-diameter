import itertools
import math
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
# Maximum independent set by iterated local search with (1,2)-swaps.
# ----------------------------------------------------------------------------

def _mis(n, adj, deadline, rng):
    """Return a large independent set of the graph (n vertices, adj neighbour lists) found before deadline."""
    if n == 0:
        return []
    inS = [False] * n
    c = [0] * n
    S = set()
    adjset = [set(a) for a in adj]

    def add(v):
        inS[v] = True
        S.add(v)
        for w in adj[v]:
            c[w] += 1

    def remove(u):
        inS[u] = False
        S.discard(u)
        for w in adj[u]:
            c[w] -= 1

    def local_search():
        while True:
            changed = False
            free = [v for v in range(n) if not inS[v] and c[v] == 0]
            rng.shuffle(free)
            for v in free:
                if not inS[v] and c[v] == 0:
                    add(v)
                    changed = True
            for x in list(S):
                if not inS[x]:
                    continue
                one = [u for u in adj[x] if c[u] == 1]
                if len(one) < 2:
                    continue
                rng.shuffle(one)
                pair = None
                for i in range(len(one)):
                    for j in range(i + 1, len(one)):
                        if one[j] not in adjset[one[i]]:
                            pair = (one[i], one[j])
                            break
                    if pair is not None:
                        break
                if pair is not None:
                    remove(x)
                    add(pair[0])
                    add(pair[1])
                    changed = True
            if not changed:
                break

    order = list(range(n))
    rng.shuffle(order)
    for v in order:
        if not inS[v] and c[v] == 0:
            add(v)
    local_search()
    best = list(S)
    stale = 0

    while time.monotonic() < deadline:
        cand = [v for v in range(n) if not inS[v]]
        if not cand:
            break
        v = rng.choice(cand)
        for w in adj[v]:
            if inS[w]:
                remove(w)
        add(v)
        local_search()
        if len(S) > len(best):
            best = list(S)
            stale = 0
        else:
            stale += 1
        if len(S) < len(best) - 1 or stale > 300:
            for u in list(S):
                remove(u)
            for u in best:
                add(u)
            stale = 0
    return best


# ----------------------------------------------------------------------------
# Twin construction on W(q), degree q+2 (for d = q+2, D = 4).
# ----------------------------------------------------------------------------

def _twin_graph(q, deadline, rng):
    P, lines = _gq_w(q)
    L = len(lines)
    pl = [[] for _ in range(P)]
    for j, Ls in enumerate(lines):
        for p in Ls:
            pl[p].append(j)
    padj = [set() for _ in range(P)]
    for Ls in lines:
        for p in Ls:
            for r in Ls:
                if p != r:
                    padj[p].add(r)
    ladj = [set() for _ in range(L)]
    for p in range(P):
        for a in pl[p]:
            for b in pl[p]:
                if a != b:
                    ladj[a].add(b)

    now = time.monotonic()
    mid = now + (deadline - now) / 2.0
    I = _mis(P, [sorted(s) for s in padj], mid, rng)
    J = _mis(L, [sorted(s) for s in ladj], deadline, rng)

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
# New construction: bi-Cayley (group voltage) lifts of the 2-vertex base graph
# with d parallel darts. Vertices a_x = x, b_y = M + y for x, y in G (|G| = M).
# Edge a_x ~ b_{x*g} for each g in S (|S| = d). Left translations are
# automorphisms, so diameter <= D reduces to two BFS runs: from a_e (covers all
# a-a, a-b pairs) and from b_e (covers b-b pairs). A simulated-annealing search
# over S minimises the number of pairs left uncovered. Every hit is verified
# with lib.is_valid before use.
# ----------------------------------------------------------------------------

def _groups(M):
    """Groups of order M to try: cyclic, plus a few semidirect products Z_a x|_r Z_k with a*k = M."""
    out = [lib.cyclic_group(M)]
    for k in (2, 3, 4):
        if M % k:
            continue
        a = M // k
        if a < 3:
            continue
        cnt = 0
        for r in range(2, a):
            if math.gcd(r, a) == 1 and pow(r, k, a) == 1 % a:
                try:
                    out.append(lib.semidirect_group(a, k, r))
                except ValueError:
                    continue
                cnt += 1
                if cnt >= 1:
                    break
    return out


def _reach(src, M, S, Sinv, mulT, D):
    """Bytearray over 2M vertices: 1 for vertices within distance D of src (A: 0..M-1, B: M..2M-1)."""
    seen = bytearray(2 * M)
    seen[src] = 1
    frontier = [src]
    for _ in range(D):
        nxt = []
        for v in frontier:
            if v < M:
                row = mulT[v]
                for g in S:
                    w = M + row[g]
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            else:
                row = mulT[v - M]
                for gi in Sinv:
                    w = row[gi]
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
        frontier = nxt
        if not frontier:
            break
    return seen


def _bicayley_search(M, grp, d, D, deadline, rng):
    """Anneal a d-subset S of the group (order M) so the bi-Cayley lift has diameter <= D. Return S or None."""
    mul, inv = grp[1], grp[2]
    mulT = [[mul(x, g) for g in range(M)] for x in range(M)]
    invT = [inv(g) for g in range(M)]
    e = 0  # identity code for both cyclic and semidirect encodings

    def score(S):
        Sinv = [invT[g] for g in S]
        sA = _reach(e, M, S, Sinv, mulT, D)
        sB = _reach(M + e, M, S, Sinv, mulT, D)
        return (2 * M - sA.count(1)) + (M - sB[M:].count(1))

    S = rng.sample(range(M), d)
    Sset = set(S)
    cur = score(S)
    T = 1.5
    while cur > 0 and time.monotonic() < deadline:
        i = rng.randrange(d)
        g = rng.randrange(M)
        if g in Sset:
            continue
        old = S[i]
        S[i] = g
        sc = score(S)
        if sc <= cur or rng.random() < math.exp(-(sc - cur) / T):
            cur = sc
            Sset.discard(old)
            Sset.add(g)
        else:
            S[i] = old
        T = max(0.05, T * 0.9995)
    if cur == 0:
        return list(S)
    return None


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

    # Already at the Moore bound: nothing to gain, return immediately.
    moore = 2 * sum((d - 1) ** i for i in range(D)) if d >= 2 else 1
    if best[0] >= moore:
        if lib.is_valid(best[0], best[1], d, D):
            return best
        return 2, [(0, 1)]

    # Twin construction on W(d-2): degree d, diameter 4. Gets most of the budget.
    twin_ok = D >= 4 and lib.is_prime_power(d - 2) and 2 <= d - 2 <= 11
    if twin_ok:
        try:
            consider(*_twin_graph(d - 2, t0 + 0.65 * budget, rng))
        except Exception:
            pass

    # Bold path: bi-Cayley lifts over groups of order M, searching for M above the current best.
    M = best[0] // 2 + 1
    while time.monotonic() < deadline - 0.5 and M >= d:
        for grp in _groups(M):
            if time.monotonic() >= deadline - 0.5:
                break
            sub = min(deadline - 0.5, time.monotonic() + 6.0)
            try:
                S = _bicayley_search(M, grp, d, D, sub, rng)
            except Exception:
                S = None
            if S is not None:
                mul = grp[1]
                edges = [(x, M + mul(x, g)) for x in range(M) for g in S]
                consider(2 * M, edges)
                break
        M += 1

    if not lib.is_valid(best[0], best[1], d, D):
        return 2, [(0, 1)]
    return best
