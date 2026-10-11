import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bases.
# ----------------------------------------------------------------------------

def _pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq(q):
    """Point-line incidence graph of the symplectic generalized quadrangle W(q).

    Points are 0..P-1, lines are P..P+L-1. Every point lies on q+1 lines, every
    line has q+1 points, and the incidence graph has diameter 4.
    """
    F = lib.GF(q)
    A = F.add_table.tolist()
    M = F.mul_table.tolist()
    NEG = [F.neg(a) for a in range(q)]
    INV = [0] + [F.inv(a) for a in range(1, q)]
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    P = len(pts)
    index = {v: i for i, v in enumerate(pts)}

    def norm(v):
        c = next(x for x in v if x)
        ic = INV[c]
        return tuple(M[ic][x] for x in v)

    covered = [bytearray(P) for _ in range(P)]
    lines = []
    for i in range(P):
        x = pts[i]
        ci = covered[i]
        for j in range(i + 1, P):
            if ci[j]:
                continue
            y = pts[j]
            # Symplectic form x0*y1 - x1*y0 + x2*y3 - x3*y2.
            t = A[M[x[0]][y[1]]][NEG[M[x[1]][y[0]]]]
            s = A[M[x[2]][y[3]]][NEG[M[x[3]][y[2]]]]
            if A[t][s] != 0:
                continue
            L = set()
            for a in range(q):
                ax = [M[a][x[k]] for k in range(4)]
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(A[ax[k]][M[b][y[k]]] for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                cp = covered[p]
                for r in L:
                    cp[r] = 1
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return P + len(lines), edges


# ----------------------------------------------------------------------------
# NEW helper: ARW-style iterated local search for maximum independent set.
#
# Compared with the simple conflict-count ILS used before, this one:
#  * keeps tightness counts (number of solution neighbours) for every vertex,
#  * improves with (1,2)-swaps: remove one solution vertex x and insert two
#    non-adjacent vertices whose only solution neighbour is x,
#  * perturbs by forcing in a random outside vertex, and undoes a rejected
#    perturbation exactly through a journal (no solution copies),
#  * occasionally restarts from the best solution found so far.
# ----------------------------------------------------------------------------

def _mis(N, adj, rng, deadline):
    """Large independent set of the graph with vertices 0..N-1 and neighbour lists adj."""
    if N == 0:
        return []
    nbm = [0] * N
    for v in range(N):
        m = 0
        for w in adj[v]:
            m |= 1 << w
        nbm[v] = m

    inS = [False] * N
    tight = [0] * N
    sol = []
    pos = [-1] * N
    journal = []
    rec = [True]
    perm = list(range(N))
    rng.shuffle(perm)

    def add(v):
        inS[v] = True
        pos[v] = len(sol)
        sol.append(v)
        for w in adj[v]:
            tight[w] += 1
        if rec[0]:
            journal.append((True, v))

    def remove(v):
        inS[v] = False
        i = pos[v]
        last = sol[-1]
        sol[i] = last
        pos[last] = i
        sol.pop()
        pos[v] = -1
        for w in adj[v]:
            tight[w] -= 1
        if rec[0]:
            journal.append((False, v))

    def fill():
        s = rng.randrange(N)
        for k in range(N):
            v = perm[(s + k) % N]
            if not inS[v] and tight[v] == 0:
                add(v)

    def improve():
        changed = True
        while changed:
            changed = False
            for x in list(sol):
                if not inS[x]:
                    continue
                L = [w for w in adj[x] if tight[w] == 1]
                if len(L) < 2:
                    continue
                pair = None
                for i in range(len(L)):
                    a = L[i]
                    na = nbm[a]
                    for j in range(i + 1, len(L)):
                        if not (na >> L[j]) & 1:
                            pair = (a, L[j])
                            break
                    if pair is not None:
                        break
                if pair is not None:
                    remove(x)
                    add(pair[0])
                    add(pair[1])
                    fill()
                    changed = True

    def undo():
        rec[0] = False
        for is_add, v in reversed(journal):
            if is_add:
                remove(v)
            else:
                add(v)
        rec[0] = True
        del journal[:]

    fill()
    improve()
    best = list(sol)
    cur = len(sol)
    last_imp = 0
    it = 0
    while True:
        it += 1
        if (it & 15) == 0 and time.monotonic() >= deadline:
            break
        del journal[:]
        if it - last_imp > 30000:
            # Restart from the best solution found so far.
            rec[0] = False
            for v in list(sol):
                remove(v)
            for v in best:
                add(v)
            rec[0] = True
            cur = len(best)
            last_imp = it
            continue
        v = rng.randrange(N)
        if inS[v]:
            continue
        for w in adj[v]:
            if inS[w]:
                remove(w)
        add(v)
        fill()
        improve()
        new = len(sol)
        if new > cur:
            cur = new
            if new > len(best):
                best = list(sol)
                last_imp = it
        elif new < cur:
            # Accept a worse solution only rarely, more rarely the further it falls.
            accept = 1.0 / (1 + (cur - new) * (len(best) - new + 1))
            if rng.random() >= accept:
                undo()
                continue
            cur = new
    return best


def _sides(n0, adj):
    """Two-colour the base graph (it is bipartite); return the two colour classes."""
    color = [-1] * n0
    for s in range(n0):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    classes = [[], []]
    for v in range(n0):
        classes[max(color[v], 0)].append(v)
    return classes


def _solve_side(side, nb, rng, deadline):
    """Large conflict-free subset of one colour class (conflicts stay inside the class)."""
    loc = {v: i for i, v in enumerate(side)}
    lnb = [[loc[w] for w in nb[v] if w in loc] for v in side]
    sol = _mis(len(side), lnb, rng, deadline)
    return [side[i] for i in sol]


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


def _blowup(n0, edges0, d, deadline, rng):
    """Twin blow-up of a base graph of degree d-1 by a large distance-2-free set."""
    adj = [[] for _ in range(n0)]
    for u, v in edges0:
        adj[u].append(v)
        adj[v].append(u)
    if any(len(a) != d - 1 for a in adj):
        return None
    cs = [set() for _ in range(n0)]
    for w in range(n0):
        a = adj[w]
        for i in range(len(a)):
            for j in range(i + 1, len(a)):
                cs[a[i]].add(a[j])
                cs[a[j]].add(a[i])
    nb = [sorted(s) for s in cs]
    if n0 <= 60:
        deadline = min(deadline, time.monotonic() + 2.0)

    sides = _sides(n0, adj)
    S = []
    now = time.monotonic()
    span = max(0.0, deadline - now)
    k = len(sides)
    for idx, side in enumerate(sides):
        if not side:
            continue
        sub_deadline = now + span * (idx + 1) / k
        S.extend(_solve_side(side, nb, rng, sub_deadline))
    return _blow(n0, edges0, S)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.85 * time_limit - 4.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    pg = _pg(d)
    if pg is not None:
        consider(pg[0], pg[1])

    # Blow-up route: base of degree exactly d-1 with q = d-2 a prime power.
    q = d - 2
    if 2 <= q <= 11 and lib.is_prime_power(q) and time.monotonic() < deadline - 2.0:
        if D >= 4:
            n0, e0 = _gq(q)
        elif D == 3:
            n0, e0 = lib.projective_plane_incidence(q)
        else:
            n0, e0 = 0, []
        if n0 > 0:
            consider(n0, e0)
            res = _blowup(n0, e0, d, deadline, rng)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
