import itertools
import math
import random
import time

import lib

ITERS = 1000                 # annealing steps per try
TOP_SLACK = 8                # semidirect search orders up to Nmax//2 + TOP_SLACK
MAX_GROUPS_PER_ATTEMPT = 30  # semidirect groups tried per order N
GROUP_LIMIT = 400            # max group order accepted by closure

# Non-metacyclic groups: SL/PSL/PGL(2,p) x Z_k. Left-multiplication bi-Cayley
# graphs over these are a different family from the semidirect products.
MATRIX_SPECS = [
    ("PGL", 7, 1), ("SL", 7, 1), ("PSL", 7, 2), ("PSL", 5, 5), ("PSL", 5, 4),
    ("SL", 5, 2), ("PGL", 5, 2), ("PSL", 5, 3), ("PSL", 7, 1),
]


# ----------------------------------------------------------------------------
# Baseline families (fast, validated before use).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Finite groups given as multiplication tables (identity has index 0).
# ----------------------------------------------------------------------------

def _prim_root(p):
    for g in range(2, p):
        if len({pow(g, i, p) for i in range(1, p)}) == p - 1:
            return g
    return 1


def _normalizer(kind, p):
    """Canonical representative for the projective / sign quotient of SL(2,p)."""
    if kind == "PGL":
        def norm(M):
            for x in M:
                if x:
                    inv = pow(x, p - 2, p)
                    return tuple((y * inv) % p for y in M)
            return M
        return norm
    if kind == "PSL":
        def norm(M):
            for x in M:
                if x:
                    if x > p // 2:
                        return tuple((-y) % p for y in M)
                    return M
            return M
        return norm
    return lambda M: M


def _spec_order(kind, p, k):
    o = p * (p * p - 1)
    if kind == "PSL":
        o //= 2
    return o * k


def _closure(e0, G, mul):
    elems = [e0]
    idx = {e0: 0}
    i = 0
    while i < len(elems):
        x = elems[i]
        i += 1
        for g in G:
            y = mul(x, g)
            if y not in idx:
                if len(elems) >= GROUP_LIMIT:
                    return None
                idx[y] = len(elems)
                elems.append(y)
    return elems, idx


def _mat_table(kind, p, k):
    """Multiplication table (N, T) of kind(2,p) x Z_k, or None if too large."""
    norm = _normalizer(kind, p)

    def bmul(X, Y):
        a, b, c, d = X
        e, f, g, h = Y
        return norm(((a * e + b * g) % p, (a * f + b * h) % p,
                     (c * e + d * g) % p, (c * f + d * h) % p))

    ident = norm((1, 0, 0, 1))
    gens = [(1, 1, 0, 1), (1, 0, 1, 1), (0, p - 1, 1, 0)]
    if kind == "PGL":
        gens.append((_prim_root(p), 0, 0, 1))
    gens = [norm(g) for g in gens]
    if k == 1:
        def mul(x, y):
            return bmul(x, y)
        e0 = ident
        G = gens
    else:
        def mul(x, y):
            return (bmul(x[0], y[0]), (x[1] + y[1]) % k)
        e0 = (ident, 0)
        G = [(g, 0) for g in gens] + [(ident, 1)]
    res = _closure(e0, G, mul)
    if res is None:
        return None
    elems, idx = res
    N = len(elems)
    T = [[idx[mul(a, b)] for b in elems] for a in elems]
    return N, T


# ----------------------------------------------------------------------------
# Semidirect products Z_m x|_r Z_k (baseline family from the parent).
# ----------------------------------------------------------------------------

def _groups(N):
    import math as _m
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if _m.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


# ----------------------------------------------------------------------------
# Bi-Cayley search: vertices A_x, B_y (x, y in G), edges A_x -- B_{x s}, s in S.
# Identity WLOG in S. Diameter <= D iff all vertices are within D of A_0 and B_0.
# ----------------------------------------------------------------------------

def _unreached(N, T, invs, S, D):
    Sinv = [invs[g] for g in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < N:
                    row = T[u]
                    for g in S:
                        v = N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    row = T[u - N]
                    for h in Sinv:
                        v = row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _anneal(N, T, invs, d, D, rng, iters, deadline):
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _search(N, T, invs, d, D, rng, deadline):
    """Repeated annealing restarts on one group until success or deadline."""
    while time.monotonic() < deadline:
        S = _anneal(N, T, invs, d, D, rng, ITERS, deadline)
        if S is not None:
            return S
    return None


def _attempt_semidirect(N, d, D, rng, deadline):
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        S = _anneal(N, T, invs, d, D, rng, ITERS, deadline)
        if S is not None:
            return T, S
    return None


# ----------------------------------------------------------------------------
# Main routine.
# ----------------------------------------------------------------------------

def _run(d, D, rng, start, deadline, consider, state):
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return

    Nmax = lib._moore_bound(d, D) // 2   # bi-Cayley graph has 2N vertices
    span = deadline - start
    mid = start + 0.6 * span

    # Phase 1: non-metacyclic groups (SL/PSL/PGL(2,p) x Z_k), largest first.
    specs = []
    for kind, p, k in MATRIX_SPECS:
        o = _spec_order(kind, p, k)
        if d + 1 <= o <= Nmax:
            specs.append((o, kind, p, k))
    specs.sort(reverse=True)

    cache = {}
    budget = 2.0
    while specs and time.monotonic() < mid:
        eligible = [s for s in specs if s[0] > state["n"] // 2]
        if not eligible:
            break
        for o, kind, p, k in eligible:
            if time.monotonic() >= mid:
                break
            if o <= state["n"] // 2:
                continue
            key = (kind, p, k)
            if key not in cache:
                cache[key] = _mat_table(kind, p, k)
            tab = cache[key]
            if tab is None:
                continue
            N, T = tab
            invs = [row.index(0) for row in T]
            S = _search(N, T, invs, d, D, rng,
                        min(mid, time.monotonic() + budget))
            if S is not None:
                consider(2 * N, [(x, N + T[x][g]) for x in range(N) for g in S])
        budget *= 1.5

    # Phase 2: semidirect products (the parent's family), for the remaining time.
    top = min(Nmax, Nmax // 2 + TOP_SLACK)
    lo = d + 1
    budget = 0.4
    while time.monotonic() < deadline:
        cands = [N for N in range(lo, top + 1) if N > state["n"] // 2]
        if not cands:
            break
        for N in sorted(cands, reverse=True):
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt_semidirect(N, d, D, rng, min(deadline, now + budget))
            if res is not None:
                T, S = res
                consider(2 * N, [(x, N + T[x][g]) for x in range(N) for g in S])
                break
        budget *= 1.5


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    deadline = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    state = {"n": 1, "e": []}

    def consider(n, e):
        if n > state["n"] and lib.is_valid(n, e, d, D):
            state["n"] = n
            state["e"] = e

    try:
        _run(d, D, rng, start, deadline, consider, state)
    except Exception:
        pass

    n, e = state["n"], state["e"]
    if not lib.is_valid(n, e, d, D):
        return 1, []
    return n, e
