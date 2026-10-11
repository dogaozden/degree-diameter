import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Tunables.
# ----------------------------------------------------------------------------

MAX_ORDER = 400        # largest permutation group we materialise
MAX_SPECS = 5          # group candidates tried per bi-Cayley order
CLIMB_ITERS = 600      # annealing steps per connection-set attempt
ANNEAL_ITERS = 800     # annealing steps per multi-base attempt
CACHE_LIMIT = 24
_BIG = 10 ** 9
_GROUP_CACHE = {}
_PERM_ORDERS = {"PGL27": 336, "PSL27": 168, "S5": 120, "A5": 60, "S4": 24, "A4": 12}
_INF = 7               # index of the point at infinity in PG(1, 7)


# ----------------------------------------------------------------------------
# Baselines: projective plane and generalized quadrangle incidence graphs.
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 5."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Permutation and product groups as multiplication tables.
# A table is (N, T, invs): T[x][y] = x*y, identity = index 0, invs[g] = g^-1.
# ----------------------------------------------------------------------------

def _table_from_mul(N, mulf):
    T = [[mulf(x, y) for y in range(N)] for x in range(N)]
    invs = [row.index(0) for row in T]
    return N, T, invs


def _pmap(f):
    return tuple(f(x) for x in range(8))


def _perm_gens(name):
    """Generators acting on 8 points (PG(1,7), infinity = 7) or on 4/5 points."""
    if name in ("PGL27", "PSL27"):
        tr = _pmap(lambda x: _INF if x == _INF else (x + 1) % 7)
        inv = _pmap(lambda x: 0 if x == _INF else (_INF if x == 0 else (-pow(x, 5, 7)) % 7))
        c = 3 if name == "PGL27" else 2
        sc = _pmap(lambda x: _INF if x == _INF else (c * x) % 7)
        return [tr, sc, inv]
    if name == "S5":
        return [(1, 2, 3, 4, 0), (1, 0, 2, 3, 4)]
    if name == "A5":
        return [(1, 2, 3, 4, 0), (1, 2, 0, 3, 4)]
    if name == "S4":
        return [(1, 2, 3, 0), (1, 0, 2, 3)]
    if name == "A4":
        return [(1, 2, 0, 3), (1, 0, 3, 2)]
    raise ValueError(name)


def _perm_group(gens):
    """Closure of permutation generators; returns the table or None if too large."""
    n = len(gens[0])
    ident = tuple(range(n))
    elts = [ident]
    index = {ident: 0}
    frontier = [ident]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = tuple(x[g[i]] for i in range(n))
                if y not in index:
                    if len(elts) >= MAX_ORDER:
                        return None
                    index[y] = len(elts)
                    elts.append(y)
                    nxt.append(y)
        frontier = nxt

    def mulf(a, b):
        ea, eb = elts[a], elts[b]
        return index[tuple(ea[eb[i]] for i in range(n))]

    return _table_from_mul(len(elts), mulf)


def _dih_mul(k):
    def mul(x, y):
        r1, s1 = x % k, x // k
        r2, s2 = y % k, y // k
        r = (r1 + r2) % k if s1 == 0 else (r1 - r2) % k
        return r + k * ((s1 + s2) % 2)
    return mul


def _product(A, B):
    """Direct product; element a = x*Nb + y."""
    Na, Ta, _ = A
    Nb, Tb, _ = B
    N = Na * Nb
    T = []
    for a in range(N):
        x1, y1 = divmod(a, Nb)
        Ra, Rb = Ta[x1], Tb[y1]
        T.append([Ra[x2] * Nb + Rb[y2] for x2 in range(Na) for y2 in range(Nb)])
    invs = [row.index(0) for row in T]
    return N, T, invs


def _build_spec(spec):
    """Materialise a group spec as a table (cached). Returns None on failure."""
    if spec in _GROUP_CACHE:
        return _GROUP_CACHE[spec]
    kind = spec[0]
    val = None
    if kind == "perm":
        val = _perm_group(_perm_gens(spec[1]))
    elif kind == "cyc":
        k = spec[1]
        val = _table_from_mul(k, lambda x, y: (x + y) % k)
    elif kind == "dih":
        val = _table_from_mul(2 * spec[1], _dih_mul(spec[1]))
    elif kind == "semi":
        m, k, r = spec[1], spec[2], spec[3]
        order, mul, _ = lib.semidirect_group(m, k, r)
        val = _table_from_mul(order, mul)
    elif kind == "prod":
        A = _build_spec(spec[1])
        B = _build_spec(spec[2])
        if A is not None and B is not None:
            val = _product(A, B)
    if len(_GROUP_CACHE) >= CACHE_LIMIT:
        _GROUP_CACHE.clear()
    _GROUP_CACHE[spec] = val
    return val


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _specs_of_order(N):
    """Return (priority, rest) lists of group specs of order N."""
    pri, rest = [], []
    for name, o in _PERM_ORDERS.items():
        if o == N:
            pri.append(("perm", name))
        elif o < N and N % o == 0:
            pri.append(("prod", ("perm", name), ("cyc", N // o)))
    if N >= 6 and N % 2 == 0:
        rest.append(("dih", N // 2))
    for m, k, r in _groups(N):
        if k > 1:
            rest.append(("semi", m, k, r))
    rest.append(("cyc", N))
    return pri, rest


# ----------------------------------------------------------------------------
# Bi-Cayley graphs: A_x -- B_{x s}, s in S, |S| = d, identity in S WLOG.
# Left multiplication is an automorphism, so BFS from A_e and B_e suffices.
# ----------------------------------------------------------------------------

def _unreached(N, T, invs, S, D):
    """Count vertex pairs (source, target) not within distance D, from A_e and B_e."""
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


def _climb(N, T, invs, d, D, rng, iters, deadline):
    """Anneal a connection set S (identity fixed in S) to zero unreached pairs."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _unreached(N, T, invs, S, D)
    for it in range(iters):
        if cur == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = S[:]
        S2[i] = c
        v = _unreached(N, T, invs, S2, D)
        temp = 0.3 + 1.5 * (1.0 - it / iters)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            S, cur = S2, v
    return S if cur == 0 else None


def _bicayley_try(N, d, D, rng, deadline):
    """Try several groups of order N; return (T, S) on success, else None."""
    if N <= d:
        return None
    pri, rest = _specs_of_order(N)
    rng.shuffle(rest)
    for spec in (pri + rest)[:MAX_SPECS]:
        if time.monotonic() > deadline:
            break
        val = _build_spec(spec)
        if val is None or val[0] != N:
            continue
        _, T, invs = val
        S = _climb(N, T, invs, d, D, rng, CLIMB_ITERS, deadline)
        if S is not None:
            return T, S
    return None


# ----------------------------------------------------------------------------
# Multi-base voltage lifts over group tables, annealed.
# Each of the d layers is a perfect matching between k A-base and k B-base
# vertices, one voltage per dart. Left multiplication is an automorphism.
# ----------------------------------------------------------------------------

def _right_perm(T, G, s):
    """Permutation g -> g*s."""
    return [row[s] for row in T]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, T, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(T, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    temp = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(T_end, temp * decay)

        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(T, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / temp):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


def _multibase_try(k, G, d, D, rng, deadline):
    pri, rest = _specs_of_order(G)
    rng.shuffle(rest)
    for spec in (pri + rest)[:2]:
        if time.monotonic() > deadline:
            break
        val = _build_spec(spec)
        if val is None or val[0] != G:
            continue
        _, T, _ = val
        res = _anneal(d, D, k, G, T, rng, deadline, ANNEAL_ITERS)
        if res is not None:
            return res
    return None


# ----------------------------------------------------------------------------
# Main search: alternate bi-Cayley orders and multi-base lifts, aiming above
# the current best order.
# ----------------------------------------------------------------------------

def _main_search(d, D, moore, state, deadline, rng, consider):
    sweep = None
    while time.monotonic() < deadline:
        n_best = state["best"][0]
        if n_best >= moore:
            break
        bi_lo = max(n_best // 2 + 1, moore // 4 - 1)
        bi_hi = moore // 2
        use_bi = d >= 2 and bi_lo <= bi_hi and rng.random() < 0.6
        if use_bi:
            if sweep is None or sweep < bi_lo or sweep > bi_hi:
                sweep = bi_lo
            N = sweep
            sweep += 1
            found = _bicayley_try(N, d, D, rng, deadline)
            if found is not None:
                T, S = found
                consider(2 * N, [(x, N + T[x][g]) for x in range(N) for g in S])
        else:
            k = rng.choice((2, 3))
            lo = max(2, n_best // (2 * k) + 1)
            hi = moore // (2 * k)
            if lo > hi:
                continue
            G = rng.randint(lo, min(hi, lo + 12))
            res = _multibase_try(k, G, d, D, rng, deadline)
            if res is not None:
                consider(res[0], res[1])


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)
    state = {"best": best}

    def consider(n, e):
        if n > state["best"][0] and lib.is_valid(n, e, d, D):
            state["best"] = (n, e)

    try:
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
        if D >= 4:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
    except Exception:
        pass

    try:
        if state["best"][0] < moore:
            _main_search(d, D, moore, state, deadline, rng, consider)
    except Exception:
        pass

    best = state["best"]
    if not lib.is_valid(best[0], best[1], d, D):
        return lib.haar_graph(d, range(d))
    return best
