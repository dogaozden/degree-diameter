import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (kept from the parent as fallbacks).
# ----------------------------------------------------------------------------

def _is_prime(p):
    if p < 2:
        return False
    i = 2
    while i * i <= p:
        if p % i == 0:
            return False
        i += 1
    return True


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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# NEW construction: bi-Cayley graphs over PSL(2,p) / PGL(2,p).
#
# Let G be a finite group and S a set of d distinct elements. The bipartite graph
# with parts A_g, B_g (g in G) and edges A_g ~ B_{g s} for s in S is d-regular on
# 2|G| vertices. Left multiplication acts transitively on each part, so the
# diameter is at most D iff a BFS from A_e and a BFS from B_e both reach all
# 2|G| vertices within D steps. Groups are matrix groups over Z_p, which are
# non-abelian and have much richer word growth than cyclic lifts.
# ----------------------------------------------------------------------------

def _encode(M, p):
    return ((M[..., 0] * p + M[..., 1]) * p + M[..., 2]) * p + M[..., 3]


def _canon(M, p, kind, invtab):
    M = M % p
    if kind == "psl":
        return np.minimum(_encode(M, p), _encode((-M) % p, p))
    nz = (M != 0)
    idx = np.argmax(nz, axis=-1)
    s = np.take_along_axis(M, idx[..., None], axis=-1)
    M2 = (M * invtab[s]) % p
    return _encode(M2, p)


def _decode(codes, p):
    M = np.empty((len(codes), 4), dtype=np.int64)
    x = codes.copy()
    M[:, 3] = x % p
    x //= p
    M[:, 2] = x % p
    x //= p
    M[:, 1] = x % p
    x //= p
    M[:, 0] = x % p
    return M


def _group_tables(p, kind):
    """Return (G, mult, inv, e) for PSL(2,p) ('psl') or PGL(2,p) ('pgl'); mult[g, h] = g*h."""
    grid = np.array(list(itertools.product(range(p), repeat=4)), dtype=np.int64)
    det = (grid[:, 0] * grid[:, 3] - grid[:, 1] * grid[:, 2]) % p
    M = grid[det == 1] if kind == "psl" else grid[det != 0]
    invtab = np.array([0] + [pow(x, p - 2, p) for x in range(1, p)], dtype=np.int64)
    codes = np.unique(_canon(M, p, kind, invtab))
    G = len(codes)
    X = _decode(codes, p)
    A = X[:, None, :]
    B = X[None, :, :]
    prod = np.stack([
        (A[..., 0] * B[..., 0] + A[..., 1] * B[..., 2]) % p,
        (A[..., 0] * B[..., 1] + A[..., 1] * B[..., 3]) % p,
        (A[..., 2] * B[..., 0] + A[..., 3] * B[..., 2]) % p,
        (A[..., 2] * B[..., 1] + A[..., 3] * B[..., 3]) % p,
    ], axis=-1)
    pc = _canon(prod, p, kind, invtab)
    idx = np.searchsorted(codes, pc)
    if not np.array_equal(codes[idx], pc):
        raise ValueError("group not closed")
    mult = idx.astype(np.int64)
    ident = _canon(np.array([[1, 0, 0, 1]], dtype=np.int64), p, kind, invtab)[0]
    e = int(np.searchsorted(codes, ident))
    inv = np.argmax(mult == e, axis=1)
    return G, mult, inv, e


def _unreached(S, invS, mult, e, D, G, start_side):
    """Number of vertices not reached within D steps from A_e (start_side 0) or B_e (start_side 1)."""
    visA = np.zeros(G, dtype=bool)
    visB = np.zeros(G, dtype=bool)
    front = np.array([e], dtype=np.int64)
    if start_side == 0:
        visA[e] = True
        side = 0
    else:
        visB[e] = True
        side = 1
    for _ in range(D):
        mark = np.zeros(G, dtype=bool)
        if side == 0:
            mark[mult[np.ix_(front, S)].ravel()] = True   # A_g -> B_{g s}
            new = mark & ~visB
            visB |= new
            side = 1
        else:
            mark[mult[np.ix_(front, invS)].ravel()] = True  # B_x -> A_{x s^-1}
            new = mark & ~visA
            visA |= new
            side = 0
        front = np.flatnonzero(new)
        if front.size == 0:
            break
    return 2 * G - int(visA.sum()) - int(visB.sum())


def _cost(S, mult, inv, e, D, G):
    Sa = np.array(S, dtype=np.int64)
    invS = inv[Sa]
    return (_unreached(Sa, invS, mult, e, D, G, 0)
            + _unreached(Sa, invS, mult, e, D, G, 1))


def _anneal(d, D, G, mult, inv, e, rng, deadline, max_iters):
    """Local search over d-subsets of G. Returns (found_zero_cost, S)."""
    S = rng.sample(range(G), d)
    cost = _cost(S, mult, inv, e, D, G)
    best = (cost, list(S))
    for t in range(max_iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = 0.3 + 2.5 * (1.0 - t / max_iters)
        i = rng.randrange(d)
        new = rng.randrange(G)
        if new in S:
            continue
        old = S[i]
        S[i] = new
        c2 = _cost(S, mult, inv, e, D, G)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
            if cost < best[0]:
                best = (cost, list(S))
        else:
            S[i] = old
    return best[0] == 0, best[1]


def _graph(G, mult, S):
    d = len(S)
    Sa = np.array(S, dtype=np.int64)
    cols = mult[:, Sa]
    edges = [(g, G + int(cols[g, j])) for g in range(G) for j in range(d)]
    return 2 * G, edges


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.90 * time_limit, time_limit - 5.0))
    deadline = start + budget
    search_deadline = start + 0.88 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < search_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # New bi-Cayley search over matrix groups.
    try:
        max_n = min(lib.moore_bound(d, D), 2800)
        cands = []
        for p in range(2, 60):
            if not _is_prime(p):
                continue
            for kind in ("psl", "pgl"):
                order = p * (p * p - 1) // 2 if kind == "psl" else p * (p * p - 1)
                if order < d + 1 or 2 * order > max_n or 2 * order <= best_n:
                    continue
                cands.append((order, p, kind))
        cands.sort()

        for idx, (order, p, kind) in enumerate(cands):
            now = time.monotonic()
            if now >= search_deadline:
                break
            remaining = search_deadline - now
            if idx == len(cands) - 1:
                slice_end = search_deadline
            else:
                slice_end = now + 0.5 * remaining
            try:
                G, mult, inv, e = _group_tables(p, kind)
            except Exception:
                continue
            if G < d:
                continue
            while time.monotonic() < slice_end:
                ok, S = _anneal(d, D, G, mult, inv, e, rng, slice_end, 20000)
                if ok:
                    n2, e2 = _graph(G, mult, S)
                    consider(n2, e2)
                    break
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
