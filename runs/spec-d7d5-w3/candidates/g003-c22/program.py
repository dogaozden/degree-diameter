import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baselines.
# ----------------------------------------------------------------------------

def _pg_baseline(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (degree q + 1 <= d)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New construction: bipartite double covers of Cayley graphs of finite groups.
#
# For a group G and a symmetric generating multiset S (|S| = d, identity excluded),
# the bipartite double of Cay(G, S) has vertices (g, 0), (g, 1) and edges
# (g, 0) -- (g s, 1) for s in S. It is d-regular and bipartite, with 2|G| vertices.
#
# Left multiplication is an automorphism, so the diameter condition reduces to
# two checks from the base points (e, 0) and (e, 1):
#   Ev = union of W_l for even l <= D covers G,
#   Od = union of W_l for odd  l <= D covers G,
# where W_l is the set of products of exactly l generators. The search therefore
# only needs a boolean-set propagation per candidate generator set, which makes
# the annealing cheap. Groups are PGL(2,q) and PSL(2,q) built from lib.GF(q) and
# stored as full multiplication tables.
# ----------------------------------------------------------------------------

def _code4(a, b, c, d, q):
    return ((a * q + b) * q + c) * q + d


def _linear_group(kind, q):
    """Return (K, MT, e, inv): |G|, multiplication table MT[i, j] = index of i*j, identity index, inverse indices."""
    F = lib.GF(q)
    mul = np.asarray(F.mul_table, dtype=np.int64)
    add = np.asarray(F.add_table, dtype=np.int64)
    neg = np.array([F.neg(a) for a in range(q)], dtype=np.int64)
    inv = np.array([0] + [F.inv(a) for a in range(1, q)], dtype=np.int64)

    A = np.array(list(itertools.product(range(q), repeat=4)), dtype=np.int64)
    a, b, c, d = A[:, 0], A[:, 1], A[:, 2], A[:, 3]
    det = add[mul[a, d], neg[mul[b, c]]]
    lead = np.where(a != 0, a, np.where(b != 0, b, np.where(c != 0, c, d)))
    keep = (det != 0) & (lead == 1)  # projectively normalised, invertible
    if kind == "PSL":
        squares = np.unique(mul[np.arange(q), np.arange(q)])
        keep &= np.isin(det, squares)
    els = A[keep]
    K = len(els)

    lut = np.full(q ** 4, -1, dtype=np.int64)
    lut[_code4(els[:, 0], els[:, 1], els[:, 2], els[:, 3], q)] = np.arange(K)

    h0, h1, h2, h3 = els[:, 0], els[:, 1], els[:, 2], els[:, 3]
    MT = np.empty((K, K), dtype=np.int64)
    for i in range(K):
        a1, b1, c1, d1 = (int(x) for x in els[i])
        r0 = add[mul[a1, h0], mul[b1, h2]]
        r1 = add[mul[a1, h1], mul[b1, h3]]
        r2 = add[mul[c1, h0], mul[d1, h2]]
        r3 = add[mul[c1, h1], mul[d1, h3]]
        ld = np.where(r0 != 0, r0, np.where(r1 != 0, r1, np.where(r2 != 0, r2, r3)))
        il = inv[ld]
        s = _code4(mul[il, r0], mul[il, r1], mul[il, r2], mul[il, r3], q)
        MT[i] = lut[s]
    if (MT < 0).any():
        raise ValueError("group closure failed")

    e = int(lut[_code4(1, 0, 0, 1, q)])
    inv_el = np.empty(K, dtype=np.int64)
    rows, cols = np.nonzero(MT == e)
    inv_el[rows] = cols
    return K, MT, e, inv_el


def _group_candidates():
    out = []
    for q in (3, 4, 5, 7, 8, 9, 11, 13):
        out.append(("PGL", q, q * (q * q - 1)))
        if q % 2 == 1:
            out.append(("PSL", q, q * (q * q - 1) // 2))
    out.sort(key=lambda t: -t[2])
    return out


def _cost(MTc, S, e, G, D):
    """Uncovered elements of Ev plus Od (0 iff the double cover has diameter <= D)."""
    W = np.zeros(G, dtype=bool)
    W[e] = True
    ev = W.copy()
    od = np.zeros(G, dtype=bool)
    for step in range(1, D + 1):
        idx = np.flatnonzero(W)
        Wn = np.zeros(G, dtype=bool)
        for s in S:
            Wn[MTc[s][idx]] = True
        W = Wn
        if step % 2 == 0:
            ev |= W
        else:
            od |= W
    return (G - int(ev.sum())) + (G - int(od.sum()))


def _search_group(G, MT, e, inv, d, D, rng, deadline):
    """Anneal over symmetric generator sets (involutions for odd d, inverse pairs). Returns S or None."""
    MTc = np.ascontiguousarray(MT.T)
    inv_list = inv.tolist()
    invs = [g for g in range(G) if g != e and inv_list[g] == g]
    k_inv = d % 2
    k_pair = d // 2
    if len(invs) < k_inv:
        return None

    def rand_inv(used):
        for _ in range(200):
            g = invs[rng.randrange(len(invs))]
            if g not in used:
                return (g,)
        return None

    def rand_pair(used):
        for _ in range(400):
            g = rng.randrange(G)
            h = inv_list[g]
            if g != e and h != g and g not in used and h not in used:
                return (g, h)
        return None

    def fresh():
        used = {e}
        blocks = []
        for _ in range(k_inv):
            b = rand_inv(used)
            if b is None:
                return None
            used.update(b)
            blocks.append(b)
        for _ in range(k_pair):
            b = rand_pair(used)
            if b is None:
                return None
            used.update(b)
            blocks.append(b)
        return blocks

    def flat(blocks):
        return [x for b in blocks for x in b]

    blocks = None
    while blocks is None and time.monotonic() < deadline:
        blocks = fresh()
    if blocks is None:
        return None

    cur = _cost(MTc, flat(blocks), e, G, D)
    best = cur
    last = 0
    it = 0
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        it += 1
        if it - last > 4000:
            nb = fresh()
            if nb is not None:
                blocks = nb
                cur = _cost(MTc, flat(blocks), e, G, D)
                best = cur
            last = it
            continue
        bi = rng.randrange(len(blocks))
        old = blocks[bi]
        used = {e}
        for j, b in enumerate(blocks):
            if j != bi:
                used.update(b)
        nb = rand_inv(used) if len(old) == 1 else rand_pair(used)
        if nb is None:
            continue
        cand = blocks[:bi] + [nb] + blocks[bi + 1:]
        c = _cost(MTc, flat(cand), e, G, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / 1.5):
            blocks, cur = cand, c
            if cur < best:
                best = cur
                last = it
    return flat(blocks)


def _graph(G, MT, S):
    """Bipartite double cover: (g, 0) = g, (g, 1) = G + g; edges (g,0)-(g*s,1)."""
    arr = MT[:, S].tolist()
    edges = []
    for g in range(G):
        for h in arr[g]:
            edges.append((g, G + h))
    return 2 * G, edges


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.8 * time_limit, time_limit - 6.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    best = (2, [(0, 1)])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _pg_baseline(d)
        if pg is not None:
            consider(*pg)
            if lib.is_prime_power(d - 1):
                return best

    consider(*lib.haar_graph(d, range(d)))

    maxG = lib.moore_bound(d, D) // 2
    cands = [c for c in _group_candidates() if c[2] <= maxG and 2 * c[2] > best[0]]

    for kind, q, order in cands:
        remaining = deadline - time.monotonic()
        if remaining < 1.0:
            break
        attempt_end = min(deadline, time.monotonic() + max(1.0, 0.4 * remaining))
        try:
            G, MT, e, inv = _linear_group(kind, q)
        except Exception:
            continue
        if 2 * G <= best[0] or G > maxG:
            continue
        S = _search_group(G, MT, e, inv, d, D, rng, attempt_end)
        if S is None:
            continue
        before = best[0]
        n, edges = _graph(G, MT, S)
        consider(n, edges)
        if best[0] > before:
            break

    return best
