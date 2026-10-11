import itertools
import math
import random
import time

import numpy as np

import lib


_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_GROUP_CACHE = {}
_MAX_G = 1400
_MAX_N = 3200


# ----------------------------------------------------------------------------
# Exact baseline: projective plane incidence graphs (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Group tables.
# Prime-field matrix groups SL(2,p), PSL(2,p), PGL(2,p), built with numpy,
# and semidirect products Z_m x| Z_k2 built the same way.
# Each group is returned as (G, mul, identity_index), where mul[x, y] = x*y.
# ----------------------------------------------------------------------------

def _prime_group(kind, p):
    grid = np.array(list(itertools.product(range(p), repeat=4)), dtype=np.int64)
    a, b, c, dd = grid[:, 0], grid[:, 1], grid[:, 2], grid[:, 3]
    det = (a * dd - b * c) % p
    keep = (det != 0) if kind == "PGL" else (det == 1)
    a, b, c, dd = a[keep], b[keep], c[keep], dd[keep]

    def code(x, y, z, w):
        return ((x * p + y) * p + z) * p + w

    def canon(x, y, z, w):
        if kind == "PSL":
            return np.minimum(code(x, y, z, w),
                              code((-x) % p, (-y) % p, (-z) % p, (-w) % p))
        if kind == "PGL":
            best = code(x, y, z, w)
            for lam in range(2, p):
                best = np.minimum(best, code((lam * x) % p, (lam * y) % p,
                                             (lam * z) % p, (lam * w) % p))
            return best
        return code(x, y, z, w)

    E = np.unique(canon(a, b, c, dd))
    G = len(E)
    lookup = np.full(p ** 4, -1, dtype=np.int64)
    lookup[E] = np.arange(G, dtype=np.int64)
    ra = E // p ** 3
    rb = (E // p ** 2) % p
    rc = (E // p) % p
    rd = E % p
    na = (ra[:, None] * ra[None, :] + rb[:, None] * rc[None, :]) % p
    nb = (ra[:, None] * rb[None, :] + rb[:, None] * rd[None, :]) % p
    nc = (rc[:, None] * ra[None, :] + rd[:, None] * rc[None, :]) % p
    nd = (rc[:, None] * rb[None, :] + rd[:, None] * rd[None, :]) % p
    mul = lookup[canon(na, nb, nc, nd)]
    if (mul < 0).any():
        return None
    ec = int(canon(np.array([1]), np.array([0]), np.array([0]), np.array([1]))[0])
    e = int(lookup[ec])
    if e < 0:
        return None
    return G, mul, e


def _get_prime(kind, p):
    key = (kind, p)
    if key not in _GROUP_CACHE:
        if len(_GROUP_CACHE) > 6:
            _GROUP_CACHE.clear()
        try:
            _GROUP_CACHE[key] = _prime_group(kind, p)
        except Exception:
            _GROUP_CACHE[key] = None
    return _GROUP_CACHE[key]


def _sample_semidirect(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 6, 8])
        m = max(3, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            cands = [c for c in range(1, m)
                     if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        return m, k2, r
    return None


def _semidirect_mul(m, k2, r):
    """Element (a, b) is coded a*k2 + b with (a,b)(c,e) = (a + r^b c, b + e)."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    pw = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    mul = ((a[:, None] + pw[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    return G, mul, 0


def _inverse_table(mul, e):
    G = mul.shape[0]
    inv = np.empty(G, dtype=np.int64)
    rows, cols = np.nonzero(mul == e)
    inv[rows] = cols
    return inv


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over a finite group.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{p,h} = (k+p)*G + h.
# Layer l is a permutation layers[l] of the k blocks, with voltage S[l][i]:
#   A_{i,g} ~ B_{layers[l][i], g*s}.
# Every vertex gets degree d. Left multiplication is an automorphism, so the
# identity of each of the 2k blocks represents all orbits.
# ----------------------------------------------------------------------------

def _search(d, D, k, G, mul, e, rng, deadline, iters, patience):
    """Simulated annealing on layers and voltages. Returns (n, edges) or None."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    Rt = np.ascontiguousarray(mul.T)  # Rt[s, g] = g*s
    inv = _inverse_table(mul, e)
    Rinv = Rt[inv]                    # Rinv[s, h] = h*s^{-1}

    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)

    def set_layer(l):
        lay = layers[l]
        sl = S[l]
        for i in range(k):
            p = lay[i]
            s = sl[i]
            nbr[l, i * G:(i + 1) * G] = (k + p) * G + Rt[s]
            nbr[l, (k + p) * G:(k + p + 1) * G] = i * G + Rinv[s]

    def dupcount():
        keys = {(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)}
        return d * k - len(keys)

    def evaluate():
        reach = np.zeros(N, dtype=np.int64)
        for b in range(2 * k):
            reach[b * G + e] = 1 << b
        for _ in range(D):
            new = reach.copy()
            for l in range(d):
                new |= reach[nbr[l]]
            if np.array_equal(new, reach):
                break
            reach = new
        cost = 2 * k * N - int(_POP[reach].sum()) + _PENALTY * dupcount()
        return cost, reach

    for l in range(d):
        set_layer(l)
    cost, reach = evaluate()
    c0 = float(max(cost, 1))
    best_cost = cost
    last_improve = 0

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last_improve > patience:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))

        if k >= 2 and rng.random() < 0.25:
            # Layer-swap move.
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            lay = layers[l]
            lay[i1], lay[i2] = lay[i2], lay[i1]
            set_layer(l)
            c2, r2 = evaluate()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
                if cost < best_cost:
                    best_cost, last_improve = cost, t
            else:
                lay[i1], lay[i2] = lay[i2], lay[i1]
                set_layer(l)
            continue

        # Voltage move, defect-targeted with probability 0.4.
        bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
            l = rng.randrange(d)
            if block < k:
                i = block
            else:
                i = layers[l].index(block - k)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        set_layer(l)
        c2, r2 = evaluate()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
            if cost < best_cost:
                best_cost, last_improve = cost, t
        else:
            S[l][i] = old
            set_layer(l)

    if cost != 0:
        return None
    nb = nbr.T.tolist()
    edges = [(u, v) for u in range(k * G) for v in nb[u]]
    return N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 7.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
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

    # Candidate prime-field groups with k blocks per side.
    prime = []
    for kind in ("PSL", "PGL", "SL"):
        for p in (5, 7, 11, 13):
            order = p * (p * p - 1) // (2 if kind == "PSL" else 1)
            if order > _MAX_G:
                continue
            for k in range(1, 7):
                if 2 * k * order <= _MAX_N:
                    prime.append((kind, p, k, order))

    while time.monotonic() < deadline:
        cands = [c for c in prime if 2 * c[2] * c[3] > best_n]
        if cands and rng.random() < 0.6:
            cands.sort(key=lambda c: 2 * c[2] * c[3])
            kind, p, k, G = cands[int(len(cands) * rng.random() ** 2)]
            grp = _get_prime(kind, p)
            if grp is None or grp[0] != G:
                continue
            _, mul, e = grp
        else:
            k = rng.randint(1, 4)
            base = best_n // (2 * k)
            target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
            sg = _sample_semidirect(target, rng)
            if sg is None:
                continue
            m, k2, r = sg
            G, mul, e = _semidirect_mul(m, k2, r)
            if 2 * k * G <= best_n or G > _MAX_G or 2 * k * G > _MAX_N:
                continue

        res = _search(d, D, k, G, mul, e, rng, deadline, 4000, 1000)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
