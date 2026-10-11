import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline families for D = 3 and small cases.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# NEW MAIN FAMILY (D >= 5): bipartite Cayley graphs (Haar-type) over groups.
#
# For a finite group G with identity 0 and a connection set S (|S| = d, e in S):
#   A_g is adjacent to B_{g*s} for every s in S.
# Left translation is an automorphism, so the diameter is controlled by the
# eccentricities of A_e and B_e only. The search is over S, and the group is
# drawn from cyclic, affine (Z_p x| C_k) and semidirect (Z_m x| Z_k) families,
# so non-abelian groups are used heavily.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _is_prime(n):
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True


def _group_options(G, rng):
    """List candidate group descriptions of order G."""
    opts = [("cyc", G)]
    for k in range(2, G // 2 + 1):
        if G % k:
            continue
        m = G // k
        if m < 3:
            continue
        if _is_prime(m) and (m - 1) % k == 0:
            opts.append(("aff", m, k))
        opts.append(("sd", m, k))
    return opts


def _make_group(opt, rng):
    """Return (order, mul) for a group option, or None if it cannot be built."""
    kind = opt[0]
    if kind == "cyc":
        G = opt[1]
        return G, (lambda x, y: (x + y) % G)
    if kind == "aff":
        p, k = opt[1], opt[2]
        H = [a for a in range(1, p) if pow(a, k, p) == 1]
        if len(H) != k:
            return None
        aidx = [0] * p
        for i, a in enumerate(H):
            aidx[a] = i

        def mul(x, y):
            a, b = divmod(x, p)
            c, e = divmod(y, p)
            A = H[a]
            return aidx[A * H[c] % p] * p + (A * e + b) % p

        return p * k, mul
    m, k = opt[1], opt[2]
    rs = [r for r in rng.sample(range(2, m), min(m - 2, 40))
          if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
    if not rs:
        return None
    order, mul, _ = lib.semidirect_group(m, k, rng.choice(rs))
    return order, mul


def _group_table(G, mul):
    """Full multiplication table M[g][s] and inverse list; identity must be index 0."""
    M = [[mul(g, s) for s in range(G)] for g in range(G)]
    inv = [row.index(0) for row in M]
    return M, inv


def _bfs_unreached(src, G, M, S, Sinv, D):
    """Number of vertices of the bigraph (2G vertices) not within distance D of src."""
    seen = bytearray(2 * G)
    seen[src] = 1
    frontier = [src]
    cnt = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            if u < G:
                row = M[u]
                for s in S:
                    v = G + row[s]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            else:
                row = M[u - G]
                for si in Sinv:
                    v = row[si]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
        if not nxt:
            break
        cnt += len(nxt)
        frontier = nxt
    return 2 * G - cnt


def _cayley_cost(G, M, inv, S, D):
    Sinv = [inv[s] for s in S]
    return _bfs_unreached(0, G, M, S, Sinv, D) + _bfs_unreached(G, G, M, S, Sinv, D)


def _cayley_anneal(G, M, inv, d, D, rng, deadline, iters):
    """Anneal a connection set S (size d, containing identity) to diameter <= D."""
    if d < 2 or d - 1 > G - 1:
        return None
    S = [0] + rng.sample(range(1, G), d - 1)
    c = _cayley_cost(G, M, inv, S, D)
    T = 1.0
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        j = rng.randrange(1, d)
        x = rng.randrange(1, G)
        if x in S:
            continue
        old = S[j]
        S[j] = x
        c2 = _cayley_cost(G, M, inv, S, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            c = c2
        else:
            S[j] = old
        T = max(0.1, T * 0.997)
    return S if c == 0 else None


def _cayley_graph(G, M, S):
    edges = [(g, G + M[g][s]) for g in range(G) for s in S]
    return 2 * G, edges


def _cayley_phase(d, D, deadline, rng, consider, get_n):
    """Search Cayley bigraphs of increasing order until the deadline."""
    hi = lib._moore_bound(d, D) // 2
    lo = max(get_n() // 2 + 1, int(0.4 * hi))
    while time.monotonic() < deadline and lo <= hi:
        G = min(hi, lo + int(rng.random() * 60))
        opts = _group_options(G, rng)
        rng.shuffle(opts)
        for opt in opts[:4]:
            if time.monotonic() >= deadline:
                return
            made = _make_group(opt, rng)
            if made is None:
                continue
            order, mul = made
            if order != G:
                continue
            M, inv = _group_table(G, mul)
            per = min(deadline, time.monotonic() + 4.0)
            S = _cayley_anneal(G, M, inv, d, D, rng, per, 2500)
            if S is not None:
                n, e = _cayley_graph(G, M, S)
                consider(n, e)
                lo = max(lo, G + 1)
                break


# ----------------------------------------------------------------------------
# Secondary family (D >= 5): multi-vertex voltage lifts over semidirect groups.
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    for _ in range(40):
        k2 = rng.choice([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        order, mul, _ = lib.semidirect_group(m, k2, r)
        return order, mul
    return None


def _random_darts(d, k, G, rng):
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    return darts


def _vcost(k, G, D, darts, perms):
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _vedges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _voltage_anneal(d, D, k, G, mul, rng, deadline, iters):
    darts = _random_darts(d, k, G, rng)
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    cost = _vcost(k, G, D, darts, perms)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old_s, old_p = darts[idx][2], perms[idx]
            new_s = rng.randrange(G)
            darts[idx][2] = new_s
            perms[idx] = [mul(g, new_s) for g in range(G)]
            c2 = _vcost(k, G, D, darts, perms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_p
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _vcost(k, G, D, darts, perms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
        T = max(0.1, T * 0.997)
    if cost == 0:
        return _vedges(k, G, darts, perms)
    return None


def _voltage_phase(d, D, deadline, rng, consider, get_n):
    while time.monotonic() < deadline:
        k = rng.choice([2, 2, 3, 4])
        base = get_n() // (2 * k)
        lo = max(2, base + 1)
        G = rng.randint(lo, max(lo + 3, lo * 9 // 8))
        made = _sample_group(G, rng)
        if made is None:
            continue
        order, mul = made
        res = _voltage_anneal(d, D, k, order, mul, rng, deadline, 800)
        if res is not None:
            consider(res[0], res[1])


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    box = [lib.haar_graph(d, range(d))]

    def get_n():
        return box[0][0]

    def consider(n, e):
        if n > box[0][0] and lib.is_valid(n, e, d, D):
            box[0] = (n, e)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D >= 5 and d >= 2:
        _cayley_phase(d, D, start + 0.7 * time_limit, rng, consider, get_n)
        _voltage_phase(d, D, deadline, rng, consider, get_n)

    n, e = box[0]
    if not lib.is_valid(n, e, d, D):
        return lib.haar_graph(d, range(d))
    return n, e
