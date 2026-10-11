import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe algebraic starting points (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez record graph when q = d - 2 is a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over Z_m x| Z_k2, searched by threshold accepting.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Layer L is a perfect matching i -> p_L(i) between the k A-orbits and k B-orbits;
# dart (i, j, s) joins A_i,g to B_j,mul(g,s) for every g. Each A and B vertex
# therefore has degree d (multi-edges collapse, which only lowers degree).
# ----------------------------------------------------------------------------

def _group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G, returned as (order, mul), or None."""
    divs = [k2 for k2 in range(1, 13) if G % k2 == 0 and G // k2 >= 2]
    rng.shuffle(divs)
    for k2 in divs:
        m = G // k2
        if k2 == 1:
            order, mul, _ = lib.cyclic_group(m)
            return order, mul
        cands = [r for r in range(1, m)
                 if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if cands:
            r = rng.choice(cands)
            order, mul, _ = lib.semidirect_group(m, k2, r)
            return order, mul
    return None


def _adj(k, G, darts, tbl):
    """Adjacency lists of the lift described by darts."""
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        t = tbl[s]
        for g in range(G):
            a = i * G + g
            b = (k + j) * G + t[g]
            adj[a].append(b)
            adj[b].append(a)
    return N, adj


def _cost(N, adj, D):
    """Number of ordered vertex pairs at distance > D (0 means diameter <= D)."""
    ball = [1 << v for v in range(N)]
    for _ in range(D):
        nb = [0] * N
        for v in range(N):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nb[v] = x
        ball = nb
    return sum(N - b.bit_count() for b in ball)


def _edges(k, G, darts, tbl):
    E = set()
    for i, j, s in darts:
        t = tbl[s]
        for g in range(G):
            E.add((i * G + g, (k + j) * G + t[g]))
    return 2 * k * G, sorted(E)


def _search(d, D, k, G, tbl, rng, deadline, iters):
    """Threshold-accepting search over voltages and layer matchings. Returns darts or None."""
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    N, adj = _adj(k, G, darts, tbl)
    cur = _cost(N, adj, D)

    for it in range(iters):
        if cur == 0:
            return darts
        if (it & 31) == 0 and time.monotonic() >= deadline:
            return None
        thr = 2.0 * (1.0 - it / iters)  # accept small uphill moves early, none late

        if k == 1 or rng.random() < 0.75:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            ns = rng.randrange(G)
            if ns == old:
                continue
            darts[idx][2] = ns
            kind = 0
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            kind = 1

        N, adj = _adj(k, G, darts, tbl)
        c2 = _cost(N, adj, D)
        if c2 - cur <= thr:
            cur = c2
        else:
            if kind == 0:
                darts[idx][2] = old
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
    return darts if cur == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    try:
        if D >= 3:
            ap = _araujo(d)
            if ap is not None:
                consider(ap[0], ap[1])
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])

        if D >= 3 and d >= 2:
            # Sweep lift orders upward from the current best; re-plan after each success.
            while time.monotonic() < deadline and best_n < lib.moore_bound(d, D):
                cands = []
                for k in (1, 2, 3, 4):
                    g0 = best_n // (2 * k) + 1
                    for G in range(g0, g0 + 3):
                        cands.append((2 * k * G, k, G))
                cands.sort()
                for n_c, k, G in cands[:6]:
                    if time.monotonic() >= deadline:
                        break
                    for _ in range(2):
                        grp = _group(G, rng)
                        if grp is None:
                            continue
                        order, mul = grp
                        tbl = [[mul(g, s) for g in range(order)] for s in range(order)]
                        darts = _search(d, D, k, order, tbl, rng, deadline, 2500)
                        if darts is not None:
                            n_e, e_e = _edges(k, order, darts, tbl)
                            consider(n_e, e_e)
                            break
                    if best_n >= n_c:
                        break
    except Exception:
        pass

    try:
        valid = lib.is_valid(best_n, best_e, d, D)
    except Exception:
        valid = False
    if not valid:
        return lib.haar_graph(d, range(d))
    return best_n, best_e
