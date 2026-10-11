import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Algebraic baselines: projective plane (D >= 3) and Araujo-Pardo-Lopez (D = 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (q capped for speed)."""
    for q in range(min(d - 1, 31), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New engine: bi-Cayley lifts over semidirect products Z_m x| Z_k2.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h.
# Layer L is a perfect matching between A_i and B_{p_L(i)}; each dart
# (i, j, s) joins A_i,g to B_j,(g*s) for every g. Left translations are
# automorphisms, so one representative per base vertex suffices for the
# diameter check (2k BFS runs).
#
# Construction: greedy voltage assignment (maximising total reach from the
# representatives), followed by annealing over voltages and layer-wise
# partner swaps. Sizes are chosen by bisection on the target order.
# ----------------------------------------------------------------------------

def _reps(k, G):
    return [i * G for i in range(k)] + [(k + j) * G for j in range(k)]


def _perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _adjacency(N, k, G, darts):
    adj = [[] for _ in range(N)]
    for i, j, _s, perm in darts:
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + perm[g]
            adj[a].append(b)
            adj[b].append(a)
    return adj


def _reach(adj, N, src, D):
    """Number of vertices within distance D of src."""
    seen = bytearray(N)
    seen[src] = 1
    frontier = [src]
    cnt = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            for v in adj[u]:
                if not seen[v]:
                    seen[v] = 1
                    nxt.append(v)
        if not nxt:
            break
        cnt += len(nxt)
        frontier = nxt
    return cnt


def _full_cost(k, G, D, darts):
    """Number of (representative, vertex) pairs at distance > D. Zero means valid."""
    N = 2 * k * G
    adj = _adjacency(N, k, G, darts)
    total = 0
    for src in _reps(k, G):
        total += N - _reach(adj, N, src, D)
    return total


def _unique(darts):
    return len({(x[0], x[1], x[2]) for x in darts}) == len(darts)


def _edges(k, G, darts):
    E = []
    for i, j, _s, perm in darts:
        for g in range(G):
            E.append((i * G + g, (k + j) * G + perm[g]))
    return 2 * k * G, E


def _pick_group(G, rng):
    """Random semidirect product Z_m x| Z_k2 of order G (k2 <= 12), or None."""
    opts = [k2 for k2 in range(1, 13) if G % k2 == 0 and G // k2 >= 2]
    if not opts:
        return None
    rng.shuffle(opts)
    for k2 in opts[:6]:
        m = G // k2
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in range(1, m)
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _greedy(k, G, d, D, mul, rng, deadline):
    """Assign voltages dart by dart, maximising total reach of the partial lift."""
    N = 2 * k * G
    reps = _reps(k, G)
    adj = [[] for _ in range(N)]
    darts = []
    used = set()
    for _L in range(d):
        js = rng.sample(range(k), k)
        for i in range(k):
            if time.monotonic() > deadline:
                return None
            j = js[i]
            opts = [s for s in range(G) if (i, j, s) not in used]
            if not opts:
                return None
            if len(opts) > 12:
                opts = rng.sample(opts, 12)
            ba = i * G
            bb = (k + j) * G
            best_key, best_s = None, None
            for s in opts:
                perm = _perm(mul, G, s)
                for g in range(G):
                    adj[ba + g].append(bb + perm[g])
                    adj[bb + perm[g]].append(ba + g)
                tot = 0
                for src in reps:
                    tot += _reach(adj, N, src, D)
                for g in range(G):
                    adj[ba + g].pop()
                    adj[bb + perm[g]].pop()
                key = (tot, rng.random())
                if best_key is None or key > best_key:
                    best_key, best_s = key, s
            perm = _perm(mul, G, best_s)
            for g in range(G):
                adj[ba + g].append(bb + perm[g])
                adj[bb + perm[g]].append(ba + g)
            darts.append([i, j, best_s, perm])
            used.add((i, j, best_s))
    return darts


def _anneal(k, G, D, d, mul, darts, rng, deadline):
    """Annealed moves on voltages and layer partner swaps. Returns the final cost."""
    cost = _full_cost(k, G, D, darts)
    T = 1.0
    while cost > 0 and time.monotonic() < deadline:
        T = max(0.25, T * 0.998)
        if k > 1 and rng.random() < 0.3:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            if not _unique(darts):
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
                continue
            new = _full_cost(k, G, D, darts)
            if new <= cost or rng.random() < math.exp(-(new - cost) / T):
                cost = new
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
        else:
            idx = rng.randrange(len(darts))
            s_new = rng.randrange(G)
            if s_new == darts[idx][2]:
                continue
            old_s, old_perm = darts[idx][2], darts[idx][3]
            darts[idx][2] = s_new
            darts[idx][3] = _perm(mul, G, s_new)
            if not _unique(darts):
                darts[idx][2], darts[idx][3] = old_s, old_perm
                continue
            new = _full_cost(k, G, D, darts)
            if new <= cost or rng.random() < math.exp(-(new - cost) / T):
                cost = new
            else:
                darts[idx][2], darts[idx][3] = old_s, old_perm
    return cost


def _attempt(d, D, k, G, rng, deadline):
    """Try to find a valid lift with k base vertices per side and group order G. Returns darts or None."""
    g = _pick_group(G, rng)
    if g is None:
        return None
    mul = g[1]
    while time.monotonic() < deadline:
        darts = _greedy(k, G, d, D, mul, rng, deadline)
        if darts is None:
            return None
        if _full_cost(k, G, D, darts) == 0:
            return darts
        left = deadline - time.monotonic()
        if left <= 0:
            return None
        sub = min(deadline, time.monotonic() + max(0.5, 0.6 * left))
        if _anneal(k, G, D, d, mul, darts, rng, sub) == 0:
            return darts
    return None


def _engine(d, D, rng, deadline, base_n, consider):
    """Bisection over target order; each success is validated and offered to consider()."""
    t0 = time.monotonic()
    span = max(1.0, deadline - t0)
    budget_each = max(2.0, 0.07 * span)
    moore = lib.moore_bound(d, D)
    cap = 4000
    lo = base_n
    hi = min(cap, max(base_n + 4, int(0.45 * moore)))
    goal = min(hi, max(base_n + 4, int(0.3 * moore)))
    ks = [1, 1, 2, 2, 3, 4]
    while time.monotonic() < deadline - 0.2:
        k = rng.choice(ks)
        G = max(2, -(-goal // (2 * k)))
        until = min(deadline, time.monotonic() + budget_each)
        darts = _attempt(d, D, k, G, rng, until)
        if darts is not None:
            n, e = _edges(k, G, darts)
            consider(n, e)
            lo = max(lo, n)
            hi = max(hi, lo + 2 * k)
            hi = min(hi, cap)
        else:
            hi = min(hi, goal - 1)
        if hi <= lo:
            hi = min(cap, lo + max(4, lo // 10))
        if lo >= cap:
            break
        goal = max((lo + hi) // 2, lo + 2)
        goal = min(goal, cap)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
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

    try:
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
        if D == 3:
            ar = _araujo(d)
            if ar is not None:
                consider(ar[0], ar[1])
    except Exception:
        pass

    if D >= 4 and time.monotonic() < deadline:
        try:
            _engine(d, D, rng, deadline, best_n, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
