import math
import random
import time

import lib


_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Projective plane base (diameter 3 candidate).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New family for D = 3: cyclic Haar graphs H(m, S) with |S| = d.
# H(m, S) is bipartite, d-regular on 2m vertices, and has diameter <= 3
# exactly when S - S covers all of Z_m. Searching for such S by annealing
# over difference counts is a construction independent of the projective
# plane and the Araujo-Pardo-Lopez family.
# ----------------------------------------------------------------------------

def _haar_swap(cnt, S, i, new, m, d):
    """Replace S[i] by new, updating ordered-difference counts; return change in uncovered residues."""
    old = S[i]
    delta = 0
    for j in range(d):
        if j == i:
            continue
        b = S[j]
        for x in ((old - b) % m, (b - old) % m):
            cnt[x] -= 1
            if cnt[x] == 0:
                delta += 1
    for j in range(d):
        if j == i:
            continue
        b = S[j]
        for x in ((new - b) % m, (b - new) % m):
            if cnt[x] == 0:
                delta -= 1
            cnt[x] += 1
    S[i] = new
    return delta


def _haar_cover_sa(d, m, rng, deadline):
    """Find S in Z_m, |S| = d, 0 in S, with S - S = Z_m. Returns S or None."""
    if m - 1 > d * (d - 1):
        return None
    S = [0] + rng.sample(range(1, m), d - 1)
    inS = [False] * m
    for s in S:
        inS[s] = True
    cnt = [0] * m
    for a in S:
        for b in S:
            if a != b:
                cnt[(a - b) % m] += 1
    unc = sum(1 for x in range(1, m) if cnt[x] == 0)
    cycle = 200000
    it = 0
    while unc > 0:
        if (it & 1023) == 0 and time.monotonic() > deadline:
            return None
        frac = (it % cycle) / cycle
        T = 0.8 * (0.03 / 0.8) ** frac
        it += 1
        i = rng.randrange(1, d)
        new = rng.randrange(1, m)
        if inS[new]:
            continue
        old = S[i]
        du = _haar_swap(cnt, S, i, new, m, d)
        if du <= 0 or rng.random() < math.exp(-du / T):
            inS[old] = False
            inS[new] = True
            unc += du
        else:
            _haar_swap(cnt, S, i, old, m, d)
    return S


def _haar_ladder(d, m, deadline, rng, consider):
    """Try Haar covering graphs for m, m+1, ... while the search keeps succeeding."""
    while m - 1 <= d * (d - 1) and time.monotonic() < deadline:
        now = time.monotonic()
        S = _haar_cover_sa(d, m, rng, now + 0.5 * (deadline - now))
        if S is None:
            return
        consider(*lib.haar_graph(m, S))
        m += 1


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products (fallback for other cases).
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8])
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
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _cost(k, G, D, darts, perms, limit):
    """Number of (representative, vertex) pairs not reached within distance D; early exit above limit."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            a = i * G + g
            b = (k + j) * G + pm[g]
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
        if total > limit:
            return total
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Threshold-accepting annealing over voltages and layer assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms, float("inf"))

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = 1.0 * (0.05 ** (it / iters))
        limit = cost - T * math.log(1.0 - rng.random())
        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = [mul(g, new_s) for g in range(G)]
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        # Araujo-Pardo & Lopez record family for d = q + 2 with q a prime power.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        # Plain projective plane as a baseline.
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D == 3:
        # Bold new family: cyclic Haar graphs found by difference-covering search,
        # starting just above the current best order so every success is a gain.
        _haar_ladder(d, best_n // 2 + 1, start + 0.55 * time_limit, rng, consider)

    if D >= 3:
        ks = [1, 2, 2, 3]
        while time.monotonic() < deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, deadline, iters=1200)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
