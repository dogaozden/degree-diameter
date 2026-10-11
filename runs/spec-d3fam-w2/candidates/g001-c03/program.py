import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline: projective plane incidence graph (diameter 3, degree q+1 <= d).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley (Haar-type) graphs over abelian groups G of order m.
#
# Vertices a_g and b_g (g in G); a_g ~ b_{g+s} for s in S, |S| = d.
# Same-side distance 2 needs S - S = G; then cross-side distance <= 3.
# So diameter 3 holds iff S is a difference cover of G, and order 2m.
#
# NEW in this version: besides cyclic groups Z_m, we search non-cyclic
# abelian groups Z_a x Z_b (a*b = m). Their difference-cover landscape
# differs from the cyclic one, which gives extra chances at orders just
# above the record.
#
# NEW search: a focused WalkSAT-style annealer. Most moves pick a random
# uncovered group element r and choose x = r + S[j], so that x - S[j] = r
# is covered immediately. Other moves are uniform random for diversity.
# ----------------------------------------------------------------------------

def _group_types(m):
    """Abelian group types of order m as (a, b) with Z_a x Z_b; (1, m) is cyclic."""
    types = [(1, m)]
    a = 2
    while a * a <= m:
        if m % a == 0:
            types.append((a, m // a))
        a += 1
    return types


def _group_tables(a, b):
    """Addition and negation tables for Z_a x Z_b; element x*b + y codes (x, y)."""
    m = a * b
    add = [[0] * m for _ in range(m)]
    for x in range(m):
        x1, y1 = divmod(x, b)
        row = add[x]
        for y in range(m):
            x2, y2 = divmod(y, b)
            row[y] = ((x1 + x2) % a) * b + (y1 + y2) % b
    neg = [((-(x // b)) % a) * b + (-(x % b)) % b for x in range(m)]
    return add, neg


def _upd(cnt, S, skip, v, add, neg, sign):
    """Add (sign>0) or remove (sign<0) the ordered differences of v against all S[j], j != skip.

    Returns the change in the number of uncovered nonzero residues.
    """
    ch = 0
    for j, b in enumerate(S):
        if j == skip:
            continue
        for y in (add[v][neg[b]], add[b][neg[v]]):
            if sign > 0:
                if cnt[y] == 0:
                    ch -= 1
                cnt[y] += 1
            else:
                cnt[y] -= 1
                if cnt[y] == 0:
                    ch += 1
    return ch


def _cover_search(d, m, add, neg, rng, deadline):
    """Find S, |S| = d, 0 in S, with S - S = G for the group with tables (add, neg); None on timeout."""
    if m < d or m - 1 > d * (d - 1):
        return None
    S = [0] + rng.sample(range(1, m), d - 1)
    inS = set(S)
    cnt = [0] * m
    unc = m - 1
    for j in range(d):
        for k in range(j + 1, d):
            for y in (add[S[j]][neg[S[k]]], add[S[k]][neg[S[j]]]):
                if cnt[y] == 0:
                    unc -= 1
                cnt[y] += 1
    if unc == 0:
        return S

    start = time.monotonic()
    span = max(1e-3, deadline - start)
    frac = 0.0
    it = 0
    while unc > 0:
        it += 1
        if (it & 255) == 0:
            now = time.monotonic()
            if now >= deadline:
                return None
            frac = (now - start) / span
        T = 1.2 * (0.02 ** frac)

        if rng.random() < 0.8:
            # Focused move: cover a random uncovered residue r via x = r + S[j].
            while True:
                r = rng.randrange(1, m)
                if cnt[r] == 0:
                    break
            idx = rng.randrange(1, d)
            j = rng.randrange(d)
            if j == idx:
                continue
            x = add[r][S[j]]
        else:
            idx = rng.randrange(1, d)
            x = rng.randrange(1, m)
        if x in inS:
            continue

        old = S[idx]
        delta = _upd(cnt, S, idx, old, add, neg, -1) + _upd(cnt, S, idx, x, add, neg, +1)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[idx] = x
            inS.discard(old)
            inS.add(x)
            unc += delta
        else:
            _upd(cnt, S, idx, x, add, neg, -1)
            _upd(cnt, S, idx, old, add, neg, +1)
    return S


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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
        # Araujo-Pardo & Lopez record family for d = q + 2, q a prime power.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n_a, e_a = lib.araujo_lopez_graph(d - 2)
                consider(n_a, e_a)
            except Exception:
                pass
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

        # Search for difference covers of order m, aiming for 2m > current best.
        max_m = d * (d - 1) + 1
        m = max(d, best_n // 2 + 1)
        cache = {}
        while m <= max_m:
            now = time.monotonic()
            if now >= deadline:
                break
            per_m_end = now + max(0.5, 0.6 * (deadline - now))
            types = _group_types(m)
            rng.shuffle(types)
            found = None
            for (a, b) in types:
                now = time.monotonic()
                if now >= per_m_end:
                    break
                if (a, b) not in cache:
                    cache[(a, b)] = _group_tables(a, b)
                add, neg = cache[(a, b)]
                slice_end = min(per_m_end, now + max(0.5, 0.5 * (per_m_end - now)))
                S = _cover_search(d, m, add, neg, rng, slice_end)
                if S is not None:
                    found = (a, b, S)
                    break
            if found is None:
                break
            a, b, S = found
            add, _ = cache[(a, b)]
            edges = [(i, m + add[i][s]) for i in range(m) for s in S]
            consider(2 * m, edges)
            m += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
