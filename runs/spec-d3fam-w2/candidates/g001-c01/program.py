import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Haar-type bipartite graphs over an arbitrary finite group G of order M.
#
# Vertices a_x (x in G) and b_y (y in G), with a_x ~ b_{x*s} for s in S, |S| = d.
# The graph is d-regular and bipartite. Same-side distance is at most 2 when
# S * S^{-1} = G, and cross-side distance is then at most 3. So diameter <= 3
# holds exactly when S S^{-1} covers G. This is a difference cover in a
# (possibly non-abelian) group. Since |S S^{-1}| <= d(d-1)+1, we get
# M <= d(d-1)+1, i.e. order <= 2(d(d-1)+1).
#
# Cyclic groups alone are the parent's approach. Here we also use semidirect
# products Z_m x|_r Z_k, which can allow larger covers.
# ----------------------------------------------------------------------------


def _group_candidates(M, rng, max_nonabelian=6):
    """Return a list of (mul_table, inv_list) for groups of order M (cyclic plus some semidirect)."""
    specs = []
    for k in range(2, M):
        if M % k:
            continue
        m = M // k
        if m < 3:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                specs.append((m, k, r))
    rng.shuffle(specs)

    groups = [lib.cyclic_group(M)]
    for m, k, r in specs[:max_nonabelian]:
        try:
            groups.append(lib.semidirect_group(m, k, r))
        except ValueError:
            pass

    out = []
    for order, mul, inv in groups:
        if order != M:
            continue
        mt = [[mul(x, y) for y in range(M)] for x in range(M)]
        iv = [inv(x) for x in range(M)]
        out.append((mt, iv))
    return out


def _targets(y, S, i, mt, iv):
    """Products s * t^{-1} involving the element y at position i, with the other elements of S."""
    out = [0]  # y * y^{-1} = identity
    for j, s in enumerate(S):
        if j != i:
            out.append(mt[y][iv[s]])
            out.append(mt[s][iv[y]])
    return out


def _upd(cnt, targets, sign):
    """Add (sign=+1) or remove (sign=-1) the given targets. Returns the change in uncovered count."""
    ch = 0
    if sign > 0:
        for g in targets:
            if cnt[g] == 0:
                ch -= 1
            cnt[g] += 1
    else:
        for g in targets:
            cnt[g] -= 1
            if cnt[g] == 0:
                ch += 1
    return ch


def _anneal_cover(d, M, mt, iv, rng, deadline):
    """Find S of size d in a group of order M with S S^{-1} = G (S[0] = identity). None on timeout."""
    if M < d or d < 2:
        return None
    S = [0] + rng.sample(range(1, M), d - 1)
    cnt = [0] * M
    for s in S:
        for t in S:
            cnt[mt[s][iv[t]]] += 1
    unc = sum(1 for c in cnt if c == 0)
    if unc == 0:
        return S

    start = time.monotonic()
    span = max(1e-6, deadline - start)
    it = 0
    frac = 0.0
    while True:
        it += 1
        if (it & 255) == 0:
            now = time.monotonic()
            if now >= deadline:
                return None
            frac = (now - start) / span
        i = rng.randrange(1, d)
        x = rng.randrange(1, M)
        if x in S:
            continue
        old = S[i]
        tr_old = _targets(old, S, i, mt, iv)
        ch1 = _upd(cnt, tr_old, -1)
        tr_new = _targets(x, S, i, mt, iv)
        ch2 = _upd(cnt, tr_new, +1)
        delta = ch1 + ch2
        T = 0.5 * (0.05 ** frac)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = x
            unc += delta
            if unc == 0:
                return S
        else:
            _upd(cnt, tr_new, -1)
            _upd(cnt, tr_old, +1)


def _haar_group_edges(M, S, mt):
    """Edges of the group Haar graph: a_x = x, b_y = M + y, a_x ~ b_{x*s}."""
    return [(x, M + mt[x][s]) for x in range(M) for s in S]


# ----------------------------------------------------------------------------

def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.72 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        # Known constructions.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n_a, e_a = lib.araujo_lopez_graph(d - 2)
                consider(n_a, e_a)
            except Exception:
                pass
        try:
            pg = _pg_candidate(d)
            if pg is not None:
                consider(pg[0], pg[1])
        except Exception:
            pass

        # Main search: group Haar graphs with S S^{-1} = G, for orders M
        # that would strictly beat the current best (order 2M).
        if d >= 3 and time.monotonic() < deadline:
            M = best[0] // 2 + 1
            M_hi = d * (d - 1) + 1
            fails = 0
            while M <= M_hi and time.monotonic() < deadline:
                groups = _group_candidates(M, rng)
                found = None
                for mt, iv in groups:
                    now = time.monotonic()
                    if now >= deadline:
                        break
                    slice_t = max(0.5, (deadline - now) * 0.08)
                    S = _anneal_cover(d, M, mt, iv, rng, min(deadline, now + slice_t))
                    if S is not None:
                        found = (mt, S)
                        break
                if found is not None:
                    mt, S = found
                    consider(2 * M, _haar_group_edges(M, S, mt))
                    fails = 0
                else:
                    fails += 1
                    if fails >= 2:
                        break
                M += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
