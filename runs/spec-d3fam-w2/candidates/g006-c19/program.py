import math
import random
import time

import lib


def _fallback(d, D):
    """Verified baseline: K_{d,d} (diameter 2) or trivial graphs for small parameters."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    return lib.haar_graph(d, range(d))


def _group_list(N, rng):
    """Cyclic group of order N plus a few semidirect products Z_m x| Z_k of order N."""
    groups = [lib.cyclic_group(N)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:3]:
            try:
                groups.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return groups


def _tables(N, mul, inv):
    """Full multiplication table M[a][b] = a*b and inverse list I[b] = b^{-1}; identity is 0."""
    M = [[mul(a, b) for b in range(N)] for a in range(N)]
    I = [inv(b) for b in range(N)]
    return M, I


def _pair_add(cnt, S, skip, v, M, I, sign):
    """Add (sign=+1) or remove (sign=-1) the ordered differences of v against S[j], j != skip.

    Difference of a, b is a*b^{-1} = M[a][I[b]]. Returns the change in the number of
    uncovered group elements (cnt[g] == 0).
    """
    ch = 0
    for j, b in enumerate(S):
        if j == skip:
            continue
        for g in (M[v][I[b]], M[b][I[v]]):
            if sign > 0:
                if cnt[g] == 0:
                    ch -= 1
                cnt[g] += 1
            else:
                cnt[g] -= 1
                if cnt[g] == 0:
                    ch += 1
    return ch


def _move(cnt, S, i, x, M, I):
    """Replace S[i] by x, updating coverage counts; returns the change in uncovered count."""
    delta = _pair_add(cnt, S, i, S[i], M, I, -1)
    delta += _pair_add(cnt, S, i, x, M, I, +1)
    S[i] = x
    return delta


def _tabu(N, M, I, d, rng, steps, deadline):
    """Uncovered-difference-directed tabu search for a set S, |S| = d, with S S^{-1} = G.

    Each step picks a random uncovered group element g and proposes replacements
    x = g*s or x = g^{-1}*s for members s of S, which directly create the difference g.
    The best non-tabu proposal is applied even if it worsens the cover (tabu search).
    Returns S or None if the budget or deadline runs out.
    """
    S = rng.sample(range(N), d)
    cnt = [0] * N
    cnt[0] = 1  # identity is always covered
    for a in S:
        for b in S:
            if a != b:
                cnt[M[a][I[b]]] += 1
    unc = sum(1 for c in cnt if c == 0)
    best_unc = unc
    tabu = {}
    for it in range(steps):
        if unc == 0:
            return S
        if it % 64 == 0 and time.monotonic() >= deadline:
            return None
        zeros = [g for g in range(N) if cnt[g] == 0]
        g = rng.choice(zeros)
        inS = set(S)
        cands = set()
        for b in S:
            for x in (M[g][b], M[I[g]][b]):
                if x in inS:
                    continue
                for i in range(d):
                    cands.add((i, x))
        cand = list(cands)
        rng.shuffle(cand)
        cand = cand[:48]
        bestc = None
        bestv = None
        for i, x in cand:
            old = S[i]
            new = unc + _move(cnt, S, i, x, M, I)
            _move(cnt, S, i, old, M, I)
            if tabu.get((i, x), -1) > it and new >= best_unc:
                continue
            if bestv is None or new < bestv or (new == bestv and rng.random() < 0.5):
                bestv = new
                bestc = (i, x)
        if bestc is None:
            continue
        i, x = bestc
        old = S[i]
        unc += _move(cnt, S, i, x, M, I)
        tabu[(i, old)] = it + 7 + rng.randrange(8)
        if unc < best_unc:
            best_unc = unc
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 2.0)
    rng = random.Random(seed)

    best = _fallback(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Only diameter 3 is searched; other regimes use the baseline.
    if D != 3 or d < 3:
        return best

    # Moore-extremal case: incidence graph of PG(2, d-1) is optimal.
    if lib.is_prime_power(d - 1):
        try:
            consider(*lib.projective_plane_incidence(d - 1))
        except Exception:
            pass
        return best

    # Araujo-Pardo & Lopez record family for d = q + 2.
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Difference-cover group lifts: order 2N needs S S^{-1} = G with |S| = d.
    # Search N ascending with the directed tabu search; each success raises best_n.
    hi = d * (d - 1) + 1
    lo = max(best_n // 2 + 1, d)
    for N in range(lo, hi + 1):
        if time.monotonic() >= deadline:
            break
        if 2 * N <= best_n:
            continue
        groups = _group_list(N, rng)
        tables = [None] * len(groups)
        found = None
        now = time.monotonic()
        deadline_N = now + 0.5 * max(0.0, deadline - now)
        while found is None and time.monotonic() < deadline_N:
            for idx in range(len(groups)):
                if time.monotonic() >= deadline_N:
                    break
                if tables[idx] is None:
                    _, mul, inv = groups[idx]
                    tables[idx] = _tables(N, mul, inv)
                M, I = tables[idx]
                S = _tabu(N, M, I, d, rng, 2500, deadline_N)
                if S is not None:
                    found = (idx, S)
                    break
        if found is None:
            break
        idx, S = found
        mul = groups[idx][1]
        try:
            n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
            consider(n, edges)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        return _fallback(d, D)
    return best
