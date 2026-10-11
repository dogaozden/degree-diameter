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


def _group_list(N, rng, per_k=4):
    """Cyclic group of order N plus several semidirect products Z_m x| Z_k of order N."""
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
        for r in rs[:per_k]:
            try:
                groups.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return groups


def _ratio_table(N, mul, inv):
    """R[x][y] = x * y^{-1}."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


def _upd(cnt, R, S, skip, v, sign):
    """Add (sign=+1) or remove (sign=-1) ordered differences of v against S[j], j != skip.

    Returns the change in the number of uncovered group elements.
    """
    ch = 0
    Rv = R[v]
    for j, b in enumerate(S):
        if j == skip:
            continue
        for g in (Rv[b], R[b][v]):
            if sign > 0:
                if cnt[g] == 0:
                    ch -= 1
                cnt[g] += 1
            else:
                cnt[g] -= 1
                if cnt[g] == 0:
                    ch += 1
    return ch


def _tabu_cover(N, R, inv, mul, d, rng, max_steps, e, deadline):
    """Min-conflicts tabu search for d distinct elements S with S S^{-1} = G.

    New idea: instead of random annealing moves, pick a random UNCOVERED group element g.
    Any element x that would cover g against some s in S satisfies x = g*s or x = g^{-1}*s,
    so only those candidates are tried, each swapped into every position. A short tabu
    tenure on removed elements stops the search from cycling. Returns S or None.
    """
    S = rng.sample(range(N), d)
    cnt = [0] * N
    cnt[e] = 1
    for a in S:
        for b in S:
            if a != b:
                cnt[R[a][b]] += 1
    unc = sum(1 for c in cnt if c == 0)
    tabu_until = [0] * N

    for step in range(max_steps):
        if unc == 0:
            return S
        if (step & 31) == 0 and time.monotonic() >= deadline:
            return None

        uncovered = [x for x in range(N) if cnt[x] == 0]
        g = rng.choice(uncovered)
        ig = inv[g]
        cand = set()
        for s in S:
            cand.add(mul(g, s))
            cand.add(mul(ig, s))
        cand = [x for x in cand if x not in S and tabu_until[x] <= step]
        rng.shuffle(cand)
        cand = cand[:12]

        best_delta = None
        best_moves = []
        for x in cand:
            for i in range(d):
                old = S[i]
                dl = _upd(cnt, R, S, i, old, -1) + _upd(cnt, R, S, i, x, +1)
                _upd(cnt, R, S, i, x, -1)
                _upd(cnt, R, S, i, old, +1)
                if best_delta is None or dl < best_delta:
                    best_delta = dl
                    best_moves = [(i, x)]
                elif dl == best_delta:
                    best_moves.append((i, x))

        if best_delta is None:
            # All candidates tabu: random perturbation.
            i = rng.randrange(d)
            x = rng.randrange(N)
            if x in S:
                continue
        else:
            i, x = rng.choice(best_moves)

        old = S[i]
        unc += _upd(cnt, R, S, i, old, -1) + _upd(cnt, R, S, i, x, +1)
        S[i] = x
        tabu_until[old] = step + rng.randint(4, 8)
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

    # Moore-extremal case: incidence graph of PG(2, d-1).
    if lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best

    # Araujo-Pardo & Lopez family for d = q + 2.
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Difference-cover Haar lifts: order 2N needs S S^{-1} = G with |S| = d.
    # Only N with 2N > best_n can improve; search ascending, since each success
    # raises the bar and larger N is harder.
    hi = d * (d - 1) + 1
    lo = best_n // 2 + 1
    for N in range(max(lo, d), hi + 1):
        if time.monotonic() >= deadline:
            break
        try:
            groups = _group_list(N, rng)
            tables = [None] * len(groups)
            found = None
            now = time.monotonic()
            deadline_N = now + 0.6 * max(0.0, deadline - now)
            while found is None and time.monotonic() < deadline_N:
                for idx in range(len(groups)):
                    now = time.monotonic()
                    if now >= deadline_N:
                        break
                    order, mul, inv = groups[idx]
                    if tables[idx] is None:
                        tables[idx] = _ratio_table(N, mul, inv)
                    R = tables[idx]
                    attempt_deadline = min(deadline_N, now + 2.0)
                    S = _tabu_cover(N, R, inv, mul, d, rng, 4000, R[0][0], attempt_deadline)
                    if S is not None:
                        found = (idx, S)
                        break
            if found is None:
                break
            idx, S = found
            n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, groups[idx][1])
            consider(n, edges)
        except Exception:
            break

    return best
