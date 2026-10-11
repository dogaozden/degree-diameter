import math
import random
import time

import lib


def _fallback(d, D):
    """Safe, verified-by-construction graphs used whenever the search fails."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]
    if D == 2:
        return lib.haar_graph(d, range(d))          # K_{d,d}, diameter 2
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)  # Moore-extremal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)    # record construction
        except Exception:
            pass
    return lib.haar_graph(d, range(d))


# ------------------------------------------------ Cayley-type bipartite lifts
#
# Two base vertices a, b with darts (a, b, s) for s in S give the bipartite
# graph on G x {0,1} with a_x ~ b_{x s}. Its diameter is at most 3 exactly when
# S S^{-1} = G. So the task is a "difference cover" of size d in a group G,
# giving order 2|G|.
#
# This version replaces the parent's annealing with a tabu search over
# explicit swap moves (best-of-sampled-neighbourhood, with a tabu list on
# recently removed elements), and schedules groups in a sliding window just
# above the current best order, smallest first, so improvements are banked
# incrementally.

WINDOW = 8     # number of consecutive group orders attempted at once
GROUPS = 4     # groups tried per order (cyclic plus up to 3 semidirect)
CAND = 24      # sampled replacement candidates per position per move
STALL = 1500   # non-improving moves before a random restart


def _group_list(N, rng):
    """Candidate groups of order N: cyclic, plus semidirect Z_m x| Z_k."""
    groups = [lib.cyclic_group(N)]
    options = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                options.append((m, k, r))
    rng.shuffle(options)
    for m, k, r in options[:GROUPS - 1]:
        try:
            groups.append(lib.semidirect_group(m, k, r))
        except ValueError:
            pass
    return groups


def _ratio_table(N, mul, inv):
    """R[x][y] = x * y^{-1}, as a list of lists."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


def _pair_update(cnt, R, e, others, sign):
    """Add (sign=+1) or remove (sign=-1) all ordered pairs involving e.

    Returns the change in the number of zero entries of cnt.
    """
    change = 0
    row = R[e]
    gs = [row[e]] + [row[o] for o in others] + [R[o][e] for o in others]
    if sign > 0:
        for g in gs:
            if cnt[g] == 0:
                change -= 1
            cnt[g] += 1
    else:
        for g in gs:
            cnt[g] -= 1
            if cnt[g] == 0:
                change += 1
    return change


def _tabu_search(N, mul, inv, d, rng):
    """Generator: tabu search for d elements S with S S^{-1} = G.

    Yields None after each move (so the driver can round-robin many groups)
    and yields the cover S once found.
    """
    if N - d < 1:
        return
    R = _ratio_table(N, mul, inv)
    K = min(N - d, CAND)
    while True:
        S = rng.sample(range(N), d)
        inS = set(S)
        cnt = [0] * N
        for a in S:
            for b in S:
                cnt[R[a][b]] += 1
        zeros = cnt.count(0)
        tabu = {}
        best_local = zeros
        stall = 0
        it = 0
        while zeros > 0 and stall < STALL:
            it += 1
            yield None
            best_move = None
            best_val = None
            for i in range(d):
                old = S[i]
                others = S[:i] + S[i + 1:]
                rem = _pair_update(cnt, R, old, others, -1)
                base = zeros + rem
                cands = []
                tries = 0
                while len(cands) < K and tries < 3 * K:
                    tries += 1
                    x = rng.randrange(N)
                    if x in inS or x in cands:
                        continue
                    cands.append(x)
                for x in cands:
                    add = _pair_update(cnt, R, x, others, 1)
                    val = base + add
                    _pair_update(cnt, R, x, others, -1)
                    if tabu.get(x, 0) > it and val >= best_local:
                        continue
                    if (best_val is None or val < best_val
                            or (val == best_val and rng.random() < 0.5)):
                        best_val = val
                        best_move = (i, x)
                _pair_update(cnt, R, old, others, 1)
            if best_move is None:
                stall += 1
                continue
            i, x = best_move
            old = S[i]
            others = S[:i] + S[i + 1:]
            zeros += _pair_update(cnt, R, old, others, -1)
            zeros += _pair_update(cnt, R, x, others, 1)
            S[i] = x
            inS.discard(old)
            inS.add(x)
            tabu[old] = it + rng.randint(5, 10)
            if zeros < best_local:
                best_local = zeros
                stall = 0
            else:
                stall += 1
        if zeros == 0:
            yield list(S)
            return


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 2.0)
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Only the diameter-3 regime is searched; Moore-extremal case is optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    hi = d * (d - 1) + 1          # hard bound for diameter-3 difference covers
    best_n, best_e = base_n, base_e
    best_N = base_n // 2          # need N > best_N so 2N > current best order

    while time.monotonic() < deadline:
        top = min(hi, best_N + WINDOW)
        if top <= best_N:
            break
        # Smallest orders first: bank the cheapest improvement, then move on.
        active = []
        for N in range(best_N + 1, top + 1):
            if N < d:
                continue
            for _order, mul, inv in _group_list(N, rng):
                gen = _tabu_search(N, mul, inv, d, rng)
                active.append([N, mul, gen])

        found = None
        while active and found is None and time.monotonic() < deadline:
            for entry in list(active):
                if time.monotonic() >= deadline:
                    break
                N, mul, gen = entry
                try:
                    res = next(gen)
                except StopIteration:
                    active.remove(entry)
                    continue
                if res is None:
                    continue
                n, edges = lib.group_lift(2, [(0, 1, g) for g in res], N, mul)
                active.remove(entry)
                if n > best_n and lib.is_valid(n, edges, d, D):
                    found = (n, edges, N)
                    break

        if found is None:
            break
        best_n, best_e, best_N = found

    if lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    return base_n, base_e
