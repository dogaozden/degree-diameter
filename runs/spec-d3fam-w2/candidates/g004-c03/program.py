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
# giving order 2|G| with |G| <= d(d-1)+1.
#
# New in this version: a tabu search over difference covers. Each move swaps
# one element of S for a candidate x; the change in the number of uncovered
# group elements is computed exactly from the coverage counts (apply, read the
# delta, undo). Recently removed elements are tabu for a short tenure, with an
# aspiration rule. Tabu and annealing searches alternate across groups.

def _group_list(N, rng):
    """Candidate groups of order N: cyclic, plus semidirect Z_m x| Z_k."""
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
        for r in rs[:6]:
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
    """Add (sign=+1) or remove (sign=-1) all ordered pairs involving element e.

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


def _tabu(N, mul, inv, d, rng):
    """Generator: tabu search for d elements S with S S^{-1} = G.

    Yields None often (so the driver can round-robin) and yields the cover
    once found. Restarts from a fresh random state when a run stalls.
    """
    R = _ratio_table(N, mul, inv)
    while True:
        S = rng.sample(range(N), d)
        inS = set(S)
        cnt = [0] * N
        for a in S:
            for b in S:
                cnt[R[a][b]] += 1
        zeros = cnt.count(0)
        tabu_until = [0] * N
        it = 0
        stall = 0
        best_zeros = zeros
        while zeros > 0 and stall < 2000:
            it += 1
            stall += 1
            yield None
            best_move = None
            best_val = None
            for _ in range(48):
                i = rng.randrange(d)
                x = rng.randrange(N)
                if x in inS:
                    continue
                old = S[i]
                others = S[:i] + S[i + 1:]
                c1 = _pair_update(cnt, R, old, others, -1)
                c2 = _pair_update(cnt, R, x, others, 1)
                val = c1 + c2
                _pair_update(cnt, R, x, others, -1)   # undo addition
                _pair_update(cnt, R, old, others, 1)  # undo removal
                # Tabu unless the move beats the best seen in this run.
                if tabu_until[x] > it and zeros + val >= best_zeros:
                    continue
                if (best_val is None or val < best_val
                        or (val == best_val and rng.random() < 0.5)):
                    best_val = val
                    best_move = (i, x, old, others)
            if best_move is None:
                continue
            i, x, old, others = best_move
            zeros += _pair_update(cnt, R, old, others, -1)
            zeros += _pair_update(cnt, R, x, others, 1)
            S[i] = x
            inS.discard(old)
            inS.add(x)
            tabu_until[old] = it + 7 + rng.randrange(5)
            if zeros < best_zeros:
                best_zeros = zeros
                stall = 0
        if zeros == 0:
            yield list(S)
            return


def _anneal(N, mul, inv, d, rng):
    """Generator: incremental annealing for d elements S with S S^{-1} = G."""
    R = _ratio_table(N, mul, inv)
    while True:
        S = rng.sample(range(N), d)
        inS = set(S)
        cnt = [0] * N
        for a in S:
            for b in S:
                cnt[R[a][b]] += 1
        zeros = cnt.count(0)
        cost = zeros
        T = 0.5
        for step in range(200000):
            if cost == 0:
                break
            if step % 2000 == 0:
                yield None
            i = rng.randrange(d)
            x = rng.randrange(N)
            if x in inS:
                continue
            old = S[i]
            others = S[:i] + S[i + 1:]
            zeros += _pair_update(cnt, R, old, others, -1)
            zeros += _pair_update(cnt, R, x, others, 1)
            if zeros <= cost or rng.random() < math.exp(-(zeros - cost) / T):
                S[i] = x
                inS.discard(old)
                inS.add(x)
                cost = zeros
            else:
                zeros += _pair_update(cnt, R, x, others, -1)
                zeros += _pair_update(cnt, R, old, others, 1)
        if cost == 0:
            yield list(S)
            return


# ---------------------------------------------------------------- driver

def _search(base_n, d, lo, hi, deadline, rng):
    """Round-robin search over groups of order lo..hi; returns (n, edges) or None."""
    cands = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        groups = _group_list(N, rng)[:3]
        for _order, mul, inv in groups:
            cands.append((N, mul, inv))

    active = []
    for idx, (N, mul, inv) in enumerate(cands):
        if idx % 2 == 0:
            gen = _tabu(N, mul, inv, d, rng)
        else:
            gen = _anneal(N, mul, inv, d, rng)
        active.append([N, mul, gen])

    best = None
    best_N = lo - 1
    while active and time.monotonic() < deadline:
        for entry in list(active):
            if time.monotonic() >= deadline:
                break
            N, mul, gen = entry
            if N <= best_N:
                active.remove(entry)
                continue
            try:
                res = next(gen)
            except StopIteration:
                active.remove(entry)
                continue
            if res is None:
                continue
            n, edges = lib.group_lift(2, [(0, 1, g) for g in res], N, mul)
            active.remove(entry)
            if n > base_n and lib.is_valid(n, edges, d, 3):
                best = (n, edges)
                best_N = N
                active = [e for e in active if e[0] > best_N]
                break
        active = [e for e in active if e[0] > best_N]
    return best


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

    lo = base_n // 2 + 1          # need 2|G| > current best order
    hi = d * (d - 1) + 1          # hard bound for diameter-3 difference covers
    if lo > hi:
        return base_n, base_e

    try:
        best = _search(base_n, d, lo, hi, deadline, rng)
    except Exception:
        best = None
    if best is not None:
        return best
    return base_n, base_e
