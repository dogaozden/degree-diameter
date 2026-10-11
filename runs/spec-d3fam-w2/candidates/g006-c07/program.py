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
        return lib.haar_graph(d, range(d))              # K_{d,d}, diameter 2
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)    # Moore-extremal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)        # record construction
        except Exception:
            pass
    return lib.haar_graph(d, range(d))


# ------------------------------------------------ bi-Cayley lifts over groups
#
# Base vertices a, b with darts (a, b, s) for s in S give the bipartite graph
# on G x {0,1} with a_x ~ b_{x s}. Its diameter is at most 3 whenever
# S S^{-1} = G, so the task is a difference cover of size d in a group G of
# order N, giving order 2N with N <= d(d-1)+1.

def _specs(N, rng, cap=8):
    """Group specs of order N: the cyclic group plus a sample of semidirect Z_m x| Z_k."""
    cands = []
    for k in range(2, N):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:3]:
            cands.append(("sd", m, k, r))
    rng.shuffle(cands)
    return [("cyc",)] + cands[:cap - 1]


def _group(spec, N):
    """Return (mul, inv) for the group named by spec, of order N."""
    if spec[0] == "cyc":
        _, mul, inv = lib.cyclic_group(N)
    else:
        _, m, k, r = spec
        _, mul, inv = lib.semidirect_group(m, k, r)
    return mul, inv


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


def _anneal(N, mul, inv, d, rng):
    """Generator: annealing for d elements S with S S^{-1} = G.

    Yields None periodically so a driver can round-robin many groups, and
    yields the cover S when found. Restarts from a fresh random state on stall.
    """
    iv = [inv(y) for y in range(N)]
    R = [[mul(x, iv[y]) for y in range(N)] for x in range(N)]
    steps = 40000
    while True:
        S = rng.sample(range(N), d)
        inS = set(S)
        cnt = [0] * N
        for a in S:
            for b in S:
                cnt[R[a][b]] += 1
        cost = cnt.count(0)
        for step in range(steps):
            if cost == 0:
                break
            if step % 1000 == 0:
                yield None
            T = 0.6 * (0.02 ** (step / steps))
            i = rng.randrange(d)
            x = rng.randrange(N)
            if x in inS:
                continue
            old = S[i]
            others = S[:i] + S[i + 1:]
            delta = _pair_update(cnt, R, old, others, -1)
            delta += _pair_update(cnt, R, x, others, 1)
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                S[i] = x
                inS.discard(old)
                inS.add(x)
                cost += delta
            else:
                _pair_update(cnt, R, x, others, -1)
                _pair_update(cnt, R, old, others, 1)
        if cost == 0:
            yield list(S)
            return


def _entries(N, d, rng):
    """Active search entries [spec, mul, generator] for all sampled groups of order N."""
    out = []
    for spec in _specs(N, rng):
        try:
            mul, inv = _group(spec, N)
        except ValueError:
            continue
        out.append([spec, mul, _anneal(N, mul, inv, d, rng)])
    return out


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 2.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        base_n, base_e = lib.haar_graph(d, range(d))
        if not lib.is_valid(base_n, base_e, d, D):
            return 1, []

    # Only the diameter-3 regime is searched; skip when already Moore-extremal.
    if D != 3 or d < 3 or base_n >= lib.moore_bound(d, D):
        return base_n, base_e

    best = (base_n, base_e)
    lo = base_n // 2 + 1          # need 2N > current best order
    hi = d * (d - 1) + 1          # bound for diameter-3 difference covers
    if lo > hi:
        return best

    try:
        N = lo
        fails = 0
        while N <= hi and fails < 2 and time.monotonic() < deadline:
            now = time.monotonic()
            budget_end = now + 0.4 * (deadline - now)
            gens = _entries(N, d, rng)
            found = None
            while found is None and gens and time.monotonic() < budget_end:
                for ent in list(gens):
                    if time.monotonic() >= budget_end:
                        break
                    try:
                        res = next(ent[2])
                    except StopIteration:
                        gens.remove(ent)
                        continue
                    if res is None:
                        continue
                    n, e = lib.group_lift(2, [(0, 1, g) for g in res], N, ent[1])
                    if n > best[0] and lib.is_valid(n, e, d, D):
                        found = (n, e)
                        break
                    gens.remove(ent)
            if found is not None:
                best = found
                fails = 0
            else:
                fails += 1
            N += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return base_n, base_e
    return best
