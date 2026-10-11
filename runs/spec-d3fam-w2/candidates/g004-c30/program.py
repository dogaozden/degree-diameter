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
# S S^{-1} = G. So the task is a "difference cover" of size d in a group G.

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


def _cayley_search(d, D, base_n, rng, deadline):
    """Round-robin difference-cover annealing over many groups. Returns (n, edges) or None."""
    lo = base_n // 2 + 1
    hi = d * (d - 1) + 1
    if lo > hi:
        return None
    active = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _order, mul, inv in _group_list(N, rng):
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
            if n > base_n and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_N = N
                active = [e for e in active if e[0] > best_N]
                break
        active = [e for e in active if e[0] > best_N]
    return best


# ------------------------------------------- NEW: k-by-k voltage lifts (k = 3, 4)
#
# Base multigraph: k vertices A_0..A_{k-1} and k vertices B_0..B_{k-1}, with
# every vertex of base degree d (A-side darts listed as i repeated d times, the
# B-side endpoints a random permutation of the same multiset). Each dart carries
# a voltage in a group G of order N. The lift has 2kN vertices and max degree d
# by construction, is bipartite, and has diameter <= 3 iff the bad-pair count
# is zero. Voltages are annealed directly against the bad-pair count, which
# lets the base structure (k > 2) trade off against the group order.

def _score(n, edges, D):
    """Number of unordered vertex pairs at distance more than D."""
    adj = [[] for _ in range(n)]
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt.append(r)
        reach = nxt
    return sum(n - r.bit_count() for r in reach) // 2


def _sa_lift(k, N, mul, d, D, rng, stop):
    """Anneal voltages of a random k-by-k base lift over a group of order N.

    Returns (n, edges) with zero bad pairs, or None if the time limit hits first.
    """
    nd = k * d
    base_a = [i for i in range(k) for _ in range(d)]

    def fresh_B():
        b = base_a[:]
        rng.shuffle(b)
        return b

    dB = fresh_B()
    volt = [rng.randrange(N) for _ in range(nd)]

    def lift():
        darts = [(base_a[t], k + dB[t], volt[t]) for t in range(nd)]
        return lib.group_lift(2 * k, darts, N, mul)

    n, e = lift()
    cost = _score(n, e, D)
    T = 1.0
    stall = 0
    while cost > 0:
        if time.monotonic() >= stop:
            return None
        if stall > 1500:
            # Restart from a fresh base structure and fresh voltages.
            dB = fresh_B()
            volt = [rng.randrange(N) for _ in range(nd)]
            n, e = lift()
            cost = _score(n, e, D)
            stall = 0
            T = 1.0
            continue
        i = rng.randrange(nd)
        old = volt[i]
        volt[i] = rng.randrange(N)
        n, e = lift()
        new = _score(n, e, D)
        if new <= cost or rng.random() < math.exp(-(new - cost) / T):
            stall = 0 if new < cost else stall + 1
            cost = new
        else:
            volt[i] = old
            stall += 1
        T = max(0.05, T * 0.998)
    n, e = lift()
    return n, e


def _lift_search(d, D, cur_n, rng, deadline):
    """Try to beat cur_n with k x k voltage lifts. Returns (n, edges) or None."""
    best = None
    for k in (3, 4):
        while time.monotonic() < deadline:
            N = cur_n // (2 * k) + 1
            if N < 2 or 2 * k * N > lib.moore_bound(d, D):
                break
            found = None
            for _order, mul, _inv in _group_list(N, rng)[:3]:
                now = time.monotonic()
                if now >= deadline:
                    break
                stop = min(deadline, now + 8.0)
                res = _sa_lift(k, N, mul, d, D, rng, stop)
                if res is not None and res[0] > cur_n and lib.is_valid(res[0], res[1], d, D):
                    found = res
                    break
            if found is None:
                break
            best = found
            cur_n = found[0]
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.85 * time_limit - 2.0)
    deadline = start + total
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Only the diameter-3 regime is searched; Moore-extremal case is optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    best_n, best_e = base_n, base_e

    # Phase 1: Cayley difference-cover search (keeps the parent's strong results).
    try:
        res = _cayley_search(d, D, best_n, rng, start + 0.6 * total)
        if res is not None and res[0] > best_n and lib.is_valid(res[0], res[1], d, D):
            best_n, best_e = res
    except Exception:
        pass

    # Phase 2: k x k voltage lifts with annealed voltages.
    try:
        res = _lift_search(d, D, best_n, rng, deadline)
        if res is not None and res[0] > best_n and lib.is_valid(res[0], res[1], d, D):
            best_n, best_e = res
    except Exception:
        pass

    if lib.is_valid(best_n, best_e, d, D):
        return best_n, best_e
    return base_n, base_e
