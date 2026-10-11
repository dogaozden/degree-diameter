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
# NEW IDEA: multiplier-orbit covers in cyclic groups. For a unit m of Z_N,
# split Z_N \ {0} into orbits of x -> m*x. Build S as a union of whole orbits
# (a set invariant under the multiplier subgroup), pad with a few free elements
# to size d, then repair with a hill climb on the number of uncovered
# differences. Invariance shrinks the search space a lot, so large N that
# plain annealing misses can be reached quickly.


def _orbits(N, m):
    """Orbits of x -> m*x on Z_N \\ {0}, for a unit m."""
    seen = [False] * N
    seen[0] = True
    orbs = []
    for x in range(1, N):
        if seen[x]:
            continue
        orb = []
        y = x
        while not seen[y]:
            seen[y] = True
            orb.append(y)
            y = (y * m) % N
        orbs.append(orb)
    return orbs


def _unit_orbit_sets(N, rng, count):
    """Orbit decompositions for several multipliers of Z_N (always includes -1)."""
    units = [m for m in range(2, N) if math.gcd(m, N) == 1 and m != N - 1]
    rng.shuffle(units)
    chosen = [N - 1] + units[:count]
    return [_orbits(N, m) for m in chosen]


def _uncovered_cyc(S, N):
    """Number of elements of Z_N not expressible as a difference of two elements of S."""
    cov = {(a - b) % N for a in S for b in S}
    return N - len(cov)


def _cyc_trial(N, d, orbs, rng, steps):
    """Try to build a difference cover of Z_N of size d from orbits, then hill-climb."""
    order = list(orbs)
    rng.shuffle(order)
    S = []
    for orb in order:
        if len(S) + len(orb) <= d and rng.random() < 0.85:
            S.extend(orb)
    inS = set(S)
    if 0 not in inS and len(S) < d and rng.random() < 0.5:
        S.append(0)
        inS.add(0)
    while len(S) < d:
        x = rng.randrange(N)
        if x not in inS:
            inS.add(x)
            S.append(x)
    cost = _uncovered_cyc(S, N)
    for _ in range(steps):
        if cost == 0:
            break
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in inS:
            continue
        old = S[i]
        S[i] = x
        c = _uncovered_cyc(S, N)
        if c <= cost:
            inS.discard(old)
            inS.add(x)
            cost = c
        else:
            S[i] = old
    return S if cost == 0 else None


# ------------------------------------------- generic (nonabelian) annealing

def _noncyclic_groups(N, rng):
    """Semidirect products Z_m x| Z_k of order N (k >= 2), a few automorphisms each."""
    groups = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:4]:
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
    """Generator: incremental annealing for d elements S with S S^{-1} = G.

    Yields None periodically and yields the cover S once found.
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

def _search(d, D, rng, deadline, base_n, lo, hi):
    """Round-robin search over groups of order N in [lo, hi], largest N first."""
    best = None
    best_N = lo - 1
    entries = []  # [kind, N, data, mul, gen]
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        _, cmul, _ = lib.cyclic_group(N)
        entries.append(['cyc', N, _unit_orbit_sets(N, rng, 16), cmul, None])
        for _o, mul, inv in _noncyclic_groups(N, rng):
            entries.append(['gen', N, None, mul, _anneal(N, mul, inv, d, rng)])

    while entries and best_N < hi and time.monotonic() < deadline:
        for entry in list(entries):
            if time.monotonic() >= deadline:
                break
            kind, N, data, mul, gen = entry
            if N <= best_N:
                entries.remove(entry)
                continue
            S = None
            if kind == 'cyc':
                for _ in range(4):
                    orbs = data[rng.randrange(len(data))]
                    S = _cyc_trial(N, d, orbs, rng, 60)
                    if S is not None:
                        break
            else:
                try:
                    res = next(gen)
                except StopIteration:
                    entries.remove(entry)
                    continue
                if res is None:
                    continue
                S = res
                entries.remove(entry)
            if S is None:
                continue
            n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
            if n > base_n and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_N = N
                entries = [e for e in entries if e[1] > best_N]
                break
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
        best = _search(d, D, rng, deadline, base_n, lo, hi)
    except Exception:
        best = None

    if best is not None:
        return best
    return base_n, base_e
