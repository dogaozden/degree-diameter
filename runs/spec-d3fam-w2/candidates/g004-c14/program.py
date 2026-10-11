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
# NEW IDEA: automorphism-orbit-constrained covers. For a cyclic group Z_N and a
# unit u, the map x -> u*x is an automorphism, and cover(uS) = u*cover(S). We
# restrict S to be a union of orbits of x -> u*x. This shrinks the search space
# to a few dozen blocks, so annealing reaches large N that plain annealing
# stalls on. Orbit-constrained S may be a union of several orbits of mixed
# sizes; a move swaps one block for another block of the same size, which keeps
# |S| = d exactly. The cover condition is still checked directly, so every
# output is verified.

def _group_list(N, rng):
    """Candidate groups of order N: cyclic first, then semidirect Z_m x| Z_k."""
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


def _orbit_blocks(N, u):
    """Partition Z_N into orbits of x -> u*x (gcd(u, N) = 1)."""
    seen = [False] * N
    blocks = []
    for x in range(N):
        if seen[x]:
            continue
        orb = []
        y = x
        while True:
            orb.append(y)
            seen[y] = True
            y = (y * u) % N
            if y == x:
                break
        blocks.append(tuple(orb))
    return blocks


def _singleton_blocks(N):
    return [(x,) for x in range(N)]


def _pick_units(N, rng, k):
    """Up to k random units of Z_N other than 1; always includes -1 when present."""
    units = [u for u in range(2, N) if math.gcd(u, N) == 1]
    if not units:
        return []
    picks = [N - 1] if (N - 1) in units else []
    rest = [u for u in units if u not in picks]
    rng.shuffle(rest)
    return (picks + rest)[:k]


def _initial_choice(blocks, d, rng):
    """Random set of block indices whose sizes sum to exactly d, or None."""
    idx = list(range(len(blocks)))
    for _ in range(300):
        rng.shuffle(idx)
        pick = []
        tot = 0
        for i in idx:
            s = len(blocks[i])
            if tot + s <= d:
                pick.append(i)
                tot += s
                if tot == d:
                    return pick
    return None


def _elements(blocks, chosen):
    return [x for i in chosen for x in blocks[i]]


def _covered(S, R):
    """Number of distinct elements of the form a * b^{-1}, a, b in S."""
    cov = set()
    for a in S:
        ra = R[a]
        for b in S:
            cov.add(ra[b])
    return len(cov)


def _block_gen(N, mul, inv, d, rng, blocks):
    """Generator: annealing over unions of blocks with total size d.

    Yields None periodically (so the driver can round-robin many searches), and
    yields the element list S once S S^{-1} = G. Restarts from a fresh random
    state when a run stalls.
    """
    R = _ratio_table(N, mul, inv)
    by_size = {}
    for i, b in enumerate(blocks):
        by_size.setdefault(len(b), []).append(i)
    while True:
        chosen = _initial_choice(blocks, d, rng)
        if chosen is None:
            return
        inset = set(chosen)
        cost = N - _covered(_elements(blocks, chosen), R)
        T = 0.6
        for step in range(60000):
            if cost == 0:
                break
            if step % 1000 == 0:
                yield None
            i = rng.randrange(len(chosen))
            c = rng.choice(by_size[len(blocks[chosen[i]])])
            if c in inset:
                continue
            trial = chosen[:]
            trial[i] = c
            ncost = N - _covered(_elements(blocks, trial), R)
            if ncost <= cost or rng.random() < math.exp(-(ncost - cost) / T):
                inset.discard(chosen[i])
                inset.add(c)
                chosen = trial
                cost = ncost
        if cost == 0:
            yield _elements(blocks, chosen)
            return


# ---------------------------------------------------------------- driver

def _search(d, lo, hi, base_n, deadline, rng):
    """Round-robin search over groups and orbit-constrained covers; returns (n, edges) or None."""
    active = []
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        groups = _group_list(N, rng)
        for gi, (_order, mul, inv) in enumerate(groups):
            active.append([N, mul, _block_gen(N, mul, inv, d, rng, _singleton_blocks(N))])
            if gi == 0:  # cyclic group: add multiplier-orbit searches
                for u in _pick_units(N, rng, 3):
                    blocks = _orbit_blocks(N, u)
                    active.append([N, mul, _block_gen(N, mul, inv, d, rng, blocks)])

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
        best = _search(d, lo, hi, base_n, deadline, rng)
    except Exception:
        best = None
    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return base_n, base_e
