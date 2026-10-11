"""Diameter-3 bipartite search: parent difference-cover lifts plus new two-orbit voltage lifts.

New idea in this version: a two-orbit lift. Take four base vertices a0, a1 | b0, b1 and
a multiplicity pattern M = [[x, d-x], [d-x, x]] of darts. Each block (i, j) holds m_ij
distinct group elements. Lifting over a group G gives a bipartite graph of order 4|G| with
every degree exactly d. The voltages are annealed directly against lib.bad_pairs(.., 3),
so no algebraic cover condition is needed. The parent's difference-cover search runs in
the same round-robin, and every candidate is checked with lib.is_valid before it is kept.
"""
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


# ------------------------------------------------ groups

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


# ------------------------------------------ parent: difference-cover lifts

def _ratio_table(N, mul, inv):
    """R[x][y] = x * y^{-1}, as a list of lists."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


def _pair_update(cnt, R, e, others, sign):
    """Add (sign=+1) or remove (sign=-1) all ordered pairs involving element e."""
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


def _diff_gen(N, mul, inv, d, rng):
    """Wrap the difference-cover anneal so it yields finished graphs (or None)."""
    for r in _anneal(N, mul, inv, d, rng):
        if r is None:
            yield None
        else:
            yield lib.group_lift(2, [(0, 1, g) for g in r], N, mul)


# ------------------------------------------------ new: two-orbit voltage lifts
#
# Base: A-vertices a0, a1 and B-vertices b0, b1. Block (i, j) carries m_ij distinct
# elements of G, where M = [[x, d-x], [d-x, x]]. Every vertex then has degree d.
# Order 4|G|. Voltages are annealed against the number of pairs at distance > 3.

def _splits(d):
    """Diagonal sizes x for M = [[x, d-x], [d-x, x]]. Only x <= d/2 matters (symmetry)."""
    xs = list(range(d // 2, 0, -1))
    return xs[:2]


def _two_orbit_gen(N, mul, d, x, rng):
    """Generator: anneal the two-orbit lift over group (N, mul). Yields None, then (n, edges)."""
    M = {(0, 0): x, (1, 1): x, (0, 1): d - x, (1, 0): d - x}
    keys = list(M)

    def evaluate(bl):
        darts = [(i, 2 + j, g) for (i, j), gs in bl.items() for g in gs]
        n, edges = lib.group_lift(4, darts, N, mul)
        return lib.bad_pairs(n, edges, 3), n, edges

    while True:
        bl = {k: rng.sample(range(N), M[k]) for k in keys}
        cost, _, _ = evaluate(bl)
        T = 1.0
        for step in range(30000):
            if cost == 0:
                break
            if step % 20 == 0:
                yield None
            k = rng.choice(keys)
            gs = bl[k]
            idx = rng.randrange(len(gs))
            new = rng.randrange(N)
            if new in gs:
                continue
            old = gs[idx]
            gs[idx] = new
            c2, _, _ = evaluate(bl)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                gs[idx] = old
            T = max(0.05, T * 0.9995)
        if cost == 0:
            _, n, edges = evaluate(bl)
            yield (n, edges)
            return


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 2.0)
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Only the diameter-3 regime is searched; the Moore-extremal case is optimal.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    best = (base_n, base_e)
    best_n = base_n
    moore = lib.moore_bound(d, 3)

    # entries: [size upper bound on vertex count, generator yielding None or (n, edges)]
    entries = []

    # New: two-orbit lifts of order 4N, need 4N > best_n and 4N <= Moore bound.
    for N in range(moore // 4, best_n // 4, -1):
        if N < 2:
            continue
        for x in _splits(d):
            for _o, mul, _inv in _group_list(N, rng)[:3]:
                entries.append([4 * N, _two_orbit_gen(N, mul, d, x, rng)])

    # Parent: difference-cover lifts of order 2N, need 2N > best_n.
    hi = d * (d - 1) + 1
    lo = best_n // 2 + 1
    for N in range(hi, lo - 1, -1):
        if N < d:
            continue
        for _o, mul, inv in _group_list(N, rng):
            entries.append([2 * N, _diff_gen(N, mul, inv, d, rng)])

    while entries and time.monotonic() < deadline:
        for entry in list(entries):
            if time.monotonic() >= deadline:
                break
            if entry[0] <= best_n:
                entries.remove(entry)
                continue
            try:
                res = next(entry[1])
            except StopIteration:
                entries.remove(entry)
                continue
            if res is None:
                continue
            entries.remove(entry)
            n, edges = res
            if n > best_n and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_n = n
                entries = [e for e in entries if e[0] > best_n]
                break
        entries = [e for e in entries if e[0] > best_n]

    return best[0], best[1]
