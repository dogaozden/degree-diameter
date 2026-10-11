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
        return lib.haar_graph(d, range(d))            # K_{d,d}, diameter 2
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)  # Moore-extremal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            return lib.araujo_lopez_graph(d - 2)      # record construction
        except Exception:
            pass
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------ groups

def _groups(N, rng):
    """Candidate groups of order N: cyclic, plus a few semidirect products Z_m x| Z_k."""
    out = [lib.cyclic_group(N)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(2, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        rng.shuffle(rs)
        for r in rs[:4]:
            try:
                out.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return out


# ------------------------------------------- non-Cayley voltage-lift search
#
# Base graph: k vertices on each side, d-regular bipartite multigraph built as
# the union of d random perfect matchings between the sides, each dart carrying
# a random group voltage. The lift has 2*k*|G| vertices and max degree d.
# Local search moves change one voltage and minimise lib.bad_pairs(.., 3).

def _search(d, k, group, rng, slice_deadline):
    """Anneal voltages until the lift has diameter <= 3. Returns (n, edges) or None."""
    order, mul, _inv = group
    darts = []
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        for i in range(k):
            darts.append([i, k + perm[i], rng.randrange(order)])

    def evaluate():
        n, edges = lib.group_lift(2 * k, [tuple(x) for x in darts], order, mul)
        return n, edges, lib.bad_pairs(n, edges, 3)

    n, edges, cur = evaluate()
    T = 0.9
    step = 0
    while True:
        if cur == 0:
            return n, edges
        step += 1
        if (step & 7) == 0 and time.monotonic() > slice_deadline:
            return None
        idx = rng.randrange(len(darts))
        old = darts[idx][2]
        darts[idx][2] = rng.randrange(order)
        n2, e2, c2 = evaluate()
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur, n, edges = c2, n2, e2
        else:
            darts[idx][2] = old


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.8 * time_limit - 3.0)
    rng = random.Random(seed)

    base_n, base_e = _fallback(d, D)
    if not lib.is_valid(base_n, base_e, d, D):
        return 1, []

    # Only the diameter-3, non-Moore regime is searched.
    if D != 3 or d < 3 or lib.is_prime_power(d - 1):
        return base_n, base_e

    moore = lib.moore_bound(d, 3)
    best_n, best_e = base_n, base_e
    target = best_n + 2
    failures = 0

    while time.monotonic() < deadline:
        if target > moore:
            break
        k = rng.choice([3, 4, 5, 6])
        N = -(-target // (2 * k))          # ceil(target / (2k))
        if N < 2:
            N = 2
        groups = _groups(N, rng)
        group = rng.choice(groups)
        slice_len = 4.0 + 2.0 * min(failures, 5)
        slice_deadline = min(deadline, time.monotonic() + slice_len)

        res = _search(d, k, group, rng, slice_deadline)
        if res is not None:
            n, edges = res
            if n > best_n and lib.is_valid(n, edges, d, D):
                best_n, best_e = n, edges
                target = best_n + 2
                failures = 0
                continue
        failures += 1

    return best_n, best_e
