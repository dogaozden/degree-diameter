import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction: Z_m-style voltage lifts over a small bipartite base multigraph.
#
# Base: a A-vertices and a B-vertices, d darts from each A-vertex (d permutations
# pi_k from A to B). Each dart (u, pi_k(u), g) carries a group element g from a
# finite group G of order N. The lift has 2*a*N vertices (u, x), and (u, x) is
# joined to (v, x*g). Left multiplication by h is an automorphism of the lift,
# so the diameter is at most D exactly when every base vertex's fibre is reached
# within D steps from the identity representative (u, e). Each candidate is
# therefore checked with 2a BFS runs. Voltages are found by hill climbing on the
# number of unreached (representative, vertex) pairs.
# ----------------------------------------------------------------------------

N_CAP = 300  # caps the group order, so the multiplication table stays small


def _group(N, rng):
    """Return (order, mul, inv) for a group of order N: a random semidirect product, or cyclic."""
    options = [k for k in range(2, N + 1) if N % k == 0 and N // k >= 2]
    if options and rng.random() < 0.7:
        rng.shuffle(options)
        for k in options:
            m = N // k
            rs = [r for r in range(1, m)
                  if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            if rs:
                return lib.semidirect_group(m, k, rng.choice(rs))
    return lib.cyclic_group(N)


def _tables(N, mul, inv):
    mt = [[mul(x, y) for y in range(N)] for x in range(N)]
    iv = [inv(x) for x in range(N)]
    return mt, iv


def _search(a, d, D, N, rng, deadline):
    """Hill-climb voltages for a d-regular lift of order 2*a*N with diameter <= D.

    Returns (mul, darts) on success, or None.
    """
    order, mul, inv = _group(N, rng)
    mt, iv = _tables(N, mul, inv)
    n = 2 * a * N
    perms = [list(range(a))]
    for _ in range(d - 1):
        p = list(range(a))
        rng.shuffle(p)
        perms.append(p)
    volt = [[rng.randrange(N) for _ in range(a)] for _ in range(d)]

    def cost(volt):
        adjA = [[] for _ in range(a)]
        adjB = [[] for _ in range(a)]
        for k in range(d):
            p = perms[k]
            vk = volt[k]
            for u in range(a):
                g = vk[u]
                v = p[u]
                adjA[u].append((a + v, g))
                adjB[v].append((u, iv[g]))
        total = 0
        for src_base in range(2 * a):
            seen = bytearray(n)
            s = src_base * N
            seen[s] = 1
            frontier = [s]
            c = 1
            for _ in range(D):
                nxt = []
                for vtx in frontier:
                    b, x = divmod(vtx, N)
                    row = mt[x]
                    if b < a:
                        for wb, g in adjA[b]:
                            w = wb * N + row[g]
                            if not seen[w]:
                                seen[w] = 1
                                nxt.append(w)
                    else:
                        for ub, gi in adjB[b - a]:
                            w = ub * N + row[gi]
                            if not seen[w]:
                                seen[w] = 1
                                nxt.append(w)
                if not nxt:
                    break
                c += len(nxt)
                frontier = nxt
            total += n - c
        return total

    cur = cost(volt)
    it = 0
    while cur > 0:
        if (it & 31) == 0 and time.monotonic() > deadline:
            return None
        it += 1
        k = rng.randrange(d)
        u = rng.randrange(a)
        old = volt[k][u]
        volt[k][u] = rng.randrange(N)
        new = cost(volt)
        if new <= cur or rng.random() < 0.01:
            cur = new
        else:
            volt[k][u] = old
    darts = [(u, a + perms[k][u], volt[k][u]) for k in range(d) for u in range(a)]
    return mul, darts


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(time_limit * 0.85, time_limit - 5.0))
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is bipartite with degree d.
    best = lib.haar_graph(d, range(d))
    moore = lib._moore_bound(d, D)

    # Projective plane incidence graph meets the Moore bound when D = 3 and d-1 is a prime power.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if best[0] >= moore:
        return best

    # Lift search: grow the target order, keeping each success verified.
    a_choices = [2, 3, 4, 5]
    step = 4
    while time.monotonic() < deadline:
        a = rng.choice(a_choices)
        if 2 * a > moore:
            a = 1
        max_N = min(N_CAP, moore // (2 * a))
        if max_N < 1:
            break
        base_N = best[0] // (2 * a) + 1
        N = min(max_N, base_N + rng.randrange(step + 1))
        if N < 1:
            N = 1
        remaining = deadline - time.monotonic()
        att_deadline = time.monotonic() + max(1.0, min(4.0, remaining / 5.0))
        att_deadline = min(att_deadline, deadline)
        res = _search(a, d, D, N, rng, att_deadline)
        if res is not None:
            mul, darts = res
            n2, e2 = lib.group_lift(2 * a, darts, N, mul)
            if n2 > best[0] and lib.is_valid(n2, e2, d, D):
                best = (n2, e2)
            step = min(step * 2, 64)
        else:
            step = max(1, step // 2)

    return best
