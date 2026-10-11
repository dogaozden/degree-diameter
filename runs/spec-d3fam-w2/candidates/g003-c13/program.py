import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baselines: record Araujo-Pardo/Lopez graph, projective-plane incidence, K_{d,d}.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over ABELIAN groups with a tabu difference-cover search.
#
# Let G be a group of order N and S a d-subset of G with 0 in S. Put a_x ~ b_{x+s}
# for s in S (x in G). Every vertex has degree d and the graph is bipartite.
# If S - S = G, then diameter <= 3:
#   same side: a_x - b_{x+s} - a_{x+s-t} reaches a_{x+g} for any g = s - t;
#   cross:     b_y is at distance <= 3 from a_x since y - x = s - t for some s, t
#              in S, and a_x - b_{x+s} - a_{x+s-t} - b_{x+s-t+0} = b_y.
#
# New in this version: the parent used simulated annealing over cyclic and
# non-abelian semidirect groups. Here we use a TABU search with full best-move
# neighbourhood evaluation (every (position, candidate) swap is scored exactly
# via incremental difference counts), over ALL abelian groups Z_a x Z_b of order
# N, including the non-cyclic ones (for example Z_2 x Z_k), with restarts that
# cycle through the groups.
# ----------------------------------------------------------------------------

def _abelian_tables(a, b):
    """Addition and negation tables for Z_a x Z_b; element (i, j) is coded as i*b + j."""
    N = a * b
    ADD = [[((x // b + y // b) % a) * b + (x % b + y % b) % b for y in range(N)]
           for x in range(N)]
    NEG = [((-(x // b)) % a) * b + (-(x % b)) % b for x in range(N)]
    return N, ADD, NEG


def _group_tables(N, rng):
    """Tables for every abelian group of order N: the cyclic one plus each non-cyclic Z_a x Z_b."""
    shapes = [(1, N)]
    for a in range(2, N):
        if N % a == 0:
            b = N // a
            if a <= b and math.gcd(a, b) > 1:
                shapes.append((a, b))
    rng.shuffle(shapes)
    return [_abelian_tables(a, b) for a, b in shapes]


def _touch(cnt, others, x, ADD, NEG, sign):
    """Add (sign=+1) or remove (sign=-1) the ordered differences between x and each y in others.

    Returns the number of difference values that became covered (+1) or uncovered (-1).
    """
    flips = 0
    for y in others:
        for g in (ADD[x][NEG[y]], ADD[y][NEG[x]]):
            if sign > 0:
                if cnt[g] == 0:
                    flips += 1
                cnt[g] += 1
            else:
                cnt[g] -= 1
                if cnt[g] == 0:
                    flips += 1
    return flips


def _tabu(tables, d, rng, deadline, stall_limit=3000):
    """Find S of size d with 0 in S and S - S = G, cycling over the given group tables.

    Returns (S, (N, ADD, NEG)) on success, or None on timeout.
    """
    r = 0
    while time.monotonic() < deadline:
        table = tables[r % len(tables)]
        r += 1
        N, ADD, NEG = table
        S = [0] + rng.sample(range(1, N), d - 1)
        inS = set(S)
        cnt = [0] * N
        for i in range(d):
            for j in range(d):
                if i != j:
                    cnt[ADD[S[i]][NEG[S[j]]]] += 1
        unc = sum(1 for g in range(1, N) if cnt[g] == 0)
        if unc == 0:
            return S, table
        tabu = [0] * N
        best = unc
        stall = 0
        it = 0
        while stall < stall_limit:
            it += 1
            if (it & 15) == 0 and time.monotonic() >= deadline:
                return None
            pick = None
            pick_val = None
            ties = 0
            for i in range(1, d):
                out = S[i]
                others = [S[j] for j in range(d) if j != i]
                lost = _touch(cnt, others, out, ADD, NEG, -1)
                for x in range(1, N):
                    if x in inS:
                        continue
                    gained = _touch(cnt, others, x, ADD, NEG, 1)
                    _touch(cnt, others, x, ADD, NEG, -1)
                    val = unc + lost - gained
                    if tabu[x] > it and val >= best:
                        continue
                    if pick_val is None or val < pick_val:
                        pick_val = val
                        pick = (i, x)
                        ties = 1
                    elif val == pick_val:
                        ties += 1
                        if rng.randrange(ties) == 0:
                            pick = (i, x)
                _touch(cnt, others, out, ADD, NEG, 1)
            if pick is None:
                break
            i, x = pick
            out = S[i]
            others = [S[j] for j in range(d) if j != i]
            _touch(cnt, others, out, ADD, NEG, -1)
            _touch(cnt, others, x, ADD, NEG, 1)
            inS.discard(out)
            inS.add(x)
            S[i] = x
            unc = pick_val
            tabu[out] = it + rng.randint(3, 3 + d)
            if unc < best:
                best = unc
                stall = 0
            else:
                stall += 1
            if unc == 0:
                return S, table
    return None


def _bicayley_edges(N, ADD, S):
    """Edges a_x = x -- b_{x+s} = N + (x + s) for s in S."""
    return [(x, N + ADD[x][s]) for x in range(N) for s in S]


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit - 0.5
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    if D < 3 or d < 2:
        return best

    try:
        # Known record family for d = q + 2, q a prime power.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                n_a, e_a = lib.araujo_lopez_graph(d - 2)
                if n_a > best[0] and lib.is_valid(n_a, e_a, d, D):
                    best = (n_a, e_a)
            except Exception:
                pass
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg

        # Bi-Cayley search over abelian groups; order 2N, need N <= d(d-1)+1.
        max_N = d * (d - 1) + 1
        N = best[0] // 2 + 1
        while N <= max_N and N >= d and time.monotonic() < deadline:
            remaining = deadline - time.monotonic()
            tables = _group_tables(N, rng)
            res = _tabu(tables, d, rng, time.monotonic() + 0.6 * remaining)
            if res is None:
                break
            S, (NN, ADD, _NEG) = res
            n = 2 * NN
            e = _bicayley_edges(NN, ADD, S)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
            N += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
