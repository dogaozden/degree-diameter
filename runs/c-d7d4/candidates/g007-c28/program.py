import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction family: bipartite Haar (Cayley-type) graphs over finite groups.
#
# For a group G of order N and a d-subset S of G, the Haar graph H(G, S) has
# vertices a_x and b_y (x, y in G), with a_x ~ b_y iff x^{-1} y is in S.
# Left multiplication is an automorphism that is transitive on each side, so
# the diameter bound D only needs checking from a_e and b_e. That makes each
# evaluation two small BFS runs. Groups are cyclic, direct products, or
# semidirect products Z_m x| Z_k, built with lib.semidirect_group.
# ----------------------------------------------------------------------------

def _groups_of_order(N, rng, max_k=12, samples=3):
    """Return a list of (order, mt, invl) for several groups of order N.

    mt[x][y] is the product x*y and invl[x] the inverse, with identity 0.
    """
    out = []
    for k in range(1, min(max_k, N) + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [1]  # r = 1 gives the direct product Z_m x Z_k (cyclic when k = 1)
        if k > 1:
            cands = [r for r in range(2, m)
                     if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            rng.shuffle(cands)
            rs += cands[:samples]
        for r in rs:
            try:
                order, mul, inv = lib.semidirect_group(m, k, r)
            except ValueError:
                continue
            mt = [[mul(x, y) for y in range(order)] for x in range(order)]
            invl = [inv(x) for x in range(order)]
            out.append((order, mt, invl))
    return out


def _unreached(N, mt, invl, S, D):
    """Number of (source, target) pairs not within distance D, from a_e and b_e.

    Vertices 0..N-1 are the a-side, N..2N-1 the b-side. Zero means valid.
    """
    iS = [invl[s] for s in S]
    total = 0
    for src in (0, N):
        seen = bytearray(2 * N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < N:
                    row = mt[v]
                    for s in S:
                        w = N + row[s]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    row = mt[v - N]
                    for t in iS:
                        w = row[t]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            cnt += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - cnt
    return total


def _climb(N, mt, invl, d, D, rng, iters, deadline):
    """Hill-climb a d-subset S of the group so that H(G, S) has diameter <= D.

    Returns S when the cost reaches zero, otherwise None.
    """
    S = rng.sample(range(N), d)
    c = _unreached(N, mt, invl, S, D)
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        cand = rng.randrange(N)
        if cand in S:
            continue
        old = S[i]
        S[i] = cand
        c2 = _unreached(N, mt, invl, S, D)
        if c2 <= c or rng.random() < 0.03:
            c = c2
        else:
            S[i] = old
    return list(S) if c == 0 else None


def _haar_edges(N, mt, S):
    """Edges of H(G, S): a_x joined to b_{x s} for s in S."""
    return [(x, N + mt[x][s]) for x in range(N) for s in S]


# ----------------------------------------------------------------------------
# Main build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, valid for D >= 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best = {"n": fb_n, "e": list(fb_e)}

    def consider(n, e):
        if n > best["n"] and lib.is_valid(n, e, d, D):
            best["n"] = n
            best["e"] = list(e)

    # Known structured bases for D = 3 (cheap, validated before use).
    if D >= 3:
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                try:
                    consider(*lib.projective_plane_incidence(q))
                except Exception:
                    pass
                break
    if D == 3:
        q = d - 2
        if q >= 3 and lib.is_prime_power(q):
            try:
                consider(*lib.araujo_lopez_graph(q))
            except Exception:
                pass

    # Main stage: Haar graphs over groups, searching just above the current best.
    moore = lib.moore_bound(d, D)
    cache = {}
    window = 3
    while time.monotonic() < deadline:
        lo = best["n"] // 2 + 1
        if 2 * lo > moore:
            break
        N = lo + rng.randrange(window)
        if 2 * N > moore:
            N = lo
        if N < d:
            continue
        if N not in cache:
            cache[N] = _groups_of_order(N, rng)
        groups = cache[N]
        if not groups:
            continue
        order, mt, invl = rng.choice(groups)
        if order < d:
            continue

        S = None
        attempts = 0
        while S is None and attempts < 3 and time.monotonic() < deadline:
            S = _climb(order, mt, invl, d, D, rng, 1500, deadline)
            attempts += 1
        if S is not None:
            consider(2 * order, _haar_edges(order, mt, S))

    n_out, e_out = best["n"], best["e"]
    if not lib.is_valid(n_out, e_out, d, D):
        return lib.haar_graph(d, range(d))
    return n_out, list(e_out)
