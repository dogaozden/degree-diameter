import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe fallback and algebraic candidates (diameter 3).
# ----------------------------------------------------------------------------

def _fallback(d):
    """K_{d,d}: diameter 2, always valid for D >= 2."""
    return lib.haar_graph(d, range(d))


def _algebraic(d):
    """Projective-plane incidence and Araujo-Pardo-Lopez graphs, both of diameter 3."""
    out = []
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            out.append(lib.projective_plane_incidence(q))
            break
    for q in range(min(d - 2, 23), 2, -1):
        if lib.is_prime_power(q):
            try:
                out.append(lib.araujo_lopez_graph(q))
            except ValueError:
                pass
            break
    return out


# ----------------------------------------------------------------------------
# New family: degree-preserving edge-switch search on bipartite d-regular graphs.
#
# Instead of voltage lifts over groups, we start from a random Haar graph on
# M + M vertices (d distinct cyclic shifts), then repeatedly apply 2-switches
# (i1,j1),(i2,j2) -> (i1,j2),(i2,j1). Switches preserve regularity and
# bipartiteness, and leave the group structure entirely. A switch is kept if
# the number of pairs at distance > D does not grow (with a small annealing
# allowance). M is grown while a zero-defect graph is found in time.
# ----------------------------------------------------------------------------

def _bad_pairs_sets(M, L, R, D):
    """Unordered pairs at distance > D. Left i = vertex i, right j = vertex M+j."""
    V = 2 * M
    adj = [[M + j for j in L[i]] for i in range(M)] + [list(R[j]) for j in range(M)]
    reach = [1 << v for v in range(V)]
    for _ in range(D):
        new = []
        for v in range(V):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        reach = new
    return sum(V - r.bit_count() for r in reach) // 2


def _apply(E, L, R, e1, e2):
    """2-switch on edges e1 and e2. Applying it twice restores the original state."""
    i1, j1 = E[e1]
    i2, j2 = E[e2]
    L[i1].discard(j1)
    R[j1].discard(i1)
    L[i2].discard(j2)
    R[j2].discard(i2)
    L[i1].add(j2)
    R[j2].add(i1)
    L[i2].add(j1)
    R[j1].add(i2)
    E[e1] = [i1, j2]
    E[e2] = [i2, j1]


def _search(d, D, M, rng, deadline):
    """Try to find a d-regular bipartite graph on M + M vertices with diameter <= D."""
    shifts = rng.sample(range(M), d)
    E = [[i, (i + s) % M] for i in range(M) for s in shifts]
    L = [set() for _ in range(M)]
    R = [set() for _ in range(M)]
    for i, j in E:
        L[i].add(j)
        R[j].add(i)
    cur = _bad_pairs_sets(M, L, R, D)
    T = 1.0
    n_e = len(E)
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        e1 = rng.randrange(n_e)
        e2 = rng.randrange(n_e)
        i1, j1 = E[e1]
        i2, j2 = E[e2]
        if i1 == i2 or j1 == j2 or j2 in L[i1] or j1 in L[i2]:
            continue
        _apply(E, L, R, e1, e2)
        new = _bad_pairs_sets(M, L, R, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            _apply(E, L, R, e1, e2)
        T = max(0.1, T * 0.9995)
    return [(i, M + j) for i, j in E]


def _grow(d, D, rng, deadline):
    """Increase M while the switch search succeeds; return (M, edges) or None."""
    best_M, best_E = None, None
    step = max(1, d // 4)
    M = d
    limit = lib.moore_bound(d, D) // 2
    while time.monotonic() < deadline and M <= limit:
        now = time.monotonic()
        remaining = deadline - now
        sub = now + max(0.3 * remaining, min(remaining, 1.0))
        E = _search(d, D, M, rng, min(sub, deadline))
        if E is not None:
            best_M, best_E = M, E
            M = best_M + step
        else:
            step = max(1, step // 2)
            base = best_M if best_M is not None else d
            M = base + step
    if best_M is None:
        return None
    return best_M, best_E


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = _fallback(d)
    try:
        if D >= 3:
            for n, e in _algebraic(d):
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)

        deadline = start + 0.6 * time_limit
        rng = random.Random(seed * 1000003 + d * 97 + D)
        res = _grow(d, D, rng, deadline)
        if res is not None:
            M, E = res
            n = 2 * M
            if n > best[0] and lib.is_valid(n, E, d, D):
                best = (n, E)
    except Exception:
        pass
    return best
