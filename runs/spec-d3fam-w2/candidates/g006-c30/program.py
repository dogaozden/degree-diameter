"""Diameter-3 bipartite construction, with a two-class voltage-lift search added.

Phase 0 keeps the verified baselines: PG(2,q) incidence, the Araujo-Pardo-Lopez
graph, and the trivial fallback.

Phase 1 (new, the bold change) searches a different family: bipartite voltage
lifts of a 4-vertex base graph (A0, A1 | B0, B1) over the cyclic group Z_N. The
base has x darts A0-B0, x darts A1-B1, and d-x darts in each of A0-B1 and A1-B0,
so the lift is d-regular with order 4N. Each dart carries a voltage, and the
voltages within one class pair are distinct so the graph is simple. The lift
is G-invariant, so diameter <= 3 holds iff all four class roots reach every
vertex within 3 steps. Simulated annealing minimizes the number of unreached
(root, vertex) pairs, using bitmask BFS. This family allows order up to about
4 * (d(d-1)+1)/2, which exceeds the single-class Haar bound 2(d(d-1)+1).

Phase 2 keeps the earlier difference-cover Haar search as a secondary option.
Every candidate passes lib.is_valid before it is accepted, so the output is
always a valid graph.
"""
import math
import random
import time

import lib


_KEYS = ((0, 0), (1, 1), (0, 1), (1, 0))  # (A class, B class) of each voltage set


def _fallback(d, D):
    """Verified baseline: K_{d,d} (diameter 2) or trivial graphs for small parameters."""
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    return lib.haar_graph(d, range(d))


def _group_list(N, rng):
    """Cyclic group of order N plus a few semidirect products Z_m x| Z_k of order N."""
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
        for r in rs[:3]:
            try:
                groups.append(lib.semidirect_group(m, k, r))
            except ValueError:
                pass
    return groups


def _ratio_table(N, mul, inv):
    """R[x][y] = x * y^{-1}."""
    iv = [inv(y) for y in range(N)]
    return [[mul(x, iv[y]) for y in range(N)] for x in range(N)]


def _upd(cnt, R, S, skip, v, sign):
    """Add (sign=+1) or remove (sign=-1) ordered differences of v against S[j], j != skip.

    Returns the change in the number of uncovered group elements.
    """
    ch = 0
    Rv = R[v]
    for j, b in enumerate(S):
        if j == skip:
            continue
        for g in (Rv[b], R[b][v]):
            if sign > 0:
                if cnt[g] == 0:
                    ch -= 1
                cnt[g] += 1
            else:
                cnt[g] -= 1
                if cnt[g] == 0:
                    ch += 1
    return ch


def _anneal(N, R, d, rng, steps, e):
    """Find d distinct elements S with S S^{-1} = G by annealing; None if not found."""
    S = rng.sample(range(N), d)
    cnt = [0] * N
    cnt[e] = 1
    for a in S:
        for b in S:
            if a != b:
                cnt[R[a][b]] += 1
    unc = sum(1 for c in cnt if c == 0)
    if unc == 0:
        return S
    for it in range(steps):
        T = 1.0 - 0.95 * it / steps
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        old = S[i]
        delta = _upd(cnt, R, S, i, old, -1) + _upd(cnt, R, S, i, x, +1)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = x
            unc += delta
            if unc == 0:
                return S
        else:
            _upd(cnt, R, S, i, x, -1)
            _upd(cnt, R, S, i, old, +1)
    return None


# ----------------------------------------------------- two-class cyclic lifts

def _rot(x, v, N, full):
    """Rotate the N-bit block x so that bit g moves to bit (g + v) mod N."""
    if v == 0:
        return x
    return ((x << v) | (x >> (N - v))) & full


def _lift_cost(N, darts, full):
    """Number of (root, vertex) pairs at distance > 3, summed over the four class roots.

    Vertex layout: A_i block at offset i*N, B_j block at offset (2+j)*N.
    Dart (i, j, v) joins A_{i,g} to B_{j,g+v}.
    """
    total = 0
    for root in (0, N, 2 * N, 3 * N):
        R = 1 << root
        F = R
        for _ in range(3):
            A = (F & full, (F >> N) & full)
            B = ((F >> (2 * N)) & full, (F >> (3 * N)) & full)
            nb = [0, 0]
            na = [0, 0]
            for i, j, v in darts:
                ai = A[i]
                if ai:
                    nb[j] |= _rot(ai, v, N, full)
                bj = B[j]
                if bj:
                    na[i] |= _rot(bj, (N - v) % N, N, full)
            NF = (na[0] | (na[1] << N) | (nb[0] << (2 * N)) | (nb[1] << (3 * N))) & ~R
            R |= NF
            F = NF
            if not F:
                break
        total += 4 * N - R.bit_count()
    return total


def _darts_of(G):
    out = []
    for (i, j), vals in zip(_KEYS, G):
        for v in vals:
            out.append((i, j, v))
    return out


def _lift_search(N, d, x, rng, steps, deadline):
    """Anneal voltage sets so the 4N-vertex lift has diameter <= 3; return the sets or None."""
    sizes = (x, x, d - x, d - x)
    full = (1 << N) - 1
    G = [rng.sample(range(N), s) for s in sizes]
    cur = _lift_cost(N, _darts_of(G), full)
    for it in range(steps):
        if cur == 0:
            break
        if (it & 63) == 0 and time.monotonic() >= deadline:
            break
        T = max(0.15, 1.2 * (1.0 - it / steps))
        gi = rng.randrange(4)
        if not G[gi]:
            continue
        k = rng.randrange(len(G[gi]))
        y = rng.randrange(N)
        if y in G[gi]:
            continue
        old = G[gi][k]
        G[gi][k] = y
        c = _lift_cost(N, _darts_of(G), full)
        delta = c - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = c
        else:
            G[gi][k] = old
    if cur == 0:
        return G
    return None


def _lift_graph(N, G):
    """Build the 4N-vertex lift from voltage sets G."""
    edges = []
    for (i, j), vals in zip(_KEYS, G):
        for v in vals:
            for g in range(N):
                edges.append((i * N + g, 2 * N + j * N + (g + v) % N))
    return 4 * N, edges


def _lift_driver(d, deadline, rng, get_best, consider):
    """Round-robin annealing over candidate orders 4N > current best, with growing budgets."""
    hi = (d * (d - 1) + 1) // 2  # counting bound: 2N - 1 <= d(d-1)
    cands = [N for N in range(max(2, get_best() // 4 + 1), hi + 1)]
    steps = 3000
    while cands and time.monotonic() < deadline:
        for N in list(cands):
            if time.monotonic() >= deadline:
                return
            if 4 * N <= get_best():
                cands.remove(N)
                continue
            x = rng.randint(max(0, d // 2 - 3), min(d, d // 2 + 3))
            G = _lift_search(N, d, x, rng, steps, deadline)
            if G is not None:
                n, e = _lift_graph(N, G)
                consider(n, e)
                cands = [c for c in cands if 4 * c > get_best()]
        steps *= 2


# ----------------------------------------------------------------- main entry

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 2.0)
    rng = random.Random(seed)

    best = _fallback(d, D)
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Only diameter 3 is searched; other regimes use the baseline.
    if D != 3 or d < 3:
        return best

    # Moore-extremal case: incidence graph of PG(2, d-1).
    if lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best

    # Araujo-Pardo & Lopez record family for d = q + 2.
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Phase 1: two-class cyclic voltage lifts (order 4N), the main new search.
    if d >= 5:
        lift_deadline = start + 0.7 * (deadline - start)
        try:
            _lift_driver(d, lift_deadline, rng, lambda: best_n, consider)
        except Exception:
            pass

    # Phase 2: difference-cover Haar lifts (order 2N), as in the earlier search.
    hi = d * (d - 1) + 1
    lo = best_n // 2 + 1
    for N in range(max(lo, d), hi + 1):
        if time.monotonic() >= deadline:
            break
        groups = _group_list(N, rng)
        tables = [None] * len(groups)
        found = None
        deadline_N = time.monotonic() + 0.5 * max(0.0, deadline - time.monotonic())
        while found is None and time.monotonic() < deadline_N:
            for idx in range(len(groups)):
                if time.monotonic() >= deadline_N:
                    break
                if tables[idx] is None:
                    mul, inv = groups[idx][1], groups[idx][2]
                    tables[idx] = _ratio_table(N, mul, inv)
                R = tables[idx]
                S = _anneal(N, R, d, rng, 6000, R[0][0])
                if S is not None:
                    found = (idx, S)
                    break
        if found is None:
            break
        idx, S = found
        mul = groups[idx][1]
        n, edges = lib.group_lift(2, [(0, 1, g) for g in S], N, mul)
        consider(n, edges)

    return best
