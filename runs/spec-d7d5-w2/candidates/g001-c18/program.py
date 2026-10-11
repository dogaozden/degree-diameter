import math
import random
import time

import lib


# Construction: random d-regular bipartite base multigraph on t+t vertices, lifted over a
# small non-abelian group Z_m x|_r Z_k (order N). Voltages are tuned by local search that
# minimises the number of vertex pairs at distance > D. Left multiplication by the group is
# an automorphism of the lift, so BFS from one representative per base vertex checks all pairs.

def _complete(d):
    """K_{d,d}: valid for every D >= 2, optimal for D = 2."""
    return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]


def _make_group(m, k, r):
    """Multiplication and inversion for Z_m x|_r Z_k, element (a, b) coded as a*k + b."""
    pw = [pow(r, b, m) for b in range(k)]

    def mul(x, g):
        a, b = divmod(x, k)
        c, e = divmod(g, k)
        return ((a + pw[b] * c) % m) * k + (b + e) % k

    def inv(g):
        a, b = divmod(g, k)
        nb = (-b) % k
        return ((-pow(r, nb, m) * a) % m) * k + nb

    return mul, inv


def _pick_group(N, rng):
    """Random semidirect product Z_m x|_r Z_k of order N with small k (k = 1 gives cyclic)."""
    ks = [k for k in range(1, 13) if N % k == 0 and N // k >= 2]
    if not ks:
        return None
    k = rng.choice(ks)
    m = N // k
    rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
    if not rs:
        return None
    return m, k, rng.choice(rs)


def _regular_base(t, d, rng):
    """Random d-regular bipartite multigraph on t + t base vertices, as darts (a, b)."""
    A = [a for a in range(t) for _ in range(d)]
    B = [b for b in range(t) for _ in range(d)]
    rng.shuffle(B)
    return list(zip(A, B))


def _perms(g, N, mul, inv):
    """Forward map x -> x*g and backward map y -> y*g^{-1} over the whole group."""
    gi = inv(g)
    return [mul(x, g) for x in range(N)], [mul(y, gi) for y in range(N)]


def _unreached(t, N, D, darts_a, darts_b, out_of, into, fwd, bwd):
    """Total number of (representative, vertex) pairs at distance > D (0 means valid)."""
    off = t * N
    n = 2 * off
    total = 0
    sources = [a * N for a in range(t)] + [off + b * N for b in range(t)]
    for s in sources:
        seen = bytearray(n)
        seen[s] = 1
        frontier = [s]
        reached = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < off:
                    a, x = divmod(u, N)
                    for j in out_of[a]:
                        v = off + darts_b[j] * N + fwd[j][x]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    b, y = divmod(u - off, N)
                    for j in into[b]:
                        v = darts_a[j] * N + bwd[j][y]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            reached += len(nxt)
            if not nxt:
                break
            frontier = nxt
        total += n - reached
    return total


def _attempt(d, D, t, N, rng, deadline, steps):
    """Random base and group of order N, then local search on voltages. Returns (n, edges) or None."""
    grp = _pick_group(N, rng)
    if grp is None:
        return None
    mul, inv = _make_group(*grp)
    base = _regular_base(t, d, rng)
    L = len(base)
    darts_a = [a for a, _ in base]
    darts_b = [b for _, b in base]
    out_of = [[] for _ in range(t)]
    into = [[] for _ in range(t)]
    for j in range(L):
        out_of[darts_a[j]].append(j)
        into[darts_b[j]].append(j)

    gs = [rng.randrange(N) for _ in range(L)]
    fwd = [None] * L
    bwd = [None] * L
    for j in range(L):
        fwd[j], bwd[j] = _perms(gs[j], N, mul, inv)
    cur = _unreached(t, N, D, darts_a, darts_b, out_of, into, fwd, bwd)

    for _ in range(steps):
        if cur == 0 or time.monotonic() >= deadline:
            break
        j = rng.randrange(L)
        old = (gs[j], fwd[j], bwd[j])
        gs[j] = rng.randrange(N)
        fwd[j], bwd[j] = _perms(gs[j], N, mul, inv)
        new = _unreached(t, N, D, darts_a, darts_b, out_of, into, fwd, bwd)
        if new <= cur or rng.random() < 0.02:
            cur = new
        else:
            gs[j], fwd[j], bwd[j] = old

    if cur != 0:
        return None

    off = t * N
    edges = set()
    for j in range(L):
        a = darts_a[j]
        b = darts_b[j]
        f = fwd[j]
        for x in range(N):
            edges.add((a * N + x, off + b * N + f[x]))
    return 2 * off, sorted(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.75 * time_limit, time_limit - 8.0)

    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if D == 2:
        return _complete(d)
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    best = _complete(d)  # always valid fallback
    bound = lib.moore_bound(d, D)
    rng = random.Random(seed)

    while time.monotonic() < deadline:
        if best[0] >= bound:
            break
        t = rng.choice([1, 2, 2, 3, 3, 4])
        N = best[0] // (2 * t) + 1  # smallest order that would beat the current best
        if 2 * t * N > bound:
            continue
        res = _attempt(d, D, t, N, rng, deadline, 200)
        if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
            best = res

    return best
