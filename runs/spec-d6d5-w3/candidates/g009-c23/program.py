import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Baseline families (cheap, D >= 3): projective plane incidence graph and the
# Araujo-Pardo-Lopez graph. They provide a floor if the main search fails.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= min(d - 1, 31)."""
    for q in range(min(d - 1, 31), 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3, else None."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Main construction: cyclic Haar graphs (bi-Cayley over Z_m with one base pair).
#
# Haar graph H(m, S): A_i ~ B_j iff j - i in S, |S| = d, 0 in S (WLOG).
# H is vertex-transitive on each side and has an automorphism swapping the
# sides, so diameter <= D reduces to two sumset conditions from A_0:
#   * every A_x is at even distance <= D:  Z_m = E_{floor(D/2)}
#   * every B_y is at odd distance <= D:   Z_m = S + E_{floor((D-1)/2)}
# where E_0 = {0} and E_t = E_{t-1} + (S - S).
# The cost (uncovered count) is cheap to evaluate with numpy, so a hill-climb
# over S can scan many cyclic orders m quickly.
# ----------------------------------------------------------------------------

def _uncovered(m, S, D):
    """Number of residues not covered by the two sumset conditions. Zero means diameter <= D."""
    ta, tb = D // 2, (D - 1) // 2
    d1 = np.array(sorted({(a - b) % m for a in S for b in S}), dtype=np.int64)
    levels = [np.zeros(m, dtype=bool)]
    levels[0][0] = True
    for _ in range(max(ta, tb)):
        idx = np.flatnonzero(levels[-1])
        nxt = np.zeros(m, dtype=bool)
        for a in d1:
            nxt[(idx + a) % m] = True
        levels.append(nxt)
    uncov_a = m - int(levels[ta].sum())
    idx = np.flatnonzero(levels[tb])
    bcov = np.zeros(m, dtype=bool)
    for s in S:
        bcov[(idx + s) % m] = True
    return uncov_a + m - int(bcov.sum())


def _search_haar(d, D, m, rng, deadline):
    """Hill-climb a connection set S (|S| = d, 0 in S) in Z_m so H(m, S) has diameter <= D."""
    if m - 1 < d - 1:
        return None
    S = [0] + rng.sample(range(1, m), d - 1)
    c = _uncovered(m, S, D)
    while c > 0:
        if time.monotonic() >= deadline:
            break
        i = rng.randrange(1, d)
        x = rng.randrange(1, m)
        if x in S:
            continue
        T = S[:]
        T[i] = x
        ct = _uncovered(m, T, D)
        # Mostly greedy, with a small chance to accept a worse move (escapes plateaus).
        if ct <= c or rng.random() < 0.01:
            S, c = T, ct
    return S if c == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    target = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    # Calibration shortcut: a graph already at the Moore bound cannot be beaten.
    if best_n >= target:
        return best

    # Haar order m gives 2m vertices, so m <= target // 2 is necessary.
    moore_half = target // 2
    lo = best_n // 2 + 1
    while time.monotonic() < deadline and lo <= moore_half:
        hi = min(lo + 80, moore_half)
        m = rng.randint(lo, hi)
        S = _search_haar(d, D, m, rng,
                         min(deadline, time.monotonic() + 2.0))
        if S is not None:
            n, e = lib.haar_graph(m, S)
            consider(n, e)
            # Successes raise the floor so later attempts aim higher.
            lo = max(lo, m + 1)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
