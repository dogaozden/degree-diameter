import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction: cyclic Haar graphs from difference covers (diameter 3).
#
# Haar graph H(m, S): a_i ~ b_{i+s} for s in S, S a k-subset of Z_m, so the
# graph is bipartite, k-regular on 2m vertices. If the differences S - S cover
# all of Z_m, every same-side pair is at distance <= 2 and every cross pair is
# at distance <= 3 (offset = s - t + u with s, t, u in S), so diameter <= 3.
# Since |S-S| <= k(k-1)+1, the order is at most 2(k^2-k+1), which for k = d is
# above the parent's 394 at d = 16. A C simulated-annealing search looks for
# such covering sets at m just above the parent's half-order.
#
# Fallback: the parent's arc-extended projective plane construction (Python),
# and K_{d,d} as the last resort.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

static unsigned long long rs = 88172645463325252ULL;
static unsigned long long rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int K, M, unc;
static int S[64];
static int cnt[4096];
static char inS[4096];

static int md(int a) { a %= M; if (a < 0) a += M; return a; }
static void addp(int r) { if (cnt[r]++ == 0) unc--; }
static void remp(int r) { if (--cnt[r] == 0) unc++; }

static void init_state(void) {
    memset(inS, 0, sizeof(inS));
    memset(cnt, 0, sizeof(int) * (size_t)M);
    unc = M - 1;
    S[0] = 0; inS[0] = 1;
    for (int i = 1; i < K; i++) {
        int x;
        do { x = (int)(rnd() % (unsigned long long)M); } while (inS[x]);
        S[i] = x; inS[x] = 1;
    }
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            if (i != j) addp(md(S[i] - S[j]));
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    K = atoi(argv[1]);
    M = atoi(argv[2]);
    rs ^= (unsigned long long)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL + 777ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    double tl = atof(argv[4]);
    if (K < 2 || K > 60 || M < 2 || M > 4000 || K > M) { printf("FAIL\n"); return 0; }

    clock_t c0 = clock();
    const double T = 0.5;
    init_state();
    long it = 0, last_improve = 0;
    int best_unc = unc;
    while (unc > 0) {
        if ((it & 1023) == 0) {
            if ((double)(clock() - c0) / CLOCKS_PER_SEC > tl) break;
        }
        it++;
        int i = 1 + (int)(rnd() % (unsigned long long)(K - 1));
        int y = (int)(rnd() % (unsigned long long)M);
        if (inS[y]) continue;
        int x = S[i];
        int before = unc;
        for (int j = 0; j < K; j++)
            if (j != i) { remp(md(x - S[j])); remp(md(S[j] - x)); }
        for (int j = 0; j < K; j++)
            if (j != i) { addp(md(y - S[j])); addp(md(S[j] - y)); }
        int delta = unc - before;
        if (delta <= 0 || rnd01() < exp(-delta / T)) {
            S[i] = y; inS[x] = 0; inS[y] = 1;
        } else {
            for (int j = 0; j < K; j++)
                if (j != i) { remp(md(y - S[j])); remp(md(S[j] - y)); }
            for (int j = 0; j < K; j++)
                if (j != i) { addp(md(x - S[j])); addp(md(S[j] - x)); }
        }
        if (unc < best_unc) { best_unc = unc; last_improve = it; }
        if (it - last_improve > 200000) {
            init_state();
            best_unc = unc;
            last_improve = it;
        }
    }
    if (unc == 0) {
        printf("OK %d %d\n", M, K);
        for (int i = 0; i < K; i++) printf("%d ", S[i]);
        printf("\n");
    } else {
        printf("FAIL\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Parent's arc-extended projective plane construction (fallback, diameter 3).
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, nbr):
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs
        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, SA, SB))
    return out


# ----------------------------------------------------------------------------
# Difference-cover Haar search driver.
# ----------------------------------------------------------------------------

def _covers(S, m):
    """True if the nonzero differences of S cover every nonzero residue mod m."""
    diffs = {(a - b) % m for a in S for b in S if a != b}
    return all(r in diffs for r in range(1, m))


def _haar_cover(k, m, seed, budget):
    """Run the C annealer for a k-subset of Z_m covering all nonzero differences; return S or None."""
    try:
        out = lib.run_c(C_SOURCE, [k, m, seed, round(budget, 2)],
                        stdin_graph=None, timeout=budget + 5.0)
    except RuntimeError:
        return None
    tok = out.split()
    if len(tok) != 3 + k or tok[0] != "OK":
        return None
    try:
        S = [int(x) for x in tok[3:]]
    except ValueError:
        return None
    if len(set(S)) != k or any(not 0 <= x < m for x in S) or not _covers(S, m):
        return None
    return S


def _haar_candidate(k, D, n0, deadline, seed, per):
    """Largest Haar graph of order > n0 found by binary search over m; None if none."""
    hi = k * (k - 1) + 1
    m0 = n0 // 2 + 1
    if k < 2 or m0 > hi:
        return None

    def attempt(m):
        budget = min(per, deadline - time.monotonic() - 0.5)
        if budget < 0.3:
            return None
        return _haar_cover(k, m, seed * 1009 + m, budget)

    S0 = attempt(m0)
    if S0 is None:
        return None
    lo, best, hi_try = m0, S0, hi
    while lo < hi_try and time.monotonic() < deadline - 1.0:
        mid = (lo + hi_try + 1) // 2
        S = attempt(mid)
        if S is not None:
            lo, best = mid, S
        else:
            hi_try = mid - 1
    n, e = lib.haar_graph(lo, best)
    if lib.is_valid(n, e, k, D):
        return n, e
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe baseline: K_{d,d} has diameter 2 <= D.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])

    if D >= 3:
        # Fallback: arc-extended projective plane (diameter 3).
        try:
            cands = _arc_extensions(d, t0 + 0.15 * time_limit, random.Random(seed * 7919 + d))
            cands.sort(key=lambda t: -t[0])
            for n_c, e_c in cands:
                if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
                    best = (n_c, e_c)
                    break
        except Exception:
            pass

        # Bold path: difference-cover Haar graph that beats the current best order.
        try:
            deadline = t0 + 0.9 * time_limit - 1.5
            remaining = max(0.0, deadline - time.monotonic())
            per = max(0.8, 0.12 * remaining)
            H = _haar_candidate(d, D, best[0], deadline, seed, per)
            if H is not None and H[0] > best[0] and lib.is_valid(H[0], H[1], d, D):
                best = H
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
        if not lib.is_valid(best[0], best[1], d, D):
            best = (2, [(0, 1)])
    return best
