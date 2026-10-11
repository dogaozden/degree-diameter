import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: Haar graphs from difference covers.
#
# For a set S of k residues in Z_m, the Haar graph H(m, S) is bipartite,
# k-regular, and has 2m vertices. It has diameter <= 3 exactly when S - S
# covers all of Z_m (then S - S + s0 = Z_m for any s0 in S, which handles
# the mixed pairs). So the task is: find the largest m admitting a k-subset
# of Z_m whose difference set is all of Z_m. The Moore bound for D = 3 is
# 2(k^2 - k + 1), reached only by perfect difference sets, which do not exist
# for k = 16. The C search below uses simulated annealing on the number of
# uncovered nonzero residues, with one element moved per step, and increases m
# as long as it succeeds.
# ----------------------------------------------------------------------------

HAAR_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 64
#define MAXM 4096

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int K, M;
static int S[MAXK];
static int cnt[MAXM];
static int unc;
static double budget;
static clock_t t0;
static int timed_out = 0;

static int md(int x) { x %= M; if (x < 0) x += M; return x; }

static void dec(int x) { if (x == 0) return; cnt[x]--; if (cnt[x] == 0) unc++; }
static void inc(int x) { if (x == 0) return; if (cnt[x] == 0) unc--; cnt[x]++; }

static void recompute(void) {
    for (int x = 0; x < M; x++) cnt[x] = 0;
    unc = M - 1;
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++) {
            if (i == j) continue;
            inc(md(S[i] - S[j]));
        }
}

static void remove_el(int i) {
    int s = S[i];
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        int t = S[j];
        dec(md(s - t));
        dec(md(t - s));
    }
}

static void add_el(int i, int r) {
    S[i] = r;
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        int t = S[j];
        inc(md(r - t));
        inc(md(t - r));
    }
}

static int in_prefix(int r, int n) {
    for (int j = 0; j < n; j++) if (S[j] == r) return 1;
    return 0;
}

static int attempt(long iters) {
    S[0] = 0;
    for (int i = 1; i < K; i++) {
        int r;
        do { r = rndi(M); } while (in_prefix(r, i));
        S[i] = r;
    }
    recompute();
    int cur = unc;
    const double T0 = 1.0, T1 = 0.03;
    for (long it = 0; it < iters; it++) {
        if (unc == 0) return 1;
        if ((it & 65535) == 0) {
            if ((double)(clock() - t0) / CLOCKS_PER_SEC > budget) { timed_out = 1; return 0; }
        }
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        int i = 1 + rndi(K - 1);
        int s = S[i];
        int r;
        do { r = rndi(M); } while (in_prefix(r, K));
        remove_el(i);
        add_el(i, r);
        int delta = unc - cur;
        if (delta <= 0 || rndu() < exp(-(double)delta / T)) {
            cur = unc;
        } else {
            remove_el(i);
            add_el(i, s);
        }
    }
    return unc == 0;
}

int main(int argc, char **argv) {
    if (argc < 4) return 1;
    K = atoi(argv[1]);
    unsigned long seed = strtoul(argv[2], NULL, 10);
    budget = atof(argv[3]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();
    if (K < 2 || K > MAXK) { printf("0 0\n"); return 0; }

    t0 = clock();
    int bestM = 0;
    int bestS[MAXK];
    int maxM = K * (K - 1) + 1;
    if (maxM > MAXM - 1) maxM = MAXM - 1;

    int m = K + 1;
    while (m <= maxM && !timed_out) {
        M = m;
        long iters = 300000;
        int ok = 0;
        while (!ok && !timed_out) {
            ok = attempt(iters);
            if (!ok && iters < 200000000L) iters *= 2;
        }
        if (!ok) break;
        bestM = M;
        for (int i = 0; i < K; i++) bestS[i] = S[i];
        m++;
    }

    if (bestM == 0) { printf("0 0\n"); return 0; }
    printf("%d %d", bestM, K);
    for (int i = 0; i < K; i++) printf(" %d", bestS[i]);
    printf("\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Projective-plane arc extension (kept as a second candidate for D = 3).
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
    """True if every target is hit by at most s elements of S."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy choice so that every target is hit at most s times."""
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
    """Conic (plus nucleus for even q) as a point-index set."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
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
    """Return (n, edges) candidates from PG(2, q) plus arc-extension vertices, q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 0:
            continue
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
# Haar-graph search wrapper.
# ----------------------------------------------------------------------------

def _haar_search(d, seed, budget):
    """Run the difference-cover search for k = d; return the Haar graph (n, edges) or None."""
    if budget < 0.5:
        return None
    try:
        out = lib.run_c(HAAR_C, [d, seed, round(budget, 2)], timeout=budget + 10.0)
        nums = [int(x) for x in out.split()]
    except Exception:
        return None
    if len(nums) < 2 or nums[0] < 1 or nums[1] != d:
        return None
    m, k = nums[0], nums[1]
    S = nums[2:2 + k]
    if len(S) != k or len(set(x % m for x in S)) != k:
        return None
    return lib.haar_graph(m, S)


# ----------------------------------------------------------------------------
# Driver.
#   D == 3: Haar graph from the difference-cover search (main candidate),
#           arc-extended projective plane graphs (second candidate).
#   else  : K_{d,d} (diameter 2, valid for every D >= 2).
# Every candidate is checked with lib.is_valid; K_{d,d} is the always-valid fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    try:
        if D == 3:
            consider(_haar_search(d, seed, 0.60 * time_limit - 1.0))
            for g in _arc_extensions(d, start + 0.75 * time_limit,
                                     random.Random(seed * 7919 + d)):
                consider(g)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
