import itertools
import time

import lib


# ----------------------------------------------------------------------------
# New construction for D = 3: cyclic Haar graphs from difference covers.
#
# The Haar graph H(Z_m, S) has parts a_i, b_j with a_i ~ b_{i+s} for s in S.
# It is bipartite and d-regular when |S| = d. Its diameter is at most 3 exactly
# when the difference set S - S covers every nonzero residue of Z_m:
#   - same side, distance 2: a_i to a_j needs j - i in S - S;
#   - cross side, distance 1 or 3: x = s0 + (x - s0) with x - s0 in S - S for
#     some s0 in S, so the covering condition also gives the cross pairs.
# The order is 2m, and m <= d(d-1)+1. Perfect difference sets (m = d(d-1)+1)
# need d-1 to be a prime power, so for other d we search for near-perfect
# covers, which is the part the C engine does.
#
# C engine: for m = mlo, mlo+1, ... it runs simulated annealing on the set S
# (0 fixed, k-1 free elements), minimising the number of uncovered nonzero
# residues. On success it moves to the next m. It prints the Haar graph of the
# largest m it covered.
# ----------------------------------------------------------------------------

C_DC = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 64
#define MAXM 1024

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int K, M, U;
static int S[MAXK];
static int inS[MAXM];
static int cnt[MAXM];

static inline int md(int x) { return x < 0 ? x + M : x; }

static void dec_d(int x) { if (--cnt[x] == 0) U++; }
static void inc_d(int x) { if (cnt[x]++ == 0) U--; }

static void remove_el(int i) {
    int s = S[i];
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        int a = S[j];
        dec_d(md(a - s));
        dec_d(md(s - a));
    }
    inS[s] = 0;
}

static void add_el(int i, int t) {
    for (int j = 0; j < K; j++) {
        if (j == i) continue;
        int a = S[j];
        inc_d(md(a - t));
        inc_d(md(t - a));
    }
    S[i] = t;
    inS[t] = 1;
}

static void init_random(void) {
    memset(inS, 0, sizeof(int) * (size_t)M);
    memset(cnt, 0, sizeof(int) * (size_t)M);
    U = M - 1;
    S[0] = 0;
    inS[0] = 1;
    for (int i = 1; i < K; i++) {
        int t;
        do { t = 1 + rndi(M - 1); } while (inS[t]);
        S[i] = t;
        inS[t] = 1;
    }
    for (int i = 0; i < K; i++)
        for (int j = i + 1; j < K; j++) {
            inc_d(md(S[i] - S[j]));
            inc_d(md(S[j] - S[i]));
        }
}

/* Anneal S for modulus M within tlimit CPU seconds. Returns 1 if U == 0. */
static int search_m(double tlimit) {
    init_random();
    if (U == 0) return 1;
    clock_t t0 = clock();
    double cyc = tlimit / 3.0;
    if (cyc < 0.3) cyc = 0.3;
    const double T0 = 1.2, T1 = 0.04;
    double T = T0;
    long it = 0;
    for (;;) {
        if ((it & 255) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el >= tlimit) return 0;
            double ph = fmod(el, cyc) / cyc;
            T = T0 * pow(T1 / T0, ph);
        }
        it++;
        int i = 1 + rndi(K - 1);
        int t;
        do { t = 1 + rndi(M - 1); } while (inS[t]);
        int s = S[i];
        int oldU = U;
        remove_el(i);
        add_el(i, t);
        int delta = U - oldU;
        if (delta <= 0 || rndu() < exp(-delta / T)) {
            if (U == 0) return 1;
        } else {
            remove_el(i);
            add_el(i, s);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    K = atoi(argv[1]);
    int mlo = atoi(argv[2]);
    int mhi = atoi(argv[3]);
    uint64_t sd = strtoull(argv[4], NULL, 10);
    double budget = atof(argv[5]);
    rs ^= sd * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd64();
    if (K < 2 || K > MAXK) { printf("0 0\n"); return 0; }
    if (mlo < K + 1) mlo = K + 1;
    if (mhi > K * (K - 1) + 1) mhi = K * (K - 1) + 1;
    if (mhi >= MAXM) mhi = MAXM - 1;

    clock_t tstart = clock();
    int bestM = 0;
    int bestS[MAXK];
    int fails = 0;
    int m = mlo;
    while (m <= mhi) {
        double el = (double)(clock() - tstart) / CLOCKS_PER_SEC;
        double rem = budget - el;
        if (rem < 0.1) break;
        double slice = (fails == 0) ? 0.5 * rem : 0.9 * rem;
        M = m;
        if (search_m(slice)) {
            bestM = m;
            memcpy(bestS, S, sizeof(int) * (size_t)K);
            m++;
            fails = 0;
        } else {
            fails++;
            if (fails >= 2) break;
        }
    }

    if (bestM == 0) { printf("0 0\n"); return 0; }
    int n = 2 * bestM;
    printf("%d %d\n", n, bestM * K);
    for (int i = 0; i < bestM; i++)
        for (int j = 0; j < K; j++)
            printf("%d %d\n", i, bestM + (i + bestS[j]) % bestM);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# D = 4 construction (kept from the parent): incidence graph of W(q).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# C wrapper for the difference-cover search.
# ----------------------------------------------------------------------------

def _c_difference_cover(d, mlo, mhi, seed, budget):
    """Run the C search; return (n, edges) of a Haar graph or None on any failure."""
    if budget < 0.5:
        return None
    try:
        out = lib.run_c(C_DC, [d, mlo, mhi, seed, round(budget, 2)],
                        timeout=budget + 5.0)
        n, e = lib.parse_graph_text(out)
    except Exception:
        return None
    if n < 2:
        return None
    return n, e


# ----------------------------------------------------------------------------
# Driver.
#   D == 3: best of (PG(2,d-1) if d-1 is a prime power, C difference-cover
#           Haar graph using most of the time budget).
#   D == 4: W(q) incidence graph.
#   else  : K_{d,d}.
# Every candidate is checked with lib.is_valid. K_{d,d} is the fallback.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    def elapsed():
        return time.monotonic() - start

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
            if d >= 2 and lib.is_prime_power(d - 1):
                consider(lib.projective_plane_incidence(d - 1))
            if d >= 2:
                mhi = d * (d - 1) + 1
                mlo = max(d + 1, int(0.6 * mhi))
                budget = 0.85 * time_limit - elapsed() - 1.5
                if budget >= 0.5:
                    consider(_c_difference_cover(d, mlo, mhi, seed, budget))
        elif D == 4:
            consider(_best_gq(d))
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
