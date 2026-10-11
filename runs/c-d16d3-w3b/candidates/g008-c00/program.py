import time

import lib


# ----------------------------------------------------------------------------
# Construction: bi-Cayley (Haar) graphs over Z_m.
#
# H(m, S) has parts A = {a_i} and B = {b_j}, with a_i ~ b_{i+s} for s in S, and
# |S| = d, so the graph is d-regular and bipartite with 2m vertices.
#
# If every nonzero residue of Z_m is a difference s - t (s, t in S, s != t),
# then H(m, S) has diameter 3:
#   - a_i, a_j and b_i, b_j are at distance 2 (a common neighbour exists),
#   - a_i, b_j with j - i = r != 0 are at distance <= 3 via r = (s - t) + u,
#   - a_i, b_i are at distance <= 3 via -u = s - t for any u in S.
#
# So the problem is to find a d-element "difference cover" of Z_m with m as large
# as possible. The upper bound is m <= d(d-1)+1, and equality needs a planar
# difference set. The C engine does simulated annealing on S, minimising the
# number of uncovered nonzero residues.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXM 1024
#define MAXK 64

static int M, K;
static int S[MAXK];
static int inS[MAXM];
static int cnt[MAXM];
static int zeros;
static uint64_t rs;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int k) { return (int)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int md(int x) { x %= M; return x < 0 ? x + M : x; }
static void inc(int r) { if (cnt[r]++ == 0) zeros--; }
static void dec(int r) { if (--cnt[r] == 0) zeros++; }

/* Add or remove all ordered differences between value y and every S[j], j != skip. */
static void add_val(int y, int skip) {
    for (int j = 0; j < K; j++) if (j != skip) {
        inc(md(y - S[j]));
        inc(md(S[j] - y));
    }
}
static void rem_val(int x, int skip) {
    for (int j = 0; j < K; j++) if (j != skip) {
        dec(md(x - S[j]));
        dec(md(S[j] - x));
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    M = atoi(argv[1]);
    K = atoi(argv[2]);
    rs = 0x9E3779B97F4A7C15ULL ^ ((uint64_t)strtoull(argv[3], NULL, 10) * 0xBF58476D1CE4E5B9ULL + 777ULL);
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    if (M < 2 || M >= MAXM || K < 1 || K > MAXK || K >= M) { printf("FAIL\n"); return 0; }
    if ((long)K * (K - 1) < (long)(M - 1)) { printf("FAIL\n"); return 0; }

    clock_t t0 = clock();
    for (int r = 0; r < MAXM; r++) { cnt[r] = 0; inS[r] = 0; }
    zeros = M - 1;
    for (int i = 0; i < K; i++) {
        int v;
        do { v = rint_(M); } while (inS[v]);
        inS[v] = 1;
        S[i] = v;
    }
    for (int i = 0; i < K; i++)
        for (int j = 0; j < K; j++)
            if (i != j) inc(md(S[i] - S[j]));

    int found = (zeros == 0);
    double frac = 0.0;
    long it = 0;
    while (!found) {
        if ((it & 4095) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > tl) break;
            frac = el / tl;
        }
        it++;
        double T = 0.05 + 0.5 * (1.0 - frac);
        int i = rint_(K);
        int x = S[i], y;
        do { y = rint_(M); } while (inS[y]);
        int old = zeros;
        rem_val(x, i);
        add_val(y, i);
        int delta = zeros - old;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            S[i] = y;
            inS[x] = 0;
            inS[y] = 1;
            if (zeros == 0) found = 1;
        } else {
            rem_val(y, i);
            add_val(x, i);
        }
    }

    if (found) {
        printf("OK");
        for (int i = 0; i < K; i++) printf(" %d", S[i]);
        printf("\n");
    } else {
        printf("FAIL\n");
    }
    return 0;
}
"""


def _cover(m, d, seed, budget):
    """Try to find a d-element difference cover of Z_m within `budget` seconds; return S or None."""
    if budget < 0.05:
        return None
    try:
        out = lib.run_c(C_SOURCE, [m, d, seed, round(budget, 3)], timeout=budget + 5)
    except RuntimeError:
        return None
    t = out.split()
    if len(t) != d + 1 or t[0] != "OK":
        return None
    try:
        S = [int(x) for x in t[1:]]
    except ValueError:
        return None
    return S


def _haar_search(d, D, seed, end):
    """Return (m, S) for the largest m found with a valid difference cover, or None."""
    hi = d * (d - 1) + 1
    lo = max(d + 1, int(0.6 * hi))
    best = None

    # Pass 1: scan downwards with short budgets and stop at the first success.
    for m in range(hi, lo - 1, -1):
        left = end - time.monotonic()
        if left <= 0.1:
            return best
        S = _cover(m, d, seed + m, min(0.2, left))
        if S is not None:
            best = (m, S)
            break
    if best is None:
        return None

    # Pass 2: retry the larger m values that failed, with longer budgets, upwards.
    cands = list(range(best[0] + 1, hi + 1))
    for i, m in enumerate(cands):
        left = end - time.monotonic()
        if left <= 0.2:
            break
        budget = left / (len(cands) - i)
        S = _cover(m, d, seed + 7 * m, budget)
        if S is not None:
            best = (m, S)
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    end = t0 + 0.8 * time_limit - 1.0

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    # Haar graphs have diameter 3, so they are valid for D >= 3.
    if D >= 3 and d >= 2 and end - time.monotonic() > 1.0:
        try:
            res = _haar_search(d, D, seed, end)
        except Exception:
            res = None
        if res is not None:
            m, S = res
            n, E = lib.haar_graph(m, S)
            if n > best[0] and lib.is_valid(n, E, d, D):
                best = (n, E)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
