"""Diameter-3 bipartite search via Haar graphs of difference covers.

For D = 3, the Haar graph H(G, S) of a finite abelian group G has sides G x {0} and G x {1},
with a_g adjacent to b_{g+s} for s in S. It has 2|G| vertices, is |S|-regular and bipartite,
and has diameter at most 3 exactly when S - S = G (every group element is a difference of two
elements of S). With |S| = d this gives max degree d. The C engine searches over groups
Z_A x Z_B (A*B = N, for increasing N) and over sets S of size d by simulated annealing,
minimising the number of uncovered nonzero differences. The largest N that gets full coverage
gives the graph with 2N vertices. Python rebuilds the graph from (A, B, S), checks it with
lib.is_valid, and falls back to K_{d,d} (diameter 2, valid for every D >= 2) if anything fails.
"""
import time

import lib

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXG 400
#define MAXK 64
#define ITERS 4000000L

static int G, A, B, K;
static int sub_t[MAXG][MAXG];
static int S[MAXK];
static int inS[MAXG];
static int cnt[MAXG];
static int unc;
static unsigned long long rs = 0x9E3779B97F4A7C15ULL;

static unsigned long long rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd64() % (unsigned long long)k); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static inline void bump(int g, int delta) {
    if (delta > 0) {
        if (cnt[g] == 0) unc--;
        cnt[g]++;
    } else {
        cnt[g]--;
        if (cnt[g] == 0) unc++;
    }
}

/* A pair {x, y} contributes the differences x-y and y-x. */
static inline void pair_upd(int x, int y, int delta) {
    bump(sub_t[x][y], delta);
    bump(sub_t[y][x], delta);
}

static void build_sub(void) {
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++) {
            int u = ((x / B) - (y / B) + A) % A;
            int v = ((x % B) - (y % B) + B) % B;
            sub_t[x][y] = u * B + v;
        }
}

static void init_state(void) {
    for (int g = 0; g < G; g++) {
        inS[g] = 0;
        cnt[g] = 0;
    }
    unc = G - 1;
    S[0] = 0;
    inS[0] = 1;
    for (int i = 1; i < K; i++) {
        int t;
        do {
            t = 1 + rndint(G - 1);
        } while (inS[t]);
        S[i] = t;
        inS[t] = 1;
    }
    for (int i = 0; i < K; i++)
        for (int j = i + 1; j < K; j++) pair_upd(S[i], S[j], +1);
}

/* Simulated annealing on S (S[0] = 0 fixed). Returns 1 when all nonzero differences are covered. */
static int anneal(long iters, double T0, double T1, double deadline) {
    double lr = log(T1 / T0);
    for (long it = 0; it < iters; it++) {
        if (unc == 0) return 1;
        if ((it & 4095) == 0 && now() > deadline) return 0;
        double T = T0 * exp(lr * (double)it / (double)iters);
        int i = 1 + rndint(K - 1);
        int old = S[i];
        int t;
        do {
            t = 1 + rndint(G - 1);
        } while (inS[t]);
        int before = unc;
        for (int j = 0; j < K; j++)
            if (j != i) pair_upd(old, S[j], -1);
        inS[old] = 0;
        for (int j = 0; j < K; j++)
            if (j != i) pair_upd(t, S[j], +1);
        S[i] = t;
        inS[t] = 1;
        int delta = unc - before;
        if (delta > 0 && rnd01() >= exp(-(double)delta / T)) {
            for (int j = 0; j < K; j++)
                if (j != i) pair_upd(t, S[j], -1);
            inS[t] = 0;
            for (int j = 0; j < K; j++)
                if (j != i) pair_upd(old, S[j], +1);
            S[i] = old;
            inS[old] = 1;
        }
    }
    return unc == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (unsigned long long)seed * 0x2545F4914F6CDD1DULL + 1ULL;
    if (rs == 0) rs = 1;
    if (D != 3 || d < 2 || d > MAXK) {
        printf("0\n");
        return 0;
    }
    K = d;
    double deadline = now() + budget;
    int bestN = 0, bestA = 0, bestB = 0;
    int bestS[MAXK];
    int fails = 0;

    for (int N = K + 1; N < MAXG && now() < deadline; N++) {
        if ((long)(N - 1) > (long)K * (K - 1)) break;
        int ok = 0;
        for (int Aa = 1; Aa <= N && !ok && now() < deadline; Aa++) {
            if (N % Aa) continue;
            int Bb = N / Aa;
            if (Aa > Bb) continue;
            G = N;
            A = Aa;
            B = Bb;
            build_sub();
            for (int rep = 0; rep < 2 && !ok && now() < deadline; rep++) {
                init_state();
                if (anneal(ITERS, 1.2, 0.15, deadline)) {
                    ok = 1;
                    bestN = N;
                    bestA = Aa;
                    bestB = Bb;
                    memcpy(bestS, S, sizeof(int) * (size_t)K);
                }
            }
        }
        if (ok) {
            fails = 0;
        } else {
            fails++;
            if (fails >= 3) break;
        }
    }

    if (bestN == 0) {
        printf("0\n");
        return 0;
    }
    printf("%d %d %d\n", bestA, bestB, K);
    for (int i = 0; i < K; i++) printf("%d ", bestS[i]);
    printf("\n");
    return 0;
}
"""


def _haar_group(A, B, S):
    """Haar graph of the group Z_A x Z_B (element u*B+v) with connection set S: a_g ~ b_{g+s}."""
    G = A * B

    def add(x, y):
        return ((x // B + y // B) % A) * B + (x % B + y % B) % B

    edges = [(g, G + add(g, s)) for g in range(G) for s in S]
    return 2 * G, edges


def _haar_search(d, seed, budget):
    """Run the C difference-cover search and rebuild the graph. Returns (n, edges) or None."""
    text = lib.run_c(C_SOURCE, [d, 3, seed, f"{budget:.2f}"], timeout=budget + 10.0)
    nums = text.split()
    if not nums or nums[0] == "0":
        return None
    A, B, k = int(nums[0]), int(nums[1]), int(nums[2])
    S = [int(x) for x in nums[3:3 + k]]
    if len(S) != k or k != d:
        return None
    return _haar_group(A, B, S)


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about the time limit."""
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    best = fallback if lib.is_valid(fallback[0], fallback[1], d, D) else None

    if D == 3 and d >= 2:
        budget = max(1.0, 0.85 * time_limit - 3.0)
        try:
            res = _haar_search(d, seed, budget)
        except Exception:
            res = None
        if res is not None and lib.is_valid(res[0], res[1], d, D):
            if best is None or res[0] > best[0]:
                best = res

    if best is None:
        return 1, []
    return best
