"""Haar-graph difference-cover search for bipartite graphs with diameter D (D >= 3).

Construction: for a cyclic group Z_G and a connection set S of size d, the Haar
graph H(G, S) has vertices A_i = i and B_j = G + j, with edges A_i - B_{(i+s) mod G}
for s in S. It is d-regular and bipartite, with 2G vertices.

Diameter 3 holds exactly when the difference set S - S covers all of Z_G:
  - same-side pairs A_i, A_i' share a neighbour iff i' - i lies in S - S;
  - cross pairs A_i, B_j are at distance <= 3 because S - S + S = Z_G whenever S - S = Z_G.

So the task is to find, for the largest G possible, a d-subset S with S - S = Z_G.
The C engine runs simulated annealing on the number of uncovered nonzero differences,
increasing G after each success. The Moore bound for d = 16, D = 3 is 482 = 2 * 241,
and the cyclic version of the problem caps G at d(d-1) + 1.

Fallbacks: K_{d,d} (diameter 2) and PG(2, q) incidence graphs (diameter 3). Every
candidate is checked with lib.is_valid before it can replace the current best.
"""
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXD 64
#define MAXG 1100

static uint64_t rs = 88172645463325252ULL;

static uint32_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return (uint32_t)(rs >> 16);
}

static double urand(void) {
    return (double)rnd() / 4294967296.0;
}

static int d, G;
static int S[MAXD];
static int cnt[MAXG];     /* cnt[x] = number of ordered pairs (s,t), s != t, with s - t = x */
static int U;             /* number of x in 1..G-1 with cnt[x] == 0 */
static int bestS[MAXD];
static int bestG = 0;

static int md(int a) {
    a %= G;
    if (a < 0) a += G;
    return a;
}

static void recount(void) {
    for (int x = 0; x < G; x++) cnt[x] = 0;
    for (int i = 0; i < d; i++)
        for (int j = 0; j < d; j++)
            if (i != j) cnt[md(S[i] - S[j])]++;
    U = 0;
    for (int x = 1; x < G; x++)
        if (cnt[x] == 0) U++;
}

/* Set S[p] = v and update cnt and U incrementally. */
static void setval(int p, int v) {
    for (int j = 0; j < d; j++) {
        if (j == p) continue;
        int x = md(S[p] - S[j]);
        int y = md(S[j] - S[p]);
        if (--cnt[x] == 0) U++;
        if (--cnt[y] == 0) U++;
    }
    S[p] = v;
    for (int j = 0; j < d; j++) {
        if (j == p) continue;
        int x = md(S[p] - S[j]);
        int y = md(S[j] - S[p]);
        if (cnt[x]++ == 0) U--;
        if (cnt[y]++ == 0) U--;
    }
}

static int contains(int v) {
    for (int k = 0; k < d; k++)
        if (S[k] == v) return 1;
    return 0;
}

/* Simulated annealing at fixed G. Returns 1 if S - S covers Z_G. */
static int search(long iters, clock_t deadline) {
    for (int i = 0; i < d; ) {
        int v = (int)(rnd() % (uint32_t)G);
        int dup = 0;
        for (int k = 0; k < i; k++)
            if (S[k] == v) dup = 1;
        if (!dup) S[i++] = v;
    }
    recount();
    for (long it = 0; it < iters && U > 0; it++) {
        if ((it & 4095) == 0 && clock() > deadline) break;
        double T = 0.03 + 0.7 * (1.0 - (double)it / (double)iters);
        int p = (int)(rnd() % (uint32_t)d);
        int v = (int)(rnd() % (uint32_t)G);
        if (contains(v)) continue;
        int old = S[p];
        int oldU = U;
        setval(p, v);
        int dU = U - oldU;
        if (dU <= 0 || urand() < exp(-(double)dU / T)) continue;
        setval(p, old);
    }
    return U == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }

    clock_t t0 = clock();
    clock_t deadline = t0 + (clock_t)(budget * CLOCKS_PER_SEC);

    long base = 20000;
    long iters = base;
    G = d + 1;
    /* Non-zero differences number d(d-1), so G - 1 <= d(d-1) is necessary. */
    while (G - 1 <= d * (d - 1) && G < MAXG && clock() < deadline) {
        if (search(iters, deadline)) {
            bestG = G;
            memcpy(bestS, S, sizeof(int) * d);
            G++;
            iters = base;
        } else {
            if (clock() >= deadline) break;
            if (iters < (1L << 40)) iters *= 2;
        }
    }

    if (bestG == 0) {
        printf("0 0\n");
        return 0;
    }
    G = bestG;
    printf("%d %d\n", 2 * G, G * d);
    for (int i = 0; i < G; i++)
        for (int k = 0; k < d; k++)
            printf("%d %d\n", i, G + (i + bestS[k]) % G);
    return 0;
}
"""


def _c_haar(d, D, seed, budget):
    """Run the difference-cover engine; return (n, edges) or None on any failure."""
    if budget < 0.5:
        return None
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)], timeout=budget + 10.0)
        n, e = lib.parse_graph_text(out)
    except Exception:
        return None
    if n < 2:
        return None
    return n, e


def _pg_candidate(d):
    """Incidence graph of PG(2, q), q the largest prime power with q + 1 <= d. Diameter 3."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(g):
        nonlocal best, best_n
        if g is None:
            return
        n, e = g
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        try:
            consider(_pg_candidate(d))
        except Exception:
            pass

    if D >= 3 and d >= 2:
        # Spend most of the budget on the difference-cover search.
        budget = 0.80 * time_limit - (time.monotonic() - t0) - 2.0
        if budget >= 1.0:
            consider(_c_haar(d, D, seed, budget))

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
