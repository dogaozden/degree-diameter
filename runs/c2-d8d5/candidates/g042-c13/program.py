import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over voltage lifts of bi-Cayley graphs.
#
# A graph is a lift over G = Z_m x| Z_k2 of a base graph with k left and k right
# blocks and d layers. Layer l joins left block i to right block sig[l][i] with
# voltage vol[l][i]: (i, x) ~ (sig, x*vol). Left multiplication is an
# automorphism, so the graph is vertex-transitive within each block. Therefore
# "all pairs within distance D" is equivalent to "each of the 2k block
# representatives reaches every vertex within D steps". The reach test uses one
# 64-bit mask per vertex (bit b = block b's representative reaches it), which is
# O(N*d*D) per evaluation instead of a full all-pairs bitset BFS.
# The annealer moves voltages and swaps layer permutations, and restarts over
# random groups with orders just above the current best.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;

#define KMAX 12
#define DMAX 16
#define GMAX 2000
#define MAXIT 20000
#define PATIENCE 3000

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, k_, G_, m_, k2_, r_;
static int *mul_ = NULL, *inv_ = NULL;
static int sig[DMAX][KMAX], sinv[DMAX][KMAX], vol[DMAX][KMAX];
static u64 *bufA = NULL, *bufB = NULL;
static int *bestE = NULL;
static int bestN = 0, bestM = 0;
static double tlimit;
static clock_t tstart;

static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int powmod_(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static int time_up(void) {
    return (double)(clock() - tstart) / CLOCKS_PER_SEC >= tlimit;
}

/* Choose k, and a group Z_m x| Z_k2 with order G > the bar. Returns 0 on failure. */
static int sample_group(int bar) {
    static const int K2S[11] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12};
    k_ = 1 + rint_(10);
    int minG = bar / (2 * k_) + 1;
    int target = minG + rint_(minG / 8 + 4);
    k2_ = K2S[rint_(11)];
    int m = (target + k2_ - 1) / k2_;
    if (m < 2) m = 2;
    int r = 1 % m;
    if (k2_ > 1 && m > 2) {
        for (int t = 0; t < 200; t++) {
            int c = 2 + rint_(m - 2);
            if (gcd_(c, m) == 1 && powmod_(c, k2_, m) == 1 % m) { r = c; break; }
        }
    }
    int G = m * k2_;
    if (G > GMAX || G < minG) return 0;
    if (2 * k_ * G <= bar) return 0;
    m_ = m;
    r_ = r;
    G_ = G;
    return 1;
}

static void build_group(void) {
    int m = m_, k2 = k2_, r = r_;
    int G = m * k2;
    G_ = G;
    int pw[KMAX + 1];
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < G; y++) {
            int c = y / k2, dd = y % k2;
            mul_[x * G + y] = ((a + pw[b] * c) % m) * k2 + (b + dd) % k2;
        }
    }
    for (int x = 0; x < G; x++) {
        for (int y = 0; y < G; y++) {
            if (mul_[x * G + y] == 0) { inv_[x] = y; break; }
        }
    }
}

static void swap_sig(int l, int i1, int i2) {
    int a = sig[l][i1], b = sig[l][i2];
    sig[l][i1] = b;
    sig[l][i2] = a;
    sinv[l][b] = i1;
    sinv[l][a] = i2;
}

static void random_state(void) {
    for (int l = 0; l < d_; l++) {
        int p[KMAX];
        for (int i = 0; i < k_; i++) p[i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < k_; i++) { sig[l][i] = p[i]; sinv[l][p[i]] = i; }
        for (int i = 0; i < k_; i++) vol[l][i] = rint_(G_);
    }
}

/* Number of (block representative, vertex) pairs at distance > D_. Zero means valid. */
static long long eval_cost(void) {
    int k = k_, G = G_, d = d_;
    int N = 2 * k * G;
    int kG = k * G;
    u64 *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(u64) * (size_t)N);
    for (int b = 0; b < 2 * k; b++) cur[(size_t)b * G] = 1ULL << b;
    for (int it = 0; it < D_; it++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 x = cur[v];
            if (v < kG) {
                int i = v / G, y = v - i * G;
                for (int l = 0; l < d; l++) {
                    int u = (k + sig[l][i]) * G + mul_[y * G + vol[l][i]];
                    x |= cur[u];
                }
            } else {
                int j = v / G - k;
                int y = v - (j + k) * G;
                for (int l = 0; l < d; l++) {
                    int i = sinv[l][j];
                    int u = i * G + mul_[y * G + inv_[vol[l][i]]];
                    x |= cur[u];
                }
            }
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        u64 *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    long long cost = 0;
    int twok = 2 * k;
    for (int v = 0; v < N; v++) cost += twok - __builtin_popcountll(cur[v]);
    return cost;
}

static int anneal(void) {
    random_state();
    long long cost = eval_cost();
    if (cost == 0) return 1;
    double c0 = (double)cost;
    double T0 = fmax(2.0, 0.05 * c0), T1 = 0.3;
    long long best = cost, last = 0;
    for (long long t = 0; t < MAXIT; t++) {
        if ((t & 15) == 0 && time_up()) return 0;
        if (t - last > PATIENCE) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)MAXIT);
        int l = rint_(d_), i = rint_(k_);
        long long c2;
        if (rint_(10) < 7) {
            int old = vol[l][i];
            int ns = rint_(G_);
            if (ns == old) continue;
            vol[l][i] = ns;
            c2 = eval_cost();
            if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                vol[l][i] = old;
            }
        } else {
            int i2 = rint_(k_);
            if (i2 == i) continue;
            swap_sig(l, i, i2);
            c2 = eval_cost();
            if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                swap_sig(l, i, i2);
            }
        }
        if (cost < best) { best = cost; last = t; }
        if (cost == 0) return 1;
    }
    return cost == 0;
}

static void record_best(void) {
    int k = k_, G = G_, d = d_;
    int N = 2 * k * G;
    int *E = malloc(sizeof(int) * 2 * (size_t)N * d);
    int m = 0;
    for (int i = 0; i < k; i++) {
        for (int x = 0; x < G; x++) {
            int u = i * G + x;
            int seen[DMAX];
            int ns = 0;
            for (int l = 0; l < d; l++) {
                int v = (k + sig[l][i]) * G + mul_[x * G + vol[l][i]];
                int dup = 0;
                for (int q = 0; q < ns; q++) if (seen[q] == v) { dup = 1; break; }
                if (dup) continue;
                seen[ns++] = v;
                E[2 * m] = u;
                E[2 * m + 1] = v;
                m++;
            }
        }
    }
    free(bestE);
    bestE = E;
    bestN = N;
    bestM = m;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    tlimit = atof(argv[4]);
    int bar = argc > 5 ? atoi(argv[5]) : 0;
    if (d_ < 1 || d_ > DMAX || D_ < 1 || bar < 0) { printf("0 0\n"); return 0; }
    rs ^= (u64)seed * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;

    mul_ = malloc(sizeof(int) * (size_t)GMAX * GMAX);
    inv_ = malloc(sizeof(int) * (size_t)GMAX);
    bufA = malloc(sizeof(u64) * 2 * KMAX * GMAX);
    bufB = malloc(sizeof(u64) * 2 * KMAX * GMAX);
    if (!mul_ || !inv_ || !bufA || !bufB) { printf("0 0\n"); return 0; }

    tstart = clock();
    while (!time_up()) {
        if (!sample_group(bar)) continue;
        build_group();
        if (anneal()) {
            record_best();
            bar = bestN;
        }
    }

    if (bestN == 0) { printf("0 0\n"); return 0; }
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestE[2 * i], bestE[2 * i + 1]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (diameter 2). Verified before use.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions for D = 3.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if lib.is_prime_power(d - 1):
                return best
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    # Main phase: C annealer over voltage lifts of bi-Cayley graphs.
    # Leave margin for compilation, verification and output parsing.
    budget = time_limit - (time.monotonic() - t0) - 8.0
    if budget >= 2.0:
        try:
            out = lib.run_c(C_SOURCE,
                            [d, D, rng.randrange(1, 1 << 30), f"{budget:.2f}", best[0]],
                            timeout=budget + 15.0)
            n, e = lib.parse_graph_text(out)
            if n > 0:
                consider(n, e)
        except Exception:
            pass  # keep the valid fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
