import time

import lib


# ----------------------------------------------------------------------------
# C engine: general permutation lifts (no group structure).
#
# A-blocks A_i (i < K) and B-blocks B_j (j < K), each with G points, so N = 2KG.
# For each of DEG layers l there is a permutation P_l of the K block indices and,
# for each A-block i, a permutation PI_{l,i} of the G points. Layer l joins
# A_{i,g} to B_{P_l(i), PI_{l,i}(g)}. Every vertex then has exactly DEG neighbours,
# one per layer. A duplicate neighbour (two layers giving the same edge) is
# penalised, so a zero-cost state is simple, bipartite, degree-DEG and has
# diameter <= DIAM.
#
# Unlike the group lifts, there is no symmetry, so every vertex is a BFS source.
# Reachability is computed with bitsets (all N sources at once), which keeps one
# evaluation at roughly 0.1 ms for N near 700.
#
# Search: simulated annealing on the number of uncovered ordered pairs with
# swap moves on the PI permutations and on the P permutations. A success is
# grown by one point per block (new A and B points, randomised matching) and
# re-annealed. Growth continues until it fails, then a fresh random start is tried.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define DUP_PEN 20
#define ITERS 150000L
#define GROW_ITERS 40000L
#define TH 20.0
#define TL 0.3
#define TH_GROW 4.0

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t rnd64(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static int DEG, DIAM, K, G, N, W;
static int *P = NULL, *PI = NULL, *NB = NULL, *dcnt = NULL;
static uint64_t *RA = NULL, *RB = NULL;
static int bestK = 0, bestG = 0, best_n = 0, have_best = 0;
static int *bestP = NULL, *bestPI = NULL;

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void alloc_all(void) {
    W = (N + 63) / 64;
    P = realloc(P, sizeof(int) * (size_t)(DEG * K));
    PI = realloc(PI, sizeof(int) * (size_t)(DEG * K * G));
    NB = realloc(NB, sizeof(int) * (size_t)N * DEG);
    dcnt = realloc(dcnt, sizeof(int) * (size_t)N);
    RA = realloc(RA, sizeof(uint64_t) * (size_t)N * W);
    RB = realloc(RB, sizeof(uint64_t) * (size_t)N * W);
}

static void shuffle_int(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rnd_int(i + 1);
        int t = a[i]; a[i] = a[j]; a[j] = t;
    }
}

static void random_init(void) {
    for (int l = 0; l < DEG; l++) {
        int *p = P + l * K;
        for (int i = 0; i < K; i++) p[i] = i;
        shuffle_int(p, K);
    }
    for (int lk = 0; lk < DEG * K; lk++) {
        int *pi = PI + (size_t)lk * G;
        for (int g = 0; g < G; g++) pi[g] = g;
        shuffle_int(pi, G);
    }
}

static void build_adj(void) {
    int KG = K * G;
    memset(dcnt, 0, sizeof(int) * (size_t)N);
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < K; i++) {
            int j = P[l * K + i];
            const int *pi = PI + (size_t)(l * K + i) * G;
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = KG + j * G + pi[g];
                NB[(size_t)a * DEG + dcnt[a]++] = b;
                NB[(size_t)b * DEG + dcnt[b]++] = a;
            }
        }
}

static int count_dups(void) {
    int dup = 0;
    for (int v = 0; v < N; v++) {
        const int *nb = NB + (size_t)v * DEG;
        for (int a = 0; a < DEG; a++)
            for (int b = a + 1; b < DEG; b++)
                if (nb[a] == nb[b]) dup++;
    }
    return dup;
}

/* Cost = uncovered ordered pairs within DIAM + DUP_PEN per duplicate edge. */
static long long eval(void) {
    build_adj();
    int dup = count_dups();
    memset(RA, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) RA[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < N; v++) {
            uint64_t *out = RB + (size_t)v * W;
            const uint64_t *in = RA + (size_t)v * W;
            memcpy(out, in, sizeof(uint64_t) * (size_t)W);
            const int *nb = NB + (size_t)v * DEG;
            for (int l = 0; l < DEG; l++) {
                const uint64_t *src = RA + (size_t)nb[l] * W;
                for (int w = 0; w < W; w++) out[w] |= src[w];
            }
        }
        uint64_t *tmp = RA; RA = RB; RB = tmp;
    }
    long long unc = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *in = RA + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(in[w]);
        unc += N - c;
    }
    return unc + (long long)DUP_PEN * dup;
}

static void swp(int *a, int *b) { int t = *a; *a = *b; *b = t; }

/* Returns 1 if a zero-cost (valid) state was reached; the state is left in P/PI. */
static int anneal(long iters, double th, double tl) {
    long long cur = eval();
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 15) == 0 && elapsed() > DEADLINE) break;
        double T = th * pow(tl / th, (double)it / (double)iters);
        int l = rnd_int(DEG);
        if (K > 1 && rnd_unit() < 0.15) {
            int i1 = rnd_int(K), i2 = rnd_int(K);
            if (i1 == i2) continue;
            int *a = &P[l * K + i1], *b = &P[l * K + i2];
            swp(a, b);
            long long c2 = eval();
            if (c2 <= cur || rnd_unit() < exp(-(double)(c2 - cur) / T)) cur = c2;
            else swp(a, b);
        } else {
            int i = rnd_int(K);
            int g1 = rnd_int(G), g2 = rnd_int(G);
            if (g1 == g2) continue;
            int *pi = PI + (size_t)(l * K + i) * G;
            swp(&pi[g1], &pi[g2]);
            long long c2 = eval();
            if (c2 <= cur || rnd_unit() < exp(-(double)(c2 - cur) / T)) cur = c2;
            else swp(&pi[g1], &pi[g2]);
        }
    }
    return cur == 0;
}

static void record_best(void) {
    bestK = K; bestG = G; best_n = 2 * K * G; have_best = 1;
    bestP = realloc(bestP, sizeof(int) * (size_t)(DEG * K));
    memcpy(bestP, P, sizeof(int) * (size_t)(DEG * K));
    bestPI = realloc(bestPI, sizeof(int) * (size_t)(DEG * K * G));
    memcpy(bestPI, PI, sizeof(int) * (size_t)(DEG * K * G));
}

/* Add one point to every block. New point maps to itself, then is randomly swapped in. */
static void grow(void) {
    int oldG = G, newG = G + 1;
    int lk_count = DEG * K;
    int *nPI = malloc(sizeof(int) * (size_t)lk_count * newG);
    for (int lk = 0; lk < lk_count; lk++) {
        const int *src = PI + (size_t)lk * oldG;
        int *dst = nPI + (size_t)lk * newG;
        memcpy(dst, src, sizeof(int) * (size_t)oldG);
        dst[oldG] = oldG;
        int r = rnd_int(newG);
        int t = dst[oldG]; dst[oldG] = dst[r]; dst[r] = t;
    }
    free(PI);
    PI = nPI;
    G = newG;
    N = 2 * K * G;
    alloc_all();
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D seed time_limit start_n\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int start_n = atoi(argv[5]);
    uint64_t sm = sd * 2654435761ULL + 99991ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);
    best_n = start_n;
    if (DEG < 2 || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }

    static const int kc[4] = {1, 2, 2, 3};
    while (elapsed() < DEADLINE) {
        int k = kc[rnd_int(4)];
        int gmin = best_n / (2 * k) + 1;
        int g = gmin + rnd_int(3);
        K = k; G = g; N = 2 * K * G;
        alloc_all();
        random_init();
        if (anneal(ITERS, TH, TL)) {
            record_best();
            while (elapsed() < DEADLINE) {
                grow();
                random_init_block_dummy_guard:
                if (!anneal(GROW_ITERS, TH_GROW, TL)) break;
                record_best();
            }
        }
    }

    if (have_best) {
        K = bestK; G = bestG;
        int KG = K * G;
        printf("%d %d\n", 2 * KG, KG * DEG);
        for (int l = 0; l < DEG; l++)
            for (int i = 0; i < K; i++) {
                int j = bestP[l * K + i];
                for (int g = 0; g < G; g++) {
                    int a = i * G + g;
                    int b = KG + j * G + bestPI[(size_t)(l * K + i) * G + g];
                    printf("%d %d\n", a, b);
                }
            }
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Driver: baseline in Python, then the C permutation-lift search.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallbacks. For d = 2, the cycle C_{2D} has diameter D.
    # For d >= 3 and D = 2, K_{d,d} is optimal.
    if d == 2:
        best = lib.haar_graph(D, [0, 1])
    else:
        best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = pg

    if best[0] >= lib.moore_bound(d, D):
        return best

    # Spend most of the budget in C. The deadline is measured from C start,
    # so the reserve covers compilation, parsing and validation.
    remaining = 0.85 * time_limit - (time.monotonic() - start) - 2.0
    if D >= 3 and remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best[0]],
                            timeout=remaining + 10.0)
            n, e = lib.parse_graph_text(out)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
